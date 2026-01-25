#!/bin/bash
#
# claude-wrapper.sh - Resilient Claude CLI wrapper with retry logic
#
# Wraps the Claude CLI to handle API errors gracefully:
# - Pre-flight usage check before starting
# - Catches "No messages returned" and similar errors
# - Implements exponential backoff retry
# - Respects stop signals
#
# Usage:
#   ./claude-wrapper.sh --prompt "Your prompt" [--log logfile.log] [--max-retries N]
#
# Environment:
#   REPO_ROOT - Path to main repository (for signal files)
#   ENHANCER_ID - Agent identifier (for agent-specific signals)
#

set -uo pipefail

# Configuration
MAX_RETRIES="${MAX_RETRIES:-5}"
INITIAL_BACKOFF=60       # 1 minute
MAX_BACKOFF=1800         # 30 minutes
REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
LOG_FILE=""
PROMPT=""

# Colors
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() { echo -e "${BLUE}[wrapper]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[wrapper]${NC} $1"; }
log_error() { echo -e "${RED}[wrapper]${NC} $1" >&2; }
log_success() { echo -e "${GREEN}[wrapper]${NC} $1"; }

# Parse arguments
while [[ $# -gt 0 ]]; do
    case "$1" in
        --prompt)
            PROMPT="$2"
            shift 2
            ;;
        --log)
            LOG_FILE="$2"
            shift 2
            ;;
        --max-retries)
            MAX_RETRIES="$2"
            shift 2
            ;;
        *)
            log_error "Unknown argument: $1"
            exit 1
            ;;
    esac
done

if [[ -z "$PROMPT" ]]; then
    log_error "Usage: $0 --prompt 'Your prompt' [--log logfile.log]"
    exit 1
fi

# Check for stop signal
check_stop_signal() {
    if [[ -f "$SIGNALS_DIR/stop-all" ]]; then
        log_info "Stop-all signal detected"
        return 0
    fi
    if [[ -n "${ENHANCER_ID:-}" ]] && [[ -f "$SIGNALS_DIR/stop-$ENHANCER_ID" ]]; then
        log_info "Stop signal for $ENHANCER_ID detected"
        return 0
    fi
    return 1
}

# Pre-flight usage check
check_usage_limits() {
    if [[ -x "$REPO_ROOT/.loom/scripts/check-usage.sh" ]]; then
        local throttle
        throttle=$("$REPO_ROOT/.loom/scripts/check-usage.sh" --throttle 2>/dev/null || echo "0")

        if [[ "$throttle" -ge 3 ]]; then
            local usage_info
            usage_info=$("$REPO_ROOT/.loom/scripts/check-usage.sh" --human 2>/dev/null || echo "High usage")
            log_warn "Usage limit reached (throttle level $throttle): $usage_info"
            return 1
        fi
    fi
    return 0
}

# Check if error is recoverable
is_recoverable_error() {
    local output="$1"
    local exit_code="$2"

    # "No messages returned" - API error, likely rate limit or temporary issue
    if echo "$output" | grep -q "No messages returned"; then
        return 0
    fi

    # Rate limit errors
    if echo "$output" | grep -qi "rate.limit\|too.many.requests\|429"; then
        return 0
    fi

    # Server errors
    if echo "$output" | grep -qi "500\|502\|503\|504\|internal.server.error\|service.unavailable"; then
        return 0
    fi

    # Network errors
    if echo "$output" | grep -qi "ECONNREFUSED\|ETIMEDOUT\|network.error"; then
        return 0
    fi

    # Non-zero exit that might be transient
    if [[ "$exit_code" -ne 0 ]]; then
        return 0
    fi

    return 1
}

# Main retry loop
run_with_retry() {
    local attempt=1
    local backoff=$INITIAL_BACKOFF
    local last_output=""
    local exit_code=0

    while [[ $attempt -le $MAX_RETRIES ]]; do
        # Check for stop signal before each attempt
        if check_stop_signal; then
            log_info "Exiting due to stop signal"
            exit 0
        fi

        # Pre-flight usage check
        if ! check_usage_limits; then
            log_warn "Waiting for usage limits to reset (backoff: ${backoff}s)"
            sleep $backoff
            backoff=$((backoff * 2))
            [[ $backoff -gt $MAX_BACKOFF ]] && backoff=$MAX_BACKOFF
            continue
        fi

        log_info "Starting Claude (attempt $attempt/$MAX_RETRIES)"

        # Run Claude CLI
        if [[ -n "$LOG_FILE" ]]; then
            last_output=$(claude --dangerously-skip-permissions "$PROMPT" 2>&1 | tee "$LOG_FILE"; echo "EXIT_CODE:${PIPESTATUS[0]}")
        else
            last_output=$(claude --dangerously-skip-permissions "$PROMPT" 2>&1; echo "EXIT_CODE:$?")
        fi

        # Extract exit code from output
        exit_code=$(echo "$last_output" | grep -o 'EXIT_CODE:[0-9]*' | cut -d: -f2)
        exit_code="${exit_code:-1}"
        last_output=$(echo "$last_output" | sed '/EXIT_CODE:[0-9]*/d')

        # Success - Claude ran to completion
        if [[ "$exit_code" -eq 0 ]]; then
            log_success "Claude completed successfully"
            return 0
        fi

        # Check if this is a recoverable error
        if is_recoverable_error "$last_output" "$exit_code"; then
            log_warn "Recoverable error detected (exit code: $exit_code)"

            # Log the error
            if echo "$last_output" | grep -q "No messages returned"; then
                log_warn "Error: No messages returned from API"
            fi

            # Check stop signal again before waiting
            if check_stop_signal; then
                log_info "Exiting due to stop signal"
                exit 0
            fi

            log_info "Waiting ${backoff}s before retry..."
            sleep $backoff

            # Exponential backoff
            backoff=$((backoff * 2))
            [[ $backoff -gt $MAX_BACKOFF ]] && backoff=$MAX_BACKOFF

            attempt=$((attempt + 1))
        else
            # Non-recoverable error
            log_error "Non-recoverable error (exit code: $exit_code)"
            echo "$last_output" >&2
            return $exit_code
        fi
    done

    log_error "Max retries ($MAX_RETRIES) exceeded"
    echo "$last_output" >&2
    return 1
}

# Run the wrapper
run_with_retry
