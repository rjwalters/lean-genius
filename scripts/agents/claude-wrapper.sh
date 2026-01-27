#!/bin/bash
#
# claude-wrapper.sh - Resilient Claude CLI wrapper with retry logic
#
# Wraps the Claude CLI to handle API errors gracefully:
# - Pre-flight usage check before starting
# - Catches "No messages returned" and similar errors
# - Implements exponential backoff retry
# - Respects stop signals
# - Daemon mode for long-running agents (infinite retry)
# - Appends to log files with timestamped cycle separators
# - Automatic log rotation when files exceed size limit
#
# Usage:
#   ./claude-wrapper.sh --prompt "Your prompt" [--log logfile.log] [--max-retries N]
#   ./claude-wrapper.sh --daemon --prompt "Your prompt" [--log logfile.log]
#
# Environment:
#   REPO_ROOT      - Path to main repository (for signal files)
#   ENHANCER_ID    - Agent identifier (for agent-specific signals)
#   CLAUDE_TIMEOUT - Max seconds for a single Claude CLI invocation (default: 3600)
#                    Set to 0 to disable timeout. Agents that run longer tasks
#                    (e.g., researchers) may need higher values.
#   LOG_MAX_SIZE   - Max log file size in bytes before rotation (default: 52428800 = 50MB)
#   LOG_KEEP_COUNT - Number of rotated log files to keep (default: 3)
#

set -uo pipefail

# Configuration
MAX_RETRIES="${MAX_RETRIES:-5}"
INITIAL_BACKOFF=60       # 1 minute
MAX_BACKOFF=1800         # 30 minutes
CLAUDE_TIMEOUT="${CLAUDE_TIMEOUT:-3600}"  # 1 hour default; configurable per agent
REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"
LOG_FILE=""
PROMPT=""
DAEMON_MODE=false

# Log rotation configuration
LOG_MAX_SIZE="${LOG_MAX_SIZE:-52428800}"  # 50MB default (in bytes)
LOG_KEEP_COUNT="${LOG_KEEP_COUNT:-3}"     # Number of rotated logs to keep

# Colors
RED='\033[0;31m'
YELLOW='\033[1;33m'
GREEN='\033[0;32m'
BLUE='\033[0;34m'
NC='\033[0m'

log_to_file() {
    if [[ -n "$LOG_FILE" ]]; then
        local timestamp
        timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
        echo "[$timestamp] [wrapper] $1" >> "$LOG_FILE"
    fi
}

log_info() { echo -e "${BLUE}[wrapper]${NC} $1"; log_to_file "$1"; }
log_warn() { echo -e "${YELLOW}[wrapper]${NC} $1"; log_to_file "WARN: $1"; }
log_error() { echo -e "${RED}[wrapper]${NC} $1" >&2; log_to_file "ERROR: $1"; }
log_success() { echo -e "${GREEN}[wrapper]${NC} $1"; log_to_file "$1"; }

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
        --daemon)
            DAEMON_MODE=true
            shift
            ;;
        *)
            log_error "Unknown argument: $1"
            exit 1
            ;;
    esac
done

if [[ -z "$PROMPT" ]]; then
    log_error "Usage: $0 --prompt 'Your prompt' [--log logfile.log] [--daemon]"
    exit 1
fi

if [[ "$DAEMON_MODE" == "true" ]]; then
    log_info "Running in DAEMON mode (infinite retry enabled)"
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

# Rotate log file if it exceeds LOG_MAX_SIZE
rotate_log() {
    if [[ -z "$LOG_FILE" ]]; then
        return
    fi
    if [[ ! -f "$LOG_FILE" ]]; then
        return
    fi

    local file_size
    file_size=$(stat -f%z "$LOG_FILE" 2>/dev/null || stat -c%s "$LOG_FILE" 2>/dev/null || echo "0")

    if [[ "$file_size" -ge "$LOG_MAX_SIZE" ]]; then
        log_info "Log file $(basename "$LOG_FILE") exceeds $(( LOG_MAX_SIZE / 1048576 ))MB, rotating"

        # Shift existing rotated logs (e.g., .3 -> deleted, .2 -> .3, .1 -> .2)
        local i=$LOG_KEEP_COUNT
        while [[ $i -gt 1 ]]; do
            local prev=$((i - 1))
            if [[ -f "${LOG_FILE}.${prev}" ]]; then
                mv "${LOG_FILE}.${prev}" "${LOG_FILE}.${i}"
            fi
            i=$((i - 1))
        done

        # Rotate current log to .1
        mv "$LOG_FILE" "${LOG_FILE}.1"
        log_info "Rotated log to $(basename "${LOG_FILE}.1")"
    fi
}

# Write a cycle separator to the log file
write_cycle_separator() {
    local cycle_num="${1:-}"
    if [[ -n "$LOG_FILE" ]]; then
        local timestamp
        timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
        {
            echo ""
            echo "--- [$timestamp] Cycle ${cycle_num} start ---"
            echo ""
        } >> "$LOG_FILE"
    fi
}

# Check if error is recoverable
is_recoverable_error() {
    local output="$1"
    local exit_code="$2"

    # Timeout from 'timeout' command (SIGTERM)
    if [[ "$exit_code" -eq 124 ]]; then
        return 0
    fi

    # Timeout with SIGKILL (process didn't respond to SIGTERM)
    if [[ "$exit_code" -eq 137 ]]; then
        return 0
    fi

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

# Run Claude once and return exit code
run_claude_once() {
    local last_output=""
    local exit_code=0

    log_info "Claude CLI timeout set to ${CLAUDE_TIMEOUT}s"

    # Run Claude CLI with timeout to prevent indefinite hangs.
    # The 'timeout' command sends SIGTERM after CLAUDE_TIMEOUT seconds,
    # and SIGKILL 30s later if the process hasn't exited.
    if [[ -n "$LOG_FILE" ]]; then
        last_output=$(timeout --kill-after=30 "$CLAUDE_TIMEOUT" claude --dangerously-skip-permissions "$PROMPT" 2>&1 | tee -a "$LOG_FILE"; echo "EXIT_CODE:${PIPESTATUS[0]}")
    else
        last_output=$(timeout --kill-after=30 "$CLAUDE_TIMEOUT" claude --dangerously-skip-permissions "$PROMPT" 2>&1; echo "EXIT_CODE:$?")
    fi

    # Extract exit code from output
    exit_code=$(echo "$last_output" | grep -o 'EXIT_CODE:[0-9]*' | cut -d: -f2)
    exit_code="${exit_code:-1}"
    last_output=$(echo "$last_output" | sed '/EXIT_CODE:[0-9]*/d')

    # Check for timeout (exit code 124 = SIGTERM, 137 = SIGKILL)
    if [[ "$exit_code" -eq 124 ]]; then
        log_warn "Claude CLI timed out after ${CLAUDE_TIMEOUT}s (SIGTERM)"
    elif [[ "$exit_code" -eq 137 ]]; then
        log_warn "Claude CLI timed out after ${CLAUDE_TIMEOUT}s (required SIGKILL)"
    fi

    # Store output for caller
    LAST_OUTPUT="$last_output"
    return $exit_code
}

# Main retry loop (finite retries)
run_with_retry() {
    local attempt=1
    local backoff=$INITIAL_BACKOFF
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

        # Rotate log if needed, then write cycle separator
        rotate_log
        write_cycle_separator "$attempt"

        # Run Claude
        if run_claude_once; then
            log_success "Claude completed successfully"
            return 0
        fi
        exit_code=$?

        # Check if this is a recoverable error
        if is_recoverable_error "$LAST_OUTPUT" "$exit_code"; then
            log_warn "Recoverable error detected (exit code: $exit_code)"

            # Log the error
            if echo "$LAST_OUTPUT" | grep -q "No messages returned"; then
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
            echo "$LAST_OUTPUT" >&2
            return $exit_code
        fi
    done

    log_error "Max retries ($MAX_RETRIES) exceeded"
    echo "$LAST_OUTPUT" >&2
    return 1
}

# Daemon mode: infinite retry loop
run_daemon() {
    local cycle=1
    local backoff=$INITIAL_BACKOFF
    local consecutive_failures=0

    log_info "Daemon mode: will retry indefinitely until stop signal"

    while true; do
        # Check for stop signal before each cycle
        if check_stop_signal; then
            log_info "Daemon exiting due to stop signal"
            exit 0
        fi

        # Pre-flight usage check
        if ! check_usage_limits; then
            log_warn "Daemon: waiting for usage limits (backoff: ${backoff}s)"
            sleep $backoff
            backoff=$((backoff * 2))
            [[ $backoff -gt $MAX_BACKOFF ]] && backoff=$MAX_BACKOFF
            continue
        fi

        log_info "Daemon cycle $cycle: starting Claude"

        # Rotate log if needed, then write cycle separator
        rotate_log
        write_cycle_separator "$cycle"

        # Run Claude
        if run_claude_once; then
            log_success "Daemon cycle $cycle: Claude completed successfully"
            # Reset backoff on success
            backoff=$INITIAL_BACKOFF
            consecutive_failures=0
            cycle=$((cycle + 1))
            # In daemon mode, we restart after successful completion
            # This handles agents that are meant to run periodically
            continue
        fi

        local exit_code=$?
        consecutive_failures=$((consecutive_failures + 1))

        # Check if this is a recoverable error (in daemon mode, most errors are recoverable)
        if is_recoverable_error "$LAST_OUTPUT" "$exit_code"; then
            log_warn "Daemon cycle $cycle: recoverable error (exit code: $exit_code, consecutive failures: $consecutive_failures)"

            if echo "$LAST_OUTPUT" | grep -q "No messages returned"; then
                log_warn "Error: No messages returned from API"
            fi

            # Check stop signal before waiting
            if check_stop_signal; then
                log_info "Daemon exiting due to stop signal"
                exit 0
            fi

            log_info "Daemon: waiting ${backoff}s before retry..."
            sleep $backoff

            # Exponential backoff (capped at MAX_BACKOFF)
            backoff=$((backoff * 2))
            [[ $backoff -gt $MAX_BACKOFF ]] && backoff=$MAX_BACKOFF

            cycle=$((cycle + 1))
        else
            # Even "non-recoverable" errors get retried in daemon mode
            log_warn "Daemon cycle $cycle: error that would be fatal in normal mode (exit code: $exit_code)"
            log_warn "Daemon mode: retrying anyway after ${MAX_BACKOFF}s"

            # Check stop signal before waiting
            if check_stop_signal; then
                log_info "Daemon exiting due to stop signal"
                exit 0
            fi

            sleep $MAX_BACKOFF
            cycle=$((cycle + 1))
        fi
    done
}

# Run the wrapper
if [[ "$DAEMON_MODE" == "true" ]]; then
    run_daemon
else
    run_with_retry
fi
