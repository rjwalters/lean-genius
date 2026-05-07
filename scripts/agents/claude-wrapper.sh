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

# Allow spawning Claude from within a Claude Code session.
# The CLAUDECODE env var prevents nested sessions, but this wrapper
# intentionally launches independent agent processes.
unset CLAUDECODE 2>/dev/null || true

# Load long-lived OAuth token for autonomous agent sessions.
# Supports multiple accounts via .loom/tokens/*.token files.
# Falls back to CLAUDE_CODE_OAUTH_TOKEN in .env for single-account setups.
#
# Account selection strategy (in priority order):
#   1. If .loom/tokens/.ranking exists and is <10 min old, pick the first
#      account that has remaining weekly capacity (sorted by soonest reset).
#   2. If .loom/tokens/.allowlist exists, random among allowed accounts.
#   3. Otherwise, random among all .token files.
#
# The ranking file is written by: scripts/agents/check-accounts.sh --ranking
if [[ -z "${CLAUDE_CODE_OAUTH_TOKEN:-}" ]]; then
    _repo_root="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
    _tokens_dir="$_repo_root/.loom/tokens"

    # Bootstrap: if .loom/tokens is missing/empty/broken-symlink but .env
    # has ACCOUNT_KEY_N entries, materialize them into the tokens dir.
    if [[ ! -d "$_tokens_dir" ]] || ! ls "$_tokens_dir"/*.token &>/dev/null 2>&1; then
        _env_file="$_repo_root/.env"
        if [[ -f "$_env_file" ]] && grep -q '^ACCOUNT_KEY_[0-9]\+=' "$_env_file" 2>/dev/null; then
            # Replace whatever is at $_tokens_dir (broken symlink, etc) with a real dir.
            rm -f "$_tokens_dir" 2>/dev/null || true
            mkdir -p "$_tokens_dir" 2>/dev/null || true
            while IFS='=' read -r key val; do
                _n="${key#ACCOUNT_KEY_}"
                [[ "$_n" =~ ^[0-9]+$ ]] || continue
                printf '%s' "$val" | tr -d "'\"\n" > "$_tokens_dir/agent-$_n.token"
                chmod 600 "$_tokens_dir/agent-$_n.token" 2>/dev/null || true
            done < <(grep '^ACCOUNT_KEY_[0-9]\+=' "$_env_file")
            echo "[wrapper] Bootstrapped $(ls "$_tokens_dir"/*.token 2>/dev/null | wc -l | tr -d ' ') OAuth tokens from .env" >&2
        fi
    fi

    if [[ -d "$_tokens_dir" ]] && ls "$_tokens_dir"/*.token &>/dev/null; then
        _ranking_file="$_tokens_dir/.ranking"
        _allowlist_file="$_tokens_dir/.allowlist"
        _bad_tokens_file="$_tokens_dir/.bad_tokens"
        _selected=""
        _mode="random"

        # Strategy 1: Use cached ranking (soonest-reset-first, skip exhausted/blocked)
        if [[ -f "$_ranking_file" ]]; then
            _ranking_age=$(( $(date +%s) - $(stat -f %m "$_ranking_file" 2>/dev/null || stat -c %Y "$_ranking_file" 2>/dev/null || echo 0) ))
            if [[ $_ranking_age -lt 600 ]]; then  # <10 min old
                while IFS='|' read -r _rname _rstatus || [[ -n "$_rname" ]]; do
                    _rname=$(echo "$_rname" | tr -d '[:space:]')
                    _rstatus=$(echo "$_rstatus" | tr -d '[:space:]')
                    [[ -z "$_rname" || "$_rname" == \#* ]] && continue
                    [[ "$_rstatus" == "exhausted" || "$_rstatus" == "blocked" ]] && continue
                    if [[ -f "$_tokens_dir/${_rname}.token" ]]; then
                        # Skip bad tokens
                        if [[ -f "$_bad_tokens_file" ]] && grep -q " $_rname " "$_bad_tokens_file" 2>/dev/null; then
                            continue
                        fi
                        _selected="$_tokens_dir/${_rname}.token"
                        _mode="ranked"
                        break
                    fi
                done < "$_ranking_file"
            fi
        fi

        # Strategy 2: Allowlist random
        if [[ -z "$_selected" && -f "$_allowlist_file" ]]; then
            _eligible_tokens=()
            while IFS= read -r _name || [[ -n "$_name" ]]; do
                _name=$(echo "$_name" | tr -d '[:space:]')
                [[ -z "$_name" || "$_name" == \#* ]] && continue
                [[ -f "$_tokens_dir/${_name}.token" ]] && _eligible_tokens+=("$_tokens_dir/${_name}.token")
            done < "$_allowlist_file"
            if [[ ${#_eligible_tokens[@]} -gt 0 ]]; then
                _idx=$(( RANDOM % ${#_eligible_tokens[@]} ))
                _selected="${_eligible_tokens[$_idx]}"
                _mode="allowlist"
            fi
        fi

        # Strategy 3: Random from all
        if [[ -z "$_selected" ]]; then
            _all_tokens=("$_tokens_dir"/*.token)
            _idx=$(( RANDOM % ${#_all_tokens[@]} ))
            _selected="${_all_tokens[$_idx]}"
            _mode="random"
        fi

        _token=$(tr -d '[:space:]' < "$_selected")
        if [[ -n "$_token" ]]; then
            export CLAUDE_CODE_OAUTH_TOKEN="$_token"
            _acct=$(basename "$_selected" .token)
            echo "[wrapper] Using OAuth account: $_acct (mode: ${_mode})" >&2
        fi
    else
        # Fallback: single token from .env
        _env_file="$_repo_root/.env"
        if [[ -f "$_env_file" ]]; then
            _token=$(grep '^CLAUDE_CODE_OAUTH_TOKEN=' "$_env_file" 2>/dev/null | cut -d= -f2- | tr -d "'\"\n")
            if [[ -n "$_token" ]]; then
                export CLAUDE_CODE_OAUTH_TOKEN="$_token"
            fi
        fi
    fi
fi

# Configuration
MAX_RETRIES="${MAX_RETRIES:-5}"
INITIAL_BACKOFF=60       # 1 minute
MAX_BACKOFF=300          # 5 minutes
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

# Check for wake signal (early wakeup from backoff sleep)
check_wake_signal() {
    if [[ -f "$SIGNALS_DIR/wake-all" ]]; then
        rm -f "$SIGNALS_DIR/wake-all" 2>/dev/null || true
        log_info "Wake-all signal received. Resuming early."
        return 0
    fi
    if [[ -n "${ENHANCER_ID:-}" ]] && [[ -f "$SIGNALS_DIR/wake-$ENHANCER_ID" ]]; then
        rm -f "$SIGNALS_DIR/wake-$ENHANCER_ID" 2>/dev/null || true
        log_info "Wake signal for $ENHANCER_ID received. Resuming early."
        return 0
    fi
    return 1
}

# Pre-flight usage check
check_usage_limits() {
    if [[ -x "$REPO_ROOT/.loom/scripts/check-usage.sh" ]]; then
        local throttle
        throttle=$("$REPO_ROOT/.loom/scripts/check-usage.sh" --throttle 2>/dev/null || echo "0")

        # Ensure throttle is a valid integer (usage check may return JSON error)
        if ! [[ "$throttle" =~ ^[0-9]+$ ]]; then
            throttle=0
        fi

        if [[ "$throttle" -ge 3 ]]; then
            local usage_info
            usage_info=$("$REPO_ROOT/.loom/scripts/check-usage.sh" --status 2>/dev/null || echo "High usage")
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

# --- Error Classification ---
# Different errors need different responses. We classify into:
#   TOKEN_EXPIRED  - 401 auth error, token needs refresh (skip this token)
#   TOKEN_EXHAUSTED - "hit your limit", quota used up (rotate to next token)
#   CWD_DELETED    - working directory was removed (exit for respawn)
#   RECOVERABLE    - transient error (retry with backoff)
#   FATAL          - non-recoverable (exit)

classify_error() {
    local output="$1"
    local exit_code="$2"

    # Timeout from 'timeout' command — productive cycle, not an error
    if [[ "$exit_code" -eq 124 || "$exit_code" -eq 137 ]]; then
        echo "TIMEOUT"
        return
    fi

    # Working directory deleted (worktree cleaned up)
    if echo "$output" | grep -qi "current working directory was deleted"; then
        echo "CWD_DELETED"
        return
    fi

    # Token expired (401 auth error) — this specific token is bad
    if echo "$output" | grep -qi "401.*authentication_error\|OAuth token has expired\|token.*expired"; then
        echo "TOKEN_EXPIRED"
        return
    fi

    # Token exhausted (quota used up) — rotate to next
    if echo "$output" | grep -qi "hit your limit\|hit.your.limit"; then
        echo "TOKEN_EXHAUSTED"
        return
    fi

    # Rate limit (429) — transient, retry with backoff
    if echo "$output" | grep -qi "rate.limit\|too.many.requests\|429"; then
        echo "RECOVERABLE"
        return
    fi

    # Server errors — transient
    if echo "$output" | grep -qi "500\|502\|503\|504\|internal.server.error\|service.unavailable"; then
        echo "RECOVERABLE"
        return
    fi

    # Network errors — transient
    if echo "$output" | grep -qi "ECONNREFUSED\|ETIMEDOUT\|network.error"; then
        echo "RECOVERABLE"
        return
    fi

    # "No messages returned" — transient API issue
    if echo "$output" | grep -q "No messages returned"; then
        echo "RECOVERABLE"
        return
    fi

    # Non-zero exit — treat as recoverable in daemon mode
    if [[ "$exit_code" -ne 0 ]]; then
        echo "RECOVERABLE"
        return
    fi

    echo "SUCCESS"
}

# Legacy wrapper for existing callers
is_recoverable_error() {
    local classification
    classification=$(classify_error "$1" "$2")
    [[ "$classification" != "FATAL" && "$classification" != "SUCCESS" ]]
}

# --- Token Management ---
# Track bad tokens (expired/invalid) so we skip them on rotation.
# File-based so all agents can share the state.
_bad_tokens_file="${_tokens_dir:-.loom/tokens}/.bad_tokens"

# Mark a token as bad (expired/invalid)
mark_token_bad() {
    local token_name="$1"
    local reason="$2"
    local timestamp
    timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    echo "$timestamp $token_name $reason" >> "$_bad_tokens_file" 2>/dev/null
    log_warn "Marked token '$token_name' as bad: $reason"
}

# Check if a token is marked bad
is_token_bad() {
    local token_name="$1"
    [[ -f "$_bad_tokens_file" ]] && grep -q " $token_name " "$_bad_tokens_file" 2>/dev/null
}

# Build the list of eligible tokens (respecting allowlist)
_get_eligible_tokens() {
    local _repo_root="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
    local _tokens_dir="$_repo_root/.loom/tokens"
    local _allowlist_file="$_tokens_dir/.allowlist"

    _eligible_rotation_tokens=()
    if [[ -f "$_allowlist_file" ]]; then
        while IFS= read -r _name || [[ -n "$_name" ]]; do
            _name=$(echo "$_name" | tr -d '[:space:]')
            [[ -z "$_name" || "$_name" == \#* ]] && continue
            [[ -f "$_tokens_dir/${_name}.token" ]] && _eligible_rotation_tokens+=("$_tokens_dir/${_name}.token")
        done < "$_allowlist_file"
    fi
    # Fall back to all tokens if allowlist empty/missing
    if [[ ${#_eligible_rotation_tokens[@]} -eq 0 ]]; then
        _eligible_rotation_tokens=("$_tokens_dir"/*.token)
    fi
}

# Try rotating to a working token (skip bad ones, respect allowlist)
rotate_to_working_token() {
    local _repo_root="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
    local _tokens_dir="$_repo_root/.loom/tokens"

    if [[ ! -d "$_tokens_dir" ]] || ! ls "$_tokens_dir"/*.token &>/dev/null; then
        return 1
    fi

    _get_eligible_tokens
    local _count=${#_eligible_rotation_tokens[@]}
    local _tried=0

    while [[ $_tried -lt $_count ]]; do
        local _idx=$(( RANDOM % _count ))
        local _selected="${_eligible_rotation_tokens[$_idx]}"
        local _acct
        _acct=$(basename "$_selected" .token)

        if is_token_bad "$_acct"; then
            _tried=$((_tried + 1))
            continue
        fi

        local _token
        _token=$(tr -d '[:space:]' < "$_selected")
        if [[ -n "$_token" ]]; then
            export CLAUDE_CODE_OAUTH_TOKEN="$_token"
            log_info "Rotated to token: $_acct"
            return 0
        fi
        _tried=$((_tried + 1))
    done

    log_error "All $_count eligible tokens are marked bad or empty"
    return 1
}

# Clean up bad tokens file periodically (entries older than 6 hours)
cleanup_bad_tokens() {
    [[ -f "$_bad_tokens_file" ]] || return
    local cutoff
    cutoff=$(date -u -v-6H +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null || date -u -d '6 hours ago' +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null)
    if [[ -n "$cutoff" ]]; then
        local tmp
        tmp=$(mktemp)
        awk -v cutoff="$cutoff" '$1 >= cutoff' "$_bad_tokens_file" > "$tmp" 2>/dev/null
        mv "$tmp" "$_bad_tokens_file" 2>/dev/null
    fi
}

# --- Pre-flight Checks ---

# Verify the working directory still exists (worktree not deleted)
check_cwd_exists() {
    if [[ ! -d "$(pwd)" ]]; then
        log_error "Working directory no longer exists — worktree was likely deleted"
        log_error "Exiting so the daemon can respawn with a fresh worktree"
        return 1
    fi
    return 0
}

# Liveness check: verify claude establishes an API connection within this timeout.
# NOTE: claude -p buffers ALL stdout until the session completes — tool-heavy prompts
# produce 0 bytes of stdout for the entire run. We cannot use file size as a signal.
# Instead, check for ESTABLISHED TCP connections (sign of API communication).
LIVENESS_TIMEOUT="${LIVENESS_TIMEOUT:-120}"  # 2 minutes to establish API connection

# Run Claude once and return exit code
run_claude_once() {
    local last_output=""
    local exit_code=0

    log_info "Claude CLI timeout set to ${CLAUDE_TIMEOUT}s"

    # IMPORTANT: We write to a temp file and redirect stdin from /dev/null.
    # Claude CLI tries to set up terminal access during initialization.
    # When run inside $() command substitution or pipelines in tmux, this
    # causes SIGTTIN/SIGTTOU signals that suspend the process (state T).
    # Redirecting stdin from /dev/null and stdout to a file avoids all
    # TTY interaction issues.
    local tmpfile
    tmpfile=$(mktemp)

    # Run in background so we can monitor for startup hangs.
    # CLAUDE_MODEL env var pins a specific model (e.g. to avoid 1M-context auto-
    # selection on accounts that lack the entitlement). Empty/unset → CLI default.
    local model_arg=()
    if [[ -n "${CLAUDE_MODEL:-}" ]]; then
        model_arg=(--model "$CLAUDE_MODEL")
    fi
    timeout --kill-after=30 "$CLAUDE_TIMEOUT" claude -p --dangerously-skip-permissions "${model_arg[@]}" "$PROMPT" < /dev/null > "$tmpfile" 2>&1 &
    local timeout_pid=$!

    # Find the actual claude child process (timeout -> claude)
    sleep 2
    local claude_pid=""
    claude_pid=$(pgrep -P "$timeout_pid" 2>/dev/null | head -1)

    # Liveness monitor: wait for claude to establish an API connection.
    # A healthy claude connects within seconds. A hung one never connects.
    if [[ -n "$claude_pid" ]]; then
        local waited=0
        local connected=false
        while [[ $waited -lt $LIVENESS_TIMEOUT ]]; do
            if ! kill -0 "$timeout_pid" 2>/dev/null; then break; fi
            # Check for any ESTABLISHED TCP connection (API communication)
            if lsof -Pan -p "$claude_pid" -i 2>/dev/null | grep -q ESTABLISHED; then
                connected=true
                break
            fi
            sleep 5
            waited=$((waited + 5))
        done

        if [[ "$connected" == "false" ]] && kill -0 "$timeout_pid" 2>/dev/null; then
            log_warn "Liveness check failed: no API connection after ${LIVENESS_TIMEOUT}s — killing hung process (PID $claude_pid)"
            kill "$timeout_pid" 2>/dev/null; sleep 2; kill -9 "$timeout_pid" 2>/dev/null
            wait "$timeout_pid" 2>/dev/null
            rm -f "$tmpfile"
            LAST_OUTPUT="Liveness check failed: no API connection after ${LIVENESS_TIMEOUT}s"
            return 1
        fi

        if [[ "$connected" == "true" ]]; then
            log_info "Claude connected to API (${waited}s)"
        fi
    fi

    # Wait for claude to finish (either naturally or via timeout)
    wait "$timeout_pid" 2>/dev/null
    exit_code=$?

    if [[ -n "$LOG_FILE" ]]; then cat "$tmpfile" >> "$LOG_FILE"; fi
    last_output=$(cat "$tmpfile")
    rm -f "$tmpfile"

    if [[ "$exit_code" -eq 124 ]]; then
        log_warn "Claude CLI timed out after ${CLAUDE_TIMEOUT}s (SIGTERM)"
    elif [[ "$exit_code" -eq 137 ]]; then
        log_warn "Claude CLI timed out after ${CLAUDE_TIMEOUT}s (required SIGKILL)"
    fi

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

        # Check working directory still exists (worktree not deleted)
        if ! check_cwd_exists; then
            log_error "Daemon exiting: working directory deleted"
            exit 1
        fi

        # Periodically clean up stale bad-token entries
        cleanup_bad_tokens

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
        run_claude_once
        local exit_code=$?

        # Classify the error to determine response
        local error_class
        error_class=$(classify_error "$LAST_OUTPUT" "$exit_code")

        case "$error_class" in
            SUCCESS)
                log_success "Daemon cycle $cycle: Claude completed successfully"
                backoff=$INITIAL_BACKOFF
                consecutive_failures=0
                # Reset pin-exhaust counter on success
                rm -f "${REPO_ROOT:-.}/.loom/tokens/.pin-exhaust-count" 2>/dev/null
                cycle=$((cycle + 1))
                continue
                ;;
            TIMEOUT)
                log_info "Daemon cycle $cycle: completed (hit ${CLAUDE_TIMEOUT}s timeout)"
                backoff=$INITIAL_BACKOFF
                consecutive_failures=0
                cycle=$((cycle + 1))
                continue
                ;;
            CWD_DELETED)
                log_error "Daemon cycle $cycle: working directory was deleted"
                log_error "Exiting so the daemon can respawn with a fresh worktree"
                exit 1
                ;;
            TOKEN_EXPIRED)
                consecutive_failures=$((consecutive_failures + 1))
                local _current_acct
                _current_acct=$(basename "$(ls -t "${_tokens_dir:-/dev/null}"/*.token 2>/dev/null | head -1)" .token 2>/dev/null || echo "unknown")
                log_warn "Daemon cycle $cycle: token expired (401) — marking bad and rotating"
                mark_token_bad "$_current_acct" "expired"
                if rotate_to_working_token; then
                    log_info "Retrying immediately with new token"
                    cycle=$((cycle + 1))
                    continue
                else
                    log_error "All tokens expired — waiting ${MAX_BACKOFF}s before retry"
                    sleep $MAX_BACKOFF
                    # Clean bad tokens to retry them after cooldown
                    rm -f "$_bad_tokens_file" 2>/dev/null
                    cycle=$((cycle + 1))
                    continue
                fi
                ;;
            TOKEN_EXHAUSTED)
                consecutive_failures=$((consecutive_failures + 1))
                log_warn "Daemon cycle $cycle: token quota exhausted — rotating"
                if rotate_to_working_token; then
                    log_info "Retrying immediately with new token"
                    cycle=$((cycle + 1))
                    continue
                else
                    log_warn "All tokens exhausted — entering long backoff (${MAX_BACKOFF}s)"
                    backoff=$MAX_BACKOFF
                fi
                ;;
            RECOVERABLE)
                consecutive_failures=$((consecutive_failures + 1))
                log_warn "Daemon cycle $cycle: recoverable error (exit code: $exit_code, consecutive failures: $consecutive_failures)"
                ;;
            *)
                consecutive_failures=$((consecutive_failures + 1))
                log_warn "Daemon cycle $cycle: unclassified error (exit code: $exit_code, consecutive failures: $consecutive_failures)"
                ;;
        esac

        # Common backoff logic for recoverable/unclassified errors
        if check_stop_signal; then
            log_info "Daemon exiting due to stop signal"
            exit 0
        fi

        log_info "Daemon: waiting ${backoff}s before retry..."
        sleep $backoff
        backoff=$((backoff * 2))
        [[ $backoff -gt $MAX_BACKOFF ]] && backoff=$MAX_BACKOFF
        cycle=$((cycle + 1))
    done
}

# Run the wrapper
if [[ "$DAEMON_MODE" == "true" ]]; then
    run_daemon
else
    run_with_retry
fi
