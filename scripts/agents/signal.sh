#!/bin/bash
# Agent signal management
# Usage: ./signal.sh [--dry-run] <command> [agent-id]
#
# Commands:
#   continue [agent]  - Signal agent(s) to continue work
#   pause [agent]     - Signal agent(s) to pause (wait for continue)
#   stop [agent]      - Signal agent(s) to stop gracefully
#   status            - Show current signals
#   clear             - Clear all signals

set -e

DRY_RUN=false
ARGS=()

for arg in "$@"; do
    case "$arg" in
        --dry-run|-n)
            DRY_RUN=true
            ;;
        --help|-h)
            ARGS+=("help")
            ;;
        *)
            ARGS+=("$arg")
            ;;
    esac
done

usage() {
    echo "Usage: $0 [--dry-run] <command> [agent-id]"
    echo ""
    echo "Options:"
    echo "  --dry-run, -n  Show signal changes without writing files"
    echo "  --help, -h     Show this help message"
    echo ""
    echo "Commands:"
    echo "  continue [agent]  - Signal agent(s) to continue work"
    echo "  pause [agent]     - Signal agent(s) to pause"
    echo "  stop [agent]      - Signal agent(s) to stop gracefully"
    echo "  status            - Show current signals"
    echo "  clear             - Clear all signals"
    echo ""
    echo "Examples:"
    echo "  $0 continue              # Continue all agents"
    echo "  $0 continue enhancer-1   # Continue specific agent"
    echo "  $0 --dry-run pause       # Preview pausing all agents"
    echo "  $0 pause                 # Pause all agents"
    echo "  $0 stop aristotle        # Stop Aristotle agent"
}

REPO_ROOT="${REPO_ROOT:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"

signal_path() {
    echo "$SIGNALS_DIR/$1"
}

dry_run_remove() {
    local file
    for file in "$@"; do
        echo "Would remove: $(signal_path "$file")"
    done
}

dry_run_touch() {
    local file
    for file in "$@"; do
        echo "Would create: $(signal_path "$file")"
    done
}

ensure_signals_dir() {
    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Signals directory: $SIGNALS_DIR"
    else
        mkdir -p "$SIGNALS_DIR"
    fi
}

cmd_continue() {
    local agent="$1"

    # Remove any pause/stop signals
    if [[ -z "$agent" ]]; then
        if [[ "$DRY_RUN" == "true" ]]; then
            dry_run_remove "pause-all" "stop-all"
            dry_run_touch "continue-all"
            return
        fi
        rm -f "$SIGNALS_DIR/pause-all" "$SIGNALS_DIR/stop-all"
        touch "$SIGNALS_DIR/continue-all"
        echo "✓ Sent continue signal to all agents"
    else
        if [[ "$DRY_RUN" == "true" ]]; then
            dry_run_remove "pause-$agent" "stop-$agent"
            dry_run_touch "continue-$agent"
            return
        fi
        rm -f "$SIGNALS_DIR/pause-$agent" "$SIGNALS_DIR/stop-$agent"
        touch "$SIGNALS_DIR/continue-$agent"
        echo "✓ Sent continue signal to $agent"
    fi
}

cmd_pause() {
    local agent="$1"

    # Remove continue signals, add pause
    if [[ -z "$agent" ]]; then
        if [[ "$DRY_RUN" == "true" ]]; then
            dry_run_remove "continue-all"
            dry_run_touch "pause-all"
            return
        fi
        rm -f "$SIGNALS_DIR/continue-all"
        touch "$SIGNALS_DIR/pause-all"
        echo "✓ Sent pause signal to all agents"
    else
        if [[ "$DRY_RUN" == "true" ]]; then
            dry_run_remove "continue-$agent"
            dry_run_touch "pause-$agent"
            return
        fi
        rm -f "$SIGNALS_DIR/continue-$agent"
        touch "$SIGNALS_DIR/pause-$agent"
        echo "✓ Sent pause signal to $agent"
    fi
}

cmd_stop() {
    local agent="$1"

    # Remove other signals, add stop
    if [[ -z "$agent" ]]; then
        if [[ "$DRY_RUN" == "true" ]]; then
            dry_run_remove "continue-all" "pause-all"
            dry_run_touch "stop-all"
            return
        fi
        rm -f "$SIGNALS_DIR/continue-all" "$SIGNALS_DIR/pause-all"
        touch "$SIGNALS_DIR/stop-all"
        echo "✓ Sent stop signal to all agents"
    else
        if [[ "$DRY_RUN" == "true" ]]; then
            dry_run_remove "continue-$agent" "pause-$agent"
            dry_run_touch "stop-$agent"
            return
        fi
        rm -f "$SIGNALS_DIR/continue-$agent" "$SIGNALS_DIR/pause-$agent"
        touch "$SIGNALS_DIR/stop-$agent"
        echo "✓ Sent stop signal to $agent"
    fi
}

cmd_status() {
    echo "=== Agent Signals ==="
    echo ""

    local has_signals=false

    for sig in "$SIGNALS_DIR"/*; do
        if [[ -f "$sig" ]]; then
            has_signals=true
            local name=$(basename "$sig")
            local age=$(( ($(date +%s) - $(stat -f %m "$sig" 2>/dev/null || stat -c %Y "$sig" 2>/dev/null)) / 60 ))
            echo "  $name (${age}m ago)"
        fi
    done

    if [[ "$has_signals" == "false" ]]; then
        echo "  (no active signals)"
    fi
}

cmd_clear() {
    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would remove all signals under: $SIGNALS_DIR"
        return
    fi
    rm -f "$SIGNALS_DIR"/*
    echo "✓ Cleared all signals"
}

# Main
case "${ARGS[0]:-}" in
    continue)
        ensure_signals_dir
        cmd_continue "${ARGS[1]:-}"
        ;;
    pause)
        ensure_signals_dir
        cmd_pause "${ARGS[1]:-}"
        ;;
    stop)
        ensure_signals_dir
        cmd_stop "${ARGS[1]:-}"
        ;;
    status)
        ensure_signals_dir
        cmd_status
        ;;
    clear)
        ensure_signals_dir
        cmd_clear
        ;;
    help)
        usage
        exit 0
        ;;
    *)
        usage
        exit 1
        ;;
esac
