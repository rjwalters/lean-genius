#!/bin/bash
# Agent signal management
# Usage: ./signal.sh <command> [agent-id]
#
# Commands:
#   continue [agent]  - Signal agent(s) to continue work
#   pause [agent]     - Signal agent(s) to pause (wait for continue)
#   stop [agent]      - Signal agent(s) to stop gracefully
#   status            - Show current signals
#   clear             - Clear all signals

set -e

REPO_ROOT="${REPO_ROOT:-$(git rev-parse --show-toplevel 2>/dev/null || pwd)}"
SIGNALS_DIR="$REPO_ROOT/.loom/signals"

mkdir -p "$SIGNALS_DIR"

usage() {
    echo "Usage: $0 <command> [agent-id]"
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
    echo "  $0 pause                 # Pause all agents"
    echo "  $0 stop aristotle        # Stop Aristotle agent"
    exit 1
}

cmd_continue() {
    local agent="$1"

    # Remove any pause/stop signals
    if [[ -z "$agent" ]]; then
        rm -f "$SIGNALS_DIR/pause-all" "$SIGNALS_DIR/stop-all"
        touch "$SIGNALS_DIR/continue-all"
        echo "✓ Sent continue signal to all agents"
    else
        rm -f "$SIGNALS_DIR/pause-$agent" "$SIGNALS_DIR/stop-$agent"
        touch "$SIGNALS_DIR/continue-$agent"
        echo "✓ Sent continue signal to $agent"
    fi
}

cmd_pause() {
    local agent="$1"

    # Remove continue signals, add pause
    if [[ -z "$agent" ]]; then
        rm -f "$SIGNALS_DIR/continue-all"
        touch "$SIGNALS_DIR/pause-all"
        echo "✓ Sent pause signal to all agents"
    else
        rm -f "$SIGNALS_DIR/continue-$agent"
        touch "$SIGNALS_DIR/pause-$agent"
        echo "✓ Sent pause signal to $agent"
    fi
}

cmd_stop() {
    local agent="$1"

    # Remove other signals, add stop
    if [[ -z "$agent" ]]; then
        rm -f "$SIGNALS_DIR/continue-all" "$SIGNALS_DIR/pause-all"
        touch "$SIGNALS_DIR/stop-all"
        echo "✓ Sent stop signal to all agents"
    else
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
    rm -f "$SIGNALS_DIR"/*
    echo "✓ Cleared all signals"
}

# Main
case "${1:-}" in
    continue)
        cmd_continue "$2"
        ;;
    pause)
        cmd_pause "$2"
        ;;
    stop)
        cmd_stop "$2"
        ;;
    status)
        cmd_status
        ;;
    clear)
        cmd_clear
        ;;
    *)
        usage
        ;;
esac
