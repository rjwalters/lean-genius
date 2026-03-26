#!/bin/bash
#
# pin-account.sh - Pin all agents to a specific OAuth account
#
# When pinned, all claude-wrapper.sh invocations use the pinned account
# instead of random load balancing. Useful when you want to burn through
# a specific account's quota or debug account-specific issues.
#
# Usage:
#   ./scripts/agents/pin-account.sh pin robb-integratedplasmonics
#   ./scripts/agents/pin-account.sh unpin
#   ./scripts/agents/pin-account.sh status
#   ./scripts/agents/pin-account.sh list
#
# The pin is stored in .loom/tokens/.pinned (contains token filename stem).
# New agents pick it up immediately; running agents pick it up on next cycle.
#

set -euo pipefail

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
TOKENS_DIR="$REPO_ROOT/.loom/tokens"
PIN_FILE="$TOKENS_DIR/.pinned"

usage() {
    cat <<'EOF'
Usage: pin-account.sh <command> [account-name]

Commands:
  pin <name>   Pin all agents to the named account
  unpin        Remove pin (resume load balancing)
  status       Show current pin status
  list         List available accounts

Account names are token file stems (without .token extension).
Partial matches are supported: "robb-int" matches "robb-integratedplasmonics".

Examples:
  pin-account.sh pin robb-integratedplasmonics
  pin-account.sh pin robb-int          # partial match
  pin-account.sh pin agent0            # partial match
  pin-account.sh unpin
EOF
}

list_accounts() {
    if [[ ! -d "$TOKENS_DIR" ]] || ! ls "$TOKENS_DIR"/*.token &>/dev/null; then
        echo "No token files found in $TOKENS_DIR" >&2
        return 1
    fi

    local pinned=""
    if [[ -f "$PIN_FILE" ]]; then
        pinned=$(cat "$PIN_FILE")
    fi

    echo "Available accounts:"
    for f in "$TOKENS_DIR"/*.token; do
        local name
        name=$(basename "$f" .token)
        if [[ "$name" == "$pinned" ]]; then
            echo "  * $name  (PINNED)"
        else
            echo "    $name"
        fi
    done
}

resolve_account() {
    local query="$1"
    local matches=()

    for f in "$TOKENS_DIR"/*.token; do
        local name
        name=$(basename "$f" .token)
        if [[ "$name" == "$query" ]]; then
            # Exact match
            echo "$name"
            return 0
        fi
        if [[ "$name" == *"$query"* ]]; then
            matches+=("$name")
        fi
    done

    if [[ ${#matches[@]} -eq 1 ]]; then
        echo "${matches[0]}"
        return 0
    elif [[ ${#matches[@]} -gt 1 ]]; then
        echo "Ambiguous match for '$query'. Matches:" >&2
        for m in "${matches[@]}"; do
            echo "  $m" >&2
        done
        return 1
    else
        echo "No account matching '$query'. Use 'list' to see available accounts." >&2
        return 1
    fi
}

cmd_pin() {
    if [[ $# -lt 1 ]]; then
        echo "Error: pin requires an account name" >&2
        usage >&2
        return 1
    fi

    local account
    account=$(resolve_account "$1") || return 1

    local token_file="$TOKENS_DIR/${account}.token"
    if [[ ! -f "$token_file" ]]; then
        echo "Error: token file not found: $token_file" >&2
        return 1
    fi

    echo "$account" > "$PIN_FILE"
    echo "Pinned all agents to: $account"
    echo "New agent invocations will use this account immediately."
    echo "Running agents will pick it up on their next cycle."
    echo ""
    echo "To unpin: $(basename "$0") unpin"
}

cmd_unpin() {
    if [[ -f "$PIN_FILE" ]]; then
        local was
        was=$(cat "$PIN_FILE")
        rm -f "$PIN_FILE"
        echo "Unpinned (was: $was). Agents will resume load balancing."
    else
        echo "No account is currently pinned."
    fi
}

cmd_status() {
    if [[ -f "$PIN_FILE" ]]; then
        local pinned
        pinned=$(cat "$PIN_FILE")
        echo "Pinned to: $pinned"
    else
        echo "No pin active — agents are load-balancing across all accounts."
    fi
    echo ""
    list_accounts
}

# Main
case "${1:-}" in
    pin)
        shift
        cmd_pin "$@"
        ;;
    unpin)
        cmd_unpin
        ;;
    status|"")
        cmd_status
        ;;
    list)
        list_accounts
        ;;
    -h|--help|help)
        usage
        ;;
    *)
        echo "Unknown command: $1" >&2
        usage >&2
        exit 1
        ;;
esac
