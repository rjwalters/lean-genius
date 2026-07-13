#!/bin/bash
#
# pin-account.sh - Manage the account allowlist for agent token selection
#
# When an allowlist is active, agents load-balance only across listed accounts.
# When no allowlist exists, all .token files are eligible (default).
#
# Usage:
#   ./scripts/agents/pin-account.sh --dry-run allow agent-6 agent-7
#   ./scripts/agents/pin-account.sh allow agent-6 agent-7   # Set allowlist
#   ./scripts/agents/pin-account.sh add agent-8              # Add to allowlist
#   ./scripts/agents/pin-account.sh remove agent-8           # Remove from allowlist
#   ./scripts/agents/pin-account.sh reset                    # Remove allowlist (use all)
#   ./scripts/agents/pin-account.sh status                   # Show current state
#   ./scripts/agents/pin-account.sh list                     # List all accounts
#
# Legacy compatibility:
#   ./scripts/agents/pin-account.sh pin <name>   # Same as: allow <name>
#   ./scripts/agents/pin-account.sh unpin        # Same as: reset
#
# The allowlist is stored in .loom/tokens/.allowlist (one account per line).
# New agents pick it up immediately; running agents pick it up on next cycle.
#

set -euo pipefail

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

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
TOKENS_DIR="$REPO_ROOT/.loom/tokens"
ALLOWLIST_FILE="$TOKENS_DIR/.allowlist"
# Legacy pin file — removed on any allowlist operation
LEGACY_PIN_FILE="$TOKENS_DIR/.pinned"

usage() {
    cat <<'EOF'
Usage: pin-account.sh [--dry-run] <command> [accounts...]

Options:
  --dry-run, -n  Preview allowlist changes without writing files
  --help, -h     Show this help message

Commands:
  allow <name...>   Set allowlist to exactly these accounts
  add <name...>     Add account(s) to existing allowlist
  remove <name...>  Remove account(s) from allowlist
  reset             Remove allowlist (all accounts eligible)
  status            Show current allowlist and account state
  list              List all available accounts

  pin <name>        Legacy: same as "allow <name>"
  unpin             Legacy: same as "reset"

Account names are token file stems (without .token extension).
Partial matches are supported: "agent-6" matches "agent-6-rwalters".

Examples:
  pin-account.sh allow agent-6 agent-7     # Only use these two
  pin-account.sh --dry-run add agent-8     # Preview adding a third
  pin-account.sh add agent-8               # Add a third
  pin-account.sh remove agent-6            # Drop one
  pin-account.sh reset                     # Back to all accounts
EOF
}

cleanup_legacy() {
    if [[ -f "$LEGACY_PIN_FILE" ]]; then
        if [[ "$DRY_RUN" == "true" ]]; then
            echo "  (would remove legacy .pinned file)"
            return
        fi
        rm -f "$LEGACY_PIN_FILE" "$TOKENS_DIR/.pin-exhaust-count"
        echo "  (removed legacy .pinned file)"
    fi
}

write_allowlist() {
    local -n accounts_ref=$1

    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would write allowlist to $ALLOWLIST_FILE:"
        for acct in "${accounts_ref[@]}"; do
            echo "  $acct"
        done
        cleanup_legacy
        return
    fi

    mkdir -p "$TOKENS_DIR"
    printf '%s\n' "${accounts_ref[@]}" > "$ALLOWLIST_FILE"
    cleanup_legacy
}

list_accounts() {
    if [[ ! -d "$TOKENS_DIR" ]] || ! ls "$TOKENS_DIR"/*.token &>/dev/null; then
        echo "No token files found in $TOKENS_DIR" >&2
        return 1
    fi

    local allowlisted=()
    if [[ -f "$ALLOWLIST_FILE" ]]; then
        while IFS= read -r name || [[ -n "$name" ]]; do
            name=$(echo "$name" | tr -d '[:space:]')
            [[ -z "$name" || "$name" == \#* ]] && continue
            allowlisted+=("$name")
        done < "$ALLOWLIST_FILE"
    fi

    echo "Available accounts:"
    for f in "$TOKENS_DIR"/*.token; do
        local name
        name=$(basename "$f" .token)
        local marker="  "
        for a in "${allowlisted[@]+"${allowlisted[@]}"}"; do
            if [[ "$a" == "$name" ]]; then
                marker="* "
                break
            fi
        done
        echo "  ${marker}${name}"
    done

    if [[ ${#allowlisted[@]} -gt 0 ]]; then
        echo ""
        echo "  * = in allowlist"
    fi
}

resolve_account() {
    local query="$1"
    local matches=()

    for f in "$TOKENS_DIR"/*.token; do
        local name
        name=$(basename "$f" .token)
        if [[ "$name" == "$query" ]]; then
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

cmd_allow() {
    if [[ $# -lt 1 ]]; then
        echo "Error: allow requires at least one account name" >&2
        usage >&2
        return 1
    fi

    local resolved=()
    for name in "$@"; do
        local acct
        acct=$(resolve_account "$name") || return 1
        resolved+=("$acct")
    done

    write_allowlist resolved

    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would set allowlist to ${#resolved[@]} account(s):"
    else
        echo "Allowlist set to ${#resolved[@]} account(s):"
    fi
    for acct in "${resolved[@]}"; do
        echo "  $acct"
    done
    if [[ "$DRY_RUN" == "true" ]]; then
        echo "No files written."
    else
        echo ""
        echo "New agents will use only these accounts."
        echo "Running agents pick this up on next cycle."
        echo "To reset: $(basename "$0") reset"
    fi
}

cmd_add() {
    if [[ $# -lt 1 ]]; then
        echo "Error: add requires at least one account name" >&2
        return 1
    fi

    # Load existing
    local existing=()
    if [[ -f "$ALLOWLIST_FILE" ]]; then
        while IFS= read -r name || [[ -n "$name" ]]; do
            name=$(echo "$name" | tr -d '[:space:]')
            [[ -z "$name" || "$name" == \#* ]] && continue
            existing+=("$name")
        done < "$ALLOWLIST_FILE"
    fi

    local added=()
    for name in "$@"; do
        local acct
        acct=$(resolve_account "$name") || return 1
        # Check for duplicates
        local dup=false
        for e in "${existing[@]+"${existing[@]}"}"; do
            [[ "$e" == "$acct" ]] && dup=true && break
        done
        if $dup; then
            echo "  $acct already in allowlist, skipping"
        else
            existing+=("$acct")
            added+=("$acct")
        fi
    done

    if [[ ${#added[@]} -eq 0 ]]; then
        echo "No new accounts added."
        return 0
    fi

    write_allowlist existing

    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Would add ${#added[@]} account(s) to allowlist:"
    else
        echo "Added ${#added[@]} account(s) to allowlist:"
    fi
    for acct in "${added[@]}"; do
        echo "  + $acct"
    done
    if [[ "$DRY_RUN" == "true" ]]; then
        echo "Allowlist would have ${#existing[@]} account(s)."
        echo "No files written."
    else
        echo "Allowlist now has ${#existing[@]} account(s)."
    fi
}

cmd_remove() {
    if [[ $# -lt 1 ]]; then
        echo "Error: remove requires at least one account name" >&2
        return 1
    fi

    if [[ ! -f "$ALLOWLIST_FILE" ]]; then
        echo "No allowlist active — nothing to remove from." >&2
        return 1
    fi

    local to_remove=()
    for name in "$@"; do
        local acct
        acct=$(resolve_account "$name") || return 1
        to_remove+=("$acct")
    done

    local remaining=()
    while IFS= read -r name || [[ -n "$name" ]]; do
        name=$(echo "$name" | tr -d '[:space:]')
        [[ -z "$name" || "$name" == \#* ]] && continue
        local keep=true
        for r in "${to_remove[@]}"; do
            [[ "$r" == "$name" ]] && keep=false && break
        done
        $keep && remaining+=("$name")
    done < "$ALLOWLIST_FILE"

    if [[ ${#remaining[@]} -eq 0 ]]; then
        if [[ "$DRY_RUN" == "true" ]]; then
            echo "Would remove allowlist because it would be empty."
            cleanup_legacy
        else
            rm -f "$ALLOWLIST_FILE"
            echo "Allowlist is now empty — removed it. All accounts are eligible."
        fi
    else
        write_allowlist remaining
        if [[ "$DRY_RUN" == "true" ]]; then
            echo "Would remove ${#to_remove[@]} account(s). Allowlist would have ${#remaining[@]}:"
        else
            echo "Removed ${#to_remove[@]} account(s). Allowlist now has ${#remaining[@]}:"
        fi
        for acct in "${remaining[@]}"; do
            echo "  $acct"
        done
    fi
}

cmd_reset() {
    if [[ -f "$ALLOWLIST_FILE" ]]; then
        if [[ "$DRY_RUN" == "true" ]]; then
            echo "Would remove allowlist: $ALLOWLIST_FILE"
        else
            rm -f "$ALLOWLIST_FILE"
            echo "Allowlist removed. All accounts are now eligible."
        fi
    else
        if [[ "$DRY_RUN" == "true" ]]; then
            echo "No allowlist is active; reset would not remove anything."
        else
            echo "No allowlist was active."
        fi
    fi
    cleanup_legacy
}

cmd_status() {
    if [[ -f "$ALLOWLIST_FILE" ]]; then
        local count=0
        echo "Allowlist active:"
        while IFS= read -r name || [[ -n "$name" ]]; do
            name=$(echo "$name" | tr -d '[:space:]')
            [[ -z "$name" || "$name" == \#* ]] && continue
            echo "  * $name"
            count=$((count + 1))
        done < "$ALLOWLIST_FILE"
        echo ""
        echo "$count account(s) in allowlist."
    else
        echo "No allowlist active — agents load-balance across all accounts."
    fi
    echo ""
    list_accounts
}

# Main
case "${ARGS[0]:-}" in
    allow)
        cmd_allow "${ARGS[@]:1}"
        ;;
    add)
        cmd_add "${ARGS[@]:1}"
        ;;
    remove)
        cmd_remove "${ARGS[@]:1}"
        ;;
    reset)
        cmd_reset
        ;;
    pin)
        # Legacy: pin = allow single account
        cmd_allow "${ARGS[@]:1}"
        ;;
    unpin)
        # Legacy: unpin = reset
        cmd_reset
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
        echo "Unknown command: ${ARGS[0]}" >&2
        usage >&2
        exit 1
        ;;
esac
