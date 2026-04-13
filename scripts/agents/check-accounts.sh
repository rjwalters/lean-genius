#!/bin/bash
#
# check-accounts.sh - Show status for all agent OAuth accounts
#
# Probes each .token file in .loom/tokens/ by sending a minimal haiku
# request through the Claude CLI. Reports whether each account is
# available or rate-limited.
#
# Usage:
#   ./scripts/agents/check-accounts.sh           # Show all accounts
#   ./scripts/agents/check-accounts.sh --json     # JSON output
#   ./scripts/agents/check-accounts.sh --quick     # Skip probe, just list
#

set -euo pipefail

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
TOKENS_DIR="$REPO_ROOT/.loom/tokens"
JSON_MODE=false
QUICK_MODE=false
PROBE_TIMEOUT=30

for arg in "$@"; do
    case "$arg" in
        --json) JSON_MODE=true ;;
        --quick) QUICK_MODE=true ;;
    esac
done

if [[ ! -d "$TOKENS_DIR" ]] || ! ls "$TOKENS_DIR"/*.token &>/dev/null; then
    echo "No token files found in $TOKENS_DIR" >&2
    exit 1
fi

# Check allowlist
ALLOWLIST_FILE="$TOKENS_DIR/.allowlist"
allowlisted=()
if [[ -f "$ALLOWLIST_FILE" ]]; then
    while IFS= read -r name || [[ -n "$name" ]]; do
        name=$(echo "$name" | tr -d '[:space:]')
        [[ -z "$name" || "$name" == \#* ]] && continue
        allowlisted+=("$name")
    done < "$ALLOWLIST_FILE"
fi

is_allowlisted() {
    local name="$1"
    if [[ ${#allowlisted[@]} -eq 0 ]]; then
        echo "-"  # no allowlist = all accounts eligible
        return
    fi
    for a in "${allowlisted[@]}"; do
        [[ "$a" == "$name" ]] && echo "yes" && return
    done
    echo "no"
}

# Check bad tokens
BAD_TOKENS_FILE="$TOKENS_DIR/.bad_tokens"
is_bad() {
    local name="$1"
    [[ -f "$BAD_TOKENS_FILE" ]] && grep -q " $name " "$BAD_TOKENS_FILE" 2>/dev/null && echo "yes" || echo "no"
}

# Probe a token by sending a minimal haiku request via claude CLI
# Returns: ok, rate-limited, expired, error
probe_token() {
    local token="$1"
    local output
    output=$(CLAUDE_CODE_OAUTH_TOKEN="$token" timeout "$PROBE_TIMEOUT" \
        claude -p "say ok" --model claude-haiku-4-5-20251001 --max-turns 1 \
        < /dev/null 2>&1) || true

    if echo "$output" | grep -qi "rate.limit\|too many\|429\|throttl"; then
        echo "rate-limited"
    elif echo "$output" | grep -qi "expired\|invalid.*token\|unauthorized\|401\|authentication"; then
        echo "expired"
    elif echo "$output" | grep -qi "error\|fail\|refused"; then
        echo "error"
    elif [[ -n "$output" ]]; then
        echo "ok"
    else
        echo "no-response"
    fi
}

# Color helpers
RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
DIM='\033[0;90m'
BOLD='\033[1m'
NC='\033[0m'

status_color() {
    case "$1" in
        ok)           echo "${GREEN}" ;;
        rate-limited) echo "${RED}" ;;
        expired)      echo "${RED}" ;;
        skipped)      echo "${DIM}" ;;
        *)            echo "${YELLOW}" ;;
    esac
}

# Collect results
token_files=("$TOKENS_DIR"/*.token)
total=${#token_files[@]}

if ! $JSON_MODE && ! $QUICK_MODE; then
    echo ""
    echo -e "${BOLD}Agent Account Status${NC}  ($total accounts)"
    echo -e "${DIM}  Probing each token with a minimal haiku request...${NC}"
    echo ""
fi

declare -a results=()
probe_count=0

for token_file in "${token_files[@]}"; do
    name=$(basename "$token_file" .token)
    token=$(tr -d '[:space:]' < "$token_file")
    [[ -z "$token" ]] && continue

    eligible=$(is_allowlisted "$name")
    bad=$(is_bad "$name")

    if $QUICK_MODE; then
        status="skipped"
    else
        probe_count=$((probe_count + 1))
        if ! $JSON_MODE; then
            printf "\r  Probing %d/%d: %-12s" "$probe_count" "$total" "$name" >&2
        fi
        status=$(probe_token "$token")
    fi

    # Token preview (last 8 chars)
    token_tail="...${token: -8}"

    results+=("$name|$status|$eligible|$bad|$token_tail")
done

if ! $JSON_MODE && ! $QUICK_MODE; then
    printf "\r%-40s\r" "" >&2  # clear progress line
fi

# JSON output
if $JSON_MODE; then
    echo "["
    first=true
    for r in "${results[@]}"; do
        IFS='|' read -r name status eligible bad token_tail <<< "$r"
        $first || echo ","
        first=false
        printf '  {"account": "%s", "status": "%s", "eligible": "%s", "bad": "%s"}' \
            "$name" "$status" "$eligible" "$bad"
    done
    echo ""
    echo "]"
    exit 0
fi

# Table output
if [[ ${#allowlisted[@]} -gt 0 ]]; then
    echo -e "  Allowlist: ${CYAN}${allowlisted[*]}${NC}"
else
    echo -e "  Allowlist: ${DIM}none (all accounts eligible)${NC}"
fi
echo ""

printf "  ${BOLD}%-12s  %-14s  %-8s  %-6s  %s${NC}\n" "Account" "Status" "Eligible" "Bad" "Token"
printf "  %-12s  %-14s  %-8s  %-6s  %s\n" "------------" "--------------" "--------" "------" "------------"

ok_count=0
limited_count=0
error_count=0

for r in "${results[@]}"; do
    IFS='|' read -r name status eligible bad token_tail <<< "$r"

    s_color=$(status_color "$status")
    status_display=$(printf "%-14s" "$status")

    e_display="$eligible"
    if [[ "$eligible" == "no" ]]; then
        e_display="${DIM}no${NC}"
    elif [[ "$eligible" == "yes" ]]; then
        e_display="${GREEN}yes${NC}"
    fi

    b_display="$bad"
    if [[ "$bad" == "yes" ]]; then
        b_display="${RED}yes${NC}"
    else
        b_display="${DIM}no${NC}"
    fi

    printf "  %-12s  ${s_color}%s${NC}  %-8b  %-6b  ${DIM}%s${NC}\n" \
        "$name" "$status_display" "$e_display" "$b_display" "$token_tail"

    case "$status" in
        ok) ok_count=$((ok_count + 1)) ;;
        rate-limited) limited_count=$((limited_count + 1)) ;;
        expired|error|no-response) error_count=$((error_count + 1)) ;;
    esac
done

echo ""
if ! $QUICK_MODE; then
    echo -e "  ${GREEN}${ok_count} ok${NC}, ${RED}${limited_count} rate-limited${NC}, ${YELLOW}${error_count} error${NC} / ${BOLD}${total} total${NC}"
fi
echo ""
