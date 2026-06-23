#!/bin/bash
#
# check-accounts.sh - Show usage status for all agent OAuth accounts
#
# Probes each .token file via a minimal Messages API call and reads
# the rate-limit response headers to get session (5h) and weekly (7d)
# utilization, remaining capacity, and time until weekly reset.
#
# Usage:
#   ./scripts/agents/check-accounts.sh           # Show all accounts
#   ./scripts/agents/check-accounts.sh --json     # JSON output
#   ./scripts/agents/check-accounts.sh --quick     # Skip probe, just list
#   ./scripts/agents/check-accounts.sh --ranking   # Write .ranking file for wrapper
#   ./scripts/agents/check-accounts.sh --dry-run --ranking  # Preview .ranking
#

set -euo pipefail

REPO_ROOT="${REPO_ROOT:-$(cd "$(dirname "$0")/../.." && pwd)}"
TOKENS_DIR="$REPO_ROOT/.loom/tokens"
JSON_MODE=false
QUICK_MODE=false
RANKING_MODE=false
DRY_RUN=false

usage() {
    cat <<EOF
Usage: check-accounts.sh [options]

Show usage status for agent OAuth accounts.

Options:
  --json      Output account status as JSON
  --quick     Skip API probes and only list configured token files
  --ranking   Write .loom/tokens/.ranking for smart account selection
  --dry-run   Preview --ranking output without writing .ranking
  --help, -h  Show this help message
EOF
}

for arg in "$@"; do
    case "$arg" in
        --json) JSON_MODE=true ;;
        --quick) QUICK_MODE=true ;;
        --ranking) RANKING_MODE=true ;;
        --dry-run|-n) DRY_RUN=true ;;
        --help|-h)
            usage
            exit 0
            ;;
        *)
            echo "Unknown option: $arg" >&2
            usage >&2
            exit 1
            ;;
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
        echo "-"
        return
    fi
    for a in "${allowlisted[@]}"; do
        [[ "$a" == "$name" ]] && echo "yes" && return
    done
    echo "no"
}

# Probe a token via Messages API for rate-limit headers.
# Retries once with random backoff on failure. On persistent 401,
# falls back to CLI probe to confirm the token is alive.
probe_token() {
    local token="$1"
    local attempt headers

    for attempt in 1 2; do
        headers=$(curl -s -D - -o /dev/null --max-time 15 \
            -H "x-api-key: $token" \
            -H "content-type: application/json" \
            -H "anthropic-version: 2023-06-01" \
            -d '{"model":"claude-haiku-4-5-20251001","max_tokens":1,"messages":[{"role":"user","content":"hi"}]}' \
            "https://api.anthropic.com/v1/messages" 2>/dev/null)

        if echo "$headers" | grep -q "5h-utilization"; then
            echo "$headers"
            return
        fi
        [[ $attempt -lt 2 ]] && sleep $(( (RANDOM % 3) + 1 ))
    done

    # API auth failed — try CLI probe to check if token works at all
    if echo "$headers" | head -1 | grep -q "401"; then
        local cli_out
        cli_out=$(CLAUDE_CODE_OAUTH_TOKEN="$token" timeout 20 \
            claude -p "say ok" --model claude-haiku-4-5-20251001 --max-turns 1 \
            < /dev/null 2>&1) || true
        if [[ -n "$cli_out" ]] && ! echo "$cli_out" | grep -qi "error\|expired\|unauthorized"; then
            echo "CLI_OK"
            return
        fi
    fi

    echo "$headers"
}

# Color helpers
RED='\033[0;31m'
YELLOW='\033[0;33m'
GREEN='\033[0;32m'
CYAN='\033[0;36m'
DIM='\033[0;90m'
BOLD='\033[1m'
NC='\033[0m'

pct_color() {
    local pct="$1"
    if (( $(echo "$pct <= 20" | bc -l 2>/dev/null || echo 0) )); then
        echo "${RED}"
    elif (( $(echo "$pct <= 50" | bc -l 2>/dev/null || echo 0) )); then
        echo "${YELLOW}"
    else
        echo "${GREEN}"
    fi
}

# Collect results
token_files=("$TOKENS_DIR"/*.token)
total=${#token_files[@]}

if ! $JSON_MODE && ! $QUICK_MODE && ! $RANKING_MODE; then
    echo ""
    echo -e "${BOLD}Agent Account Status${NC}  ($total accounts)"
    echo ""
fi

declare -a results=()
probe_count=0

for token_file in "${token_files[@]}"; do
    name=$(basename "$token_file" .token)
    token=$(tr -d '[:space:]' < "$token_file")
    [[ -z "$token" ]] && continue

    eligible=$(is_allowlisted "$name")

    if $QUICK_MODE; then
        results+=("$name|-|-|-|-|-|$eligible")
        continue
    fi

    probe_count=$((probe_count + 1))
    if ! $JSON_MODE && ! $RANKING_MODE; then
        printf "\r  Probing %d/%d: %-28s" "$probe_count" "$total" "$name" >&2
    fi

    # Stagger probes (0.5-1.5s between accounts)
    if [[ $probe_count -gt 1 ]]; then
        sleep "0.$(( (RANDOM % 10) + 5 ))"
    fi

    headers=$(probe_token "$token")

    # CLI-only token: alive but no usage data available
    if [[ "$headers" == "CLI_OK" ]]; then
        results+=("$name|?|?|-||0|$eligible")
        continue
    fi

    # Extract utilization (0.0-1.0 scale) and reset timestamps
    s5h_util=$(echo "$headers" | grep "5h-utilization" | head -1 | cut -d: -f2 | tr -d ' \r' || true)
    s7d_util=$(echo "$headers" | grep "7d-utilization" | head -1 | cut -d: -f2 | tr -d ' \r' || true)
    s7d_reset=$(echo "$headers" | grep "7d-reset" | head -1 | cut -d: -f2 | tr -d ' \r' || true)
    s5h_status=$(echo "$headers" | grep "5h-status" | head -1 | cut -d: -f2 | tr -d ' \r' || true)

    if [[ -z "$s5h_util" ]]; then
        results+=("$name|err|err|-|-|-|$eligible")
        continue
    fi

    # Convert utilization to remaining % (integer)
    s5h_remain=$(python3 -c "print(max(0, round((1.0 - $s5h_util) * 100)))" 2>/dev/null || echo "?")
    s7d_remain=$(python3 -c "print(max(0, round((1.0 - $s7d_util) * 100)))" 2>/dev/null || echo "?")

    # Hours until weekly reset
    if [[ -n "$s7d_reset" && "$s7d_reset" != "0" ]]; then
        hrs_to_reset=$(python3 -c "
import time
reset = int($s7d_reset)
now = time.time()
hrs = max(0, (reset - now) / 3600)
print(f'{hrs:.1f}')
" 2>/dev/null || echo "?")
    else
        hrs_to_reset="?"
    fi

    # Session status flag
    session_flag=""
    if [[ "$s5h_status" == *"blocked"* || "$s5h_status" == *"exceeded"* ]]; then
        session_flag="BLOCKED"
    fi

    results+=("$name|$s5h_remain|$s7d_remain|$hrs_to_reset|$session_flag|$s7d_reset|$eligible")
done

if ! $JSON_MODE && ! $QUICK_MODE && ! $RANKING_MODE; then
    printf "\r%-40s\r" "" >&2
fi

# Sort by weekly reset timestamp (soonest first)
IFS=$'\n' sorted=($(for r in "${results[@]}"; do
    IFS='|' read -r name s5h s7d hrs flag reset eligible <<< "$r"
    printf "%s|%s\n" "${reset:-9999999999}" "$r"
done | sort -t'|' -k1 -n | cut -d'|' -f2-))
unset IFS

# Ranking output: write .ranking file for wrapper's smart account selection
if $RANKING_MODE; then
    _ranking_file="$TOKENS_DIR/.ranking"
    _ranking_lines=()
    for r in "${sorted[@]}"; do
        IFS='|' read -r name s5h s7d hrs flag reset eligible <<< "$r"
        [[ "$s5h" == "-" || "$s5h" == "err" ]] && continue
        if [[ "$s5h" == "?" ]]; then
            _ranking_lines+=("$name|available")
            continue
        fi
        if [[ "$flag" == "BLOCKED" ]]; then
            _ranking_lines+=("$name|blocked")
        elif [[ "$s7d" == "0" ]]; then
            _ranking_lines+=("$name|exhausted")
        else
            _ranking_lines+=("$name|available")
        fi
    done

    if $DRY_RUN; then
        echo "Would write ranking to $_ranking_file (${#_ranking_lines[@]} accounts)" >&2
        printf '%s\n' "${_ranking_lines[@]}"
    else
        : > "$_ranking_file"
        if [[ ${#_ranking_lines[@]} -gt 0 ]]; then
            printf '%s\n' "${_ranking_lines[@]}" > "$_ranking_file"
        fi
        echo "Wrote ranking to $_ranking_file (${#_ranking_lines[@]} accounts)" >&2
    fi
    exit 0
fi

# JSON output
if $JSON_MODE; then
    echo "["
    first=true
    for r in "${sorted[@]}"; do
        IFS='|' read -r name s5h s7d hrs flag reset eligible <<< "$r"
        $first || echo ","
        first=false
        printf '  {"account": "%s", "session_remaining_pct": "%s", "weekly_remaining_pct": "%s", "hrs_to_weekly_reset": "%s", "session_blocked": %s, "eligible": "%s"}' \
            "$name" "$s5h" "$s7d" "$hrs" "$([ "$flag" = "BLOCKED" ] && echo true || echo false)" "$eligible"
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

printf "  ${BOLD}%-28s  %10s  %10s  %10s  %s${NC}\n" "Account" "Session" "Weekly" "Resets in" "Status"
printf "  %-28s  %10s  %10s  %10s  %s\n" "----------------------------" "----------" "----------" "----------" "----------"

for r in "${sorted[@]}"; do
    IFS='|' read -r name s5h s7d hrs flag reset eligible <<< "$r"

    if [[ "$s5h" == "err" ]]; then
        printf "  %-28s  ${RED}%10s${NC}  ${RED}%10s${NC}  %10s  %b\n" "$name" "ERROR" "ERROR" "-" "${RED}error${NC}"
        continue
    fi

    if [[ "$s5h" == "-" ]]; then
        printf "  %-28s  %10s  %10s  %10s  %s\n" "$name" "-" "-" "-" "skipped"
        continue
    fi

    if [[ "$s5h" == "?" ]]; then
        printf "  %-28s  ${DIM}%10s${NC}  ${DIM}%10s${NC}  %10s  %b\n" "$name" "n/a" "n/a" "-" "${GREEN}available (oauth)${NC}"
        continue
    fi

    s5h_color=$(pct_color "$s5h")
    s7d_color=$(pct_color "$s7d")

    status_str=""
    if [[ "$flag" == "BLOCKED" ]]; then
        status_str="${RED}session-blocked${NC}"
    elif [[ "$eligible" == "no" ]]; then
        status_str="${DIM}not in allowlist${NC}"
    elif [[ "$s7d" == "0" ]]; then
        status_str="${RED}weekly exhausted${NC}"
    else
        status_str="${GREEN}available${NC}"
    fi

    printf "  %-28s  ${s5h_color}%9s%%${NC}  ${s7d_color}%9s%%${NC}  %8sh  %b\n" \
        "$name" "$s5h" "$s7d" "$hrs" "$status_str"
done

echo ""

# Summary
avail=0
blocked=0
exhausted=0
for r in "${results[@]}"; do
    IFS='|' read -r name s5h s7d hrs flag reset eligible <<< "$r"
    [[ "$s5h" == "-" || "$s5h" == "err" ]] && continue
    [[ "$s5h" == "?" ]] && { avail=$((avail + 1)); continue; }
    if [[ "$flag" == "BLOCKED" ]]; then
        blocked=$((blocked + 1))
    elif [[ "$s7d" == "0" ]]; then
        exhausted=$((exhausted + 1))
    else
        avail=$((avail + 1))
    fi
done
echo -e "  ${GREEN}${avail} available${NC}, ${RED}${blocked} session-blocked${NC}, ${RED}${exhausted} weekly-exhausted${NC} / ${BOLD}${total} total${NC}"
echo -e "  ${DIM}Sorted by weekly reset (soonest first — use these to avoid waste)${NC}"
echo ""
