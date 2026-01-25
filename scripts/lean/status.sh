#!/usr/bin/env bash
#
# Lean Genius Status - Display mathematical orchestration status
#
# Usage:
#   ./scripts/lean/status.sh          # Display formatted status
#   ./scripts/lean/status.sh --json   # Output as JSON
#

set -euo pipefail

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m' # No Color

# Config
STATE_FILE="research/lean-daemon-state.json"
ARISTOTLE_JOBS="research/aristotle-jobs.json"
CANDIDATE_POOL="research/candidate-pool.json"

# Parse arguments
JSON_OUTPUT=false
if [[ "${1:-}" == "--json" ]]; then
    JSON_OUTPUT=true
fi

# Helper: Check if tmux session exists
session_exists() {
    tmux has-session -t "$1" 2>/dev/null
}

# Helper: Get session uptime
get_session_uptime() {
    local session="$1"
    if session_exists "$session"; then
        local created
        created=$(tmux display-message -t "$session" -p '#{session_created}' 2>/dev/null || echo "0")
        if [[ "$created" != "0" && -n "$created" ]]; then
            local now
            now=$(date +%s)
            local diff=$((now - created))
            local hours=$((diff / 3600))
            local mins=$(((diff % 3600) / 60))
            if [[ $hours -gt 0 ]]; then
                echo "${hours}h ${mins}m"
            else
                echo "${mins}m"
            fi
        else
            echo "unknown"
        fi
    else
        echo "stopped"
    fi
}

# Helper: Count stubs needing enhancement
count_stubs() {
    if command -v npx &>/dev/null && [[ -f "scripts/erdos/find-stubs.ts" ]]; then
        npx tsx scripts/erdos/find-stubs.ts --stats 2>/dev/null | grep -oE "with sources: [0-9]+" | grep -oE "[0-9]+" || echo "?"
    else
        echo "?"
    fi
}

# Helper: Count Aristotle pending jobs
count_aristotle_jobs() {
    if [[ -f "$ARISTOTLE_JOBS" ]]; then
        jq '[.jobs[] | select(.status == "submitted")] | length' "$ARISTOTLE_JOBS" 2>/dev/null || echo "0"
    else
        echo "0"
    fi
}

# Helper: Count available research problems
count_research_problems() {
    if [[ -f "$CANDIDATE_POOL" ]]; then
        jq '[.candidates[] | select(.status == "available")] | length' "$CANDIDATE_POOL" 2>/dev/null || echo "0"
    else
        echo "0"
    fi
}

# Helper: Count PRs ready to merge
count_ready_prs() {
    gh pr list --label "loom:pr" --json number 2>/dev/null | jq 'length' || echo "0"
}

# Gather data
gather_status() {
    local daemon_running=false
    local daemon_uptime="N/A"
    local started_at=""

    # Check daemon state file
    if [[ -f "$STATE_FILE" ]]; then
        daemon_running=$(jq -r '.running // false' "$STATE_FILE")
        started_at=$(jq -r '.started_at // ""' "$STATE_FILE")
        if [[ -n "$started_at" && "$daemon_running" == "true" ]]; then
            local start_epoch
            start_epoch=$(date -j -f "%Y-%m-%dT%H:%M:%SZ" "$started_at" +%s 2>/dev/null || date -d "$started_at" +%s 2>/dev/null || echo "0")
            if [[ "$start_epoch" != "0" ]]; then
                local now
                now=$(date +%s)
                local diff=$((now - start_epoch))
                local hours=$((diff / 3600))
                local mins=$(((diff % 3600) / 60))
                daemon_uptime="${hours}h ${mins}m"
            fi
        fi
    fi

    # Check tmux sessions
    local erdos_sessions=()
    local aristotle_status="stopped"
    local researcher_sessions=()
    local deployer_status="stopped"

    # Erdős enhancers
    for i in 1 2 3 4 5; do
        if session_exists "erdos-enhancer-$i"; then
            erdos_sessions+=("erdos-enhancer-$i:$(get_session_uptime "erdos-enhancer-$i")")
        fi
    done

    # Aristotle
    if session_exists "aristotle-agent"; then
        aristotle_status="running:$(get_session_uptime "aristotle-agent")"
    fi

    # Researchers
    for i in 1 2 3; do
        if session_exists "researcher-$i"; then
            researcher_sessions+=("researcher-$i:$(get_session_uptime "researcher-$i")")
        fi
    done

    # Deployer
    if session_exists "deployer"; then
        deployer_status="running:$(get_session_uptime "deployer")"
    fi

    # Work queue counts
    local stubs_count
    local aristotle_jobs
    local research_problems
    local ready_prs

    stubs_count=$(count_stubs)
    aristotle_jobs=$(count_aristotle_jobs)
    research_problems=$(count_research_problems)
    ready_prs=$(count_ready_prs)

    # Session stats from state file
    local stubs_enhanced=0
    local proofs_submitted=0
    local deployments=0

    if [[ -f "$STATE_FILE" ]]; then
        stubs_enhanced=$(jq -r '.session_stats.stubs_enhanced // 0' "$STATE_FILE")
        proofs_submitted=$(jq -r '.session_stats.proofs_submitted // 0' "$STATE_FILE")
        deployments=$(jq -r '.session_stats.deployments // 0' "$STATE_FILE")
    fi

    if $JSON_OUTPUT; then
        # Output as JSON
        cat <<EOF
{
  "daemon": {
    "running": $daemon_running,
    "uptime": "$daemon_uptime",
    "started_at": "$started_at"
  },
  "work_queue": {
    "stubs_with_sources": "$stubs_count",
    "aristotle_pending": $aristotle_jobs,
    "research_available": $research_problems,
    "prs_ready": $ready_prs
  },
  "agents": {
    "erdos": {
      "count": ${#erdos_sessions[@]},
      "sessions": $(printf '%s\n' "${erdos_sessions[@]:-}" | jq -R -s -c 'split("\n") | map(select(length > 0))')
    },
    "aristotle": {
      "status": "${aristotle_status%%:*}",
      "uptime": "${aristotle_status#*:}"
    },
    "researcher": {
      "count": ${#researcher_sessions[@]},
      "sessions": $(printf '%s\n' "${researcher_sessions[@]:-}" | jq -R -s -c 'split("\n") | map(select(length > 0))')
    },
    "deployer": {
      "status": "${deployer_status%%:*}",
      "uptime": "${deployer_status#*:}"
    }
  },
  "session_stats": {
    "stubs_enhanced": $stubs_enhanced,
    "proofs_submitted": $proofs_submitted,
    "deployments": $deployments
  }
}
EOF
    else
        # Formatted output
        echo ""
        echo -e "${BOLD}═══════════════════════════════════════════════════${NC}"
        echo -e "${BOLD}  LEAN GENIUS STATUS${NC}"
        echo -e "${BOLD}═══════════════════════════════════════════════════${NC}"

        # Daemon status
        if [[ "$daemon_running" == "true" ]]; then
            echo -e "  Daemon: ${GREEN}Running${NC} (uptime: $daemon_uptime)"
        else
            echo -e "  Daemon: ${YELLOW}Not running${NC} (agents may still be active)"
        fi
        echo ""

        # Work Queue
        echo -e "  ${CYAN}Work Queue:${NC}"
        echo "    Stubs needing enhancement: $stubs_count (with sources)"
        echo "    Aristotle jobs pending: $aristotle_jobs"
        echo "    Research problems available: $research_problems"
        echo "    PRs ready to merge: $ready_prs"
        echo ""

        # Agent Pool
        echo -e "  ${CYAN}Agent Pool:${NC}"

        # Erdős
        local erdos_count=${#erdos_sessions[@]}
        if [[ $erdos_count -gt 0 ]]; then
            echo -e "    ${BOLD}Erdős Enhancers:${NC} ${GREEN}$erdos_count active${NC}"
            for session in "${erdos_sessions[@]}"; do
                local name="${session%%:*}"
                local uptime="${session#*:}"
                echo "      $name: Running ($uptime)"
            done
        else
            echo -e "    ${BOLD}Erdős Enhancers:${NC} ${YELLOW}0 active${NC}"
        fi

        # Aristotle
        if [[ "${aristotle_status%%:*}" == "running" ]]; then
            echo -e "    ${BOLD}Aristotle:${NC} ${GREEN}1/1 active${NC}"
            echo "      aristotle-agent: Running (${aristotle_status#*:})"
        else
            echo -e "    ${BOLD}Aristotle:${NC} ${YELLOW}0/1 active${NC}"
        fi

        # Researcher
        local researcher_count=${#researcher_sessions[@]}
        if [[ $researcher_count -gt 0 ]]; then
            echo -e "    ${BOLD}Researcher:${NC} ${GREEN}$researcher_count active${NC}"
            for session in "${researcher_sessions[@]}"; do
                local name="${session%%:*}"
                local uptime="${session#*:}"
                echo "      $name: Running ($uptime)"
            done
        else
            echo -e "    ${BOLD}Researcher:${NC} ${YELLOW}0 active${NC}"
        fi

        # Deployer
        if [[ "${deployer_status%%:*}" == "running" ]]; then
            echo -e "    ${BOLD}Deployer:${NC} ${GREEN}1/1 active${NC}"
            echo "      deployer: Running (${deployer_status#*:})"
        else
            echo -e "    ${BOLD}Deployer:${NC} ${YELLOW}0/1 active${NC}"
        fi
        echo ""

        # Session Stats
        echo -e "  ${CYAN}Session Stats:${NC}"
        echo "    Stubs enhanced: $stubs_enhanced"
        echo "    Proofs submitted: $proofs_submitted"
        echo "    Deployments: $deployments"

        echo -e "${BOLD}═══════════════════════════════════════════════════${NC}"
        echo ""

        # Commands hint
        echo -e "  ${BLUE}Commands:${NC}"
        echo "    /lean start --erdos 2 --researcher 1    Start agents"
        echo "    /lean spawn erdos                       Add one Erdős enhancer"
        echo "    /lean scale erdos 3                     Scale to 3 enhancers"
        echo "    /lean stop                              Stop all agents"
        echo ""
    fi
}

# Run
gather_status
