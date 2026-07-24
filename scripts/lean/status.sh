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
STATE_FILE=".loom/lean-daemon-state.json"
OLD_STATE_FILE="research/lean-daemon-state.json"
DAEMON_PID_FILE="research/lean-daemon.pid"
DAEMON_TMUX_SESSION="lean-daemon"
ARISTOTLE_JOBS="research/aristotle-jobs.json"
CANDIDATE_POOL=".lean/state/candidate-pool.json"
# Aristotle scale-to-zero marker (issue #22471). When this file exists and no
# aristotle-agent tmux session is running, status reports SCALED_TO_ZERO
# instead of the generic "0/1 active" line.
ARISTOTLE_SCALED_MARKER=".loom/state/aristotle-scaled-to-zero"

# Fall back to old location if new state file doesn't exist
if [[ ! -f "$STATE_FILE" && -f "$OLD_STATE_FILE" ]]; then
    STATE_FILE="$OLD_STATE_FILE"
fi

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

# Helper: Count proofs needing enrichment
count_enrichment_targets() {
    if command -v npx &>/dev/null && [[ -f "scripts/enricher/find-targets.ts" ]]; then
        npx tsx scripts/enricher/find-targets.ts --stats 2>/dev/null | grep -oE "Entries needing enrichment: +[0-9]+" | grep -oE "[0-9]+" || echo "?"
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

# Helper: Count Aristotle candidates (files eligible for submission)
count_aristotle_candidates() {
    if [[ -x "scripts/aristotle/find-candidates.sh" ]]; then
        timeout 10 ./scripts/aristotle/find-candidates.sh --count 2>/dev/null || echo "0"
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

    # Cross-check liveness from real signals — the state-file `.running`
    # has been observed stuck at the value from the last `launch.sh stop`
    # for months, so trusting it alone produces both false negatives
    # (daemon up, status says down) and false positives.
    local tmux_alive=false
    local pid_alive=false
    if tmux has-session -t "$DAEMON_TMUX_SESSION" 2>/dev/null; then
        tmux_alive=true
    fi
    if [[ -f "$DAEMON_PID_FILE" ]]; then
        local _pid
        _pid=$(cat "$DAEMON_PID_FILE" 2>/dev/null || echo "")
        if [[ -n "$_pid" ]] && kill -0 "$_pid" 2>/dev/null; then
            pid_alive=true
        fi
    fi
    if $tmux_alive || $pid_alive; then
        daemon_running=true
    fi

    if [[ -f "$STATE_FILE" ]]; then
        started_at=$(jq -r '.started_at // ""' "$STATE_FILE")
        if [[ -n "$started_at" && "$daemon_running" == "true" ]]; then
            local start_epoch
            # Strip Z suffix and parse as UTC - macOS date -j doesn't respect Z timezone suffix
            local clean_ts="${started_at%Z}"
            start_epoch=$(TZ=UTC date -j -f "%Y-%m-%dT%H:%M:%S" "$clean_ts" +%s 2>/dev/null || date -d "$started_at" +%s 2>/dev/null || echo "0")
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
    local enricher_sessions=()
    local aristotle_status="stopped"
    local researcher_sessions=()
    local auditor_sessions=()
    local peer_reviewer_sessions=()
    local seeker_status="stopped"
    local deployer_status="stopped"
    local tester_status="stopped"
    local herald_status="stopped"
    local mechanic_sessions=()

    # Enrichers
    for i in 1 2 3 4 5; do
        if session_exists "enricher-$i"; then
            enricher_sessions+=("enricher-$i:$(get_session_uptime "enricher-$i")")
        fi
    done

    # Aristotle (issue #22471: SCALED_TO_ZERO is distinct from "stopped").
    if session_exists "aristotle-agent"; then
        aristotle_status="running:$(get_session_uptime "aristotle-agent")"
    elif [[ -f "$ARISTOTLE_SCALED_MARKER" ]]; then
        local scaled_at
        scaled_at=$(jq -r '.scaled_at // "unknown"' "$ARISTOTLE_SCALED_MARKER" 2>/dev/null || echo "unknown")
        aristotle_status="scaled_to_zero:$scaled_at"
    fi

    # Researchers (up to 16 supported)
    for i in $(seq 1 16); do
        if session_exists "researcher-$i"; then
            researcher_sessions+=("researcher-$i:$(get_session_uptime "researcher-$i")")
        fi
    done

    # Auditors
    if session_exists "auditor-agent"; then
        auditor_sessions+=("auditor-agent:$(get_session_uptime "auditor-agent")")
    fi
    for i in 1 2 3; do
        if session_exists "auditor-$i"; then
            auditor_sessions+=("auditor-$i:$(get_session_uptime "auditor-$i")")
        fi
    done

    # Peer Reviewers
    for i in 1 2; do
        if session_exists "peer-reviewer-$i"; then
            peer_reviewer_sessions+=("peer-reviewer-$i:$(get_session_uptime "peer-reviewer-$i")")
        fi
    done

    # Seeker
    if session_exists "seeker-agent"; then
        seeker_status="running:$(get_session_uptime "seeker-agent")"
    fi

    # Deployer
    if session_exists "deployer"; then
        deployer_status="running:$(get_session_uptime "deployer")"
    fi

    # Tester
    if session_exists "tester-agent"; then
        tester_status="running:$(get_session_uptime "tester-agent")"
    fi

    # Herald
    if session_exists "herald-agent"; then
        herald_status="running:$(get_session_uptime "herald-agent")"
    fi

    # Mechanics
    for i in 1 2 3; do
        if session_exists "mechanic-$i"; then
            mechanic_sessions+=("mechanic-$i:$(get_session_uptime "mechanic-$i")")
        fi
    done
    if session_exists "mechanic-agent"; then
        mechanic_sessions+=("mechanic-agent:$(get_session_uptime "mechanic-agent")")
    fi

    # Work queue counts
    local enrichment_count
    local aristotle_jobs
    local aristotle_candidates
    local research_problems
    local ready_prs

    enrichment_count=$(count_enrichment_targets)
    aristotle_jobs=$(count_aristotle_jobs)
    aristotle_candidates=$(count_aristotle_candidates)
    research_problems=$(count_research_problems)
    ready_prs=$(count_ready_prs)

    # Session stats from state file
    local entries_enriched=0
    local proofs_submitted=0
    local problems_selected=0
    local deployments=0
    local research_completed=0

    if [[ -f "$STATE_FILE" ]]; then
        entries_enriched=$(jq -r '.session_stats.entries_enriched // 0' "$STATE_FILE")
        proofs_submitted=$(jq -r '.session_stats.proofs_submitted // 0' "$STATE_FILE")
        problems_selected=$(jq -r '.session_stats.problems_selected // 0' "$STATE_FILE")
        deployments=$(jq -r '.session_stats.deployments // 0' "$STATE_FILE")
        research_completed=$(jq -r '.session_stats.research_completed // 0' "$STATE_FILE")
    fi

    # Read schedule info from state file
    local schedule_window=""
    local schedule_time=""
    if [[ -f "$STATE_FILE" ]]; then
        schedule_window=$(jq -r '.schedule_window // ""' "$STATE_FILE" 2>/dev/null)
        schedule_time=$(jq -r '.schedule_time // ""' "$STATE_FILE" 2>/dev/null)
    fi

    if $JSON_OUTPUT; then
        # Persistently-missing configured agents recorded by the daemon (#39652).
        local missing_agents_json="[]"
        if [[ -f "$STATE_FILE" ]] && jq empty "$STATE_FILE" >/dev/null 2>&1; then
            missing_agents_json=$(jq -c '.missing_agents // []' "$STATE_FILE" 2>/dev/null || echo "[]")
        fi
        # Output as JSON
        cat <<EOF
{
  "daemon": {
    "running": $daemon_running,
    "uptime": "$daemon_uptime",
    "started_at": "$started_at",
    "schedule_window": "$schedule_window",
    "schedule_time": "$schedule_time"
  },
  "work_queue": {
    "proofs_needing_enrichment": "$enrichment_count",
    "aristotle_pending": $aristotle_jobs,
    "aristotle_candidates": $aristotle_candidates,
    "research_available": $research_problems,
    "prs_ready": $ready_prs
  },
  "agents": {
    "enricher": {
      "count": ${#enricher_sessions[@]},
      "sessions": $(printf '%s\n' "${enricher_sessions[@]:-}" | jq -R -s -c 'split("\n") | map(select(length > 0))')
    },
    "aristotle": {
      "status": "${aristotle_status%%:*}",
      "uptime": "${aristotle_status#*:}"
    },
    "researcher": {
      "count": ${#researcher_sessions[@]},
      "sessions": $(printf '%s\n' "${researcher_sessions[@]:-}" | jq -R -s -c 'split("\n") | map(select(length > 0))')
    },
    "seeker": {
      "status": "${seeker_status%%:*}",
      "uptime": "${seeker_status#*:}"
    },
    "deployer": {
      "status": "${deployer_status%%:*}",
      "uptime": "${deployer_status#*:}"
    },
    "tester": {
      "status": "${tester_status%%:*}",
      "uptime": "${tester_status#*:}"
    },
    "herald": {
      "status": "${herald_status%%:*}",
      "uptime": "${herald_status#*:}"
    },
    "auditor": {
      "count": ${#auditor_sessions[@]},
      "sessions": $(printf '%s\n' "${auditor_sessions[@]:-}" | jq -R -s -c 'split("\n") | map(select(length > 0))')
    },
    "peer_reviewer": {
      "count": ${#peer_reviewer_sessions[@]},
      "sessions": $(printf '%s\n' "${peer_reviewer_sessions[@]:-}" | jq -R -s -c 'split("\n") | map(select(length > 0))')
    },
    "mechanic": {
      "count": ${#mechanic_sessions[@]},
      "sessions": $(printf '%s\n' "${mechanic_sessions[@]:-}" | jq -R -s -c 'split("\n") | map(select(length > 0))')
    }
  },
  "missing_agents": $missing_agents_json,
  "session_stats": {
    "entries_enriched": $entries_enriched,
    "proofs_submitted": $proofs_submitted,
    "problems_selected": $problems_selected,
    "deployments": $deployments,
    "research_completed": $research_completed
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
            # Count live agent tmux sessions other than the daemon itself.
            # A daemon-down state is benign if nothing is running, but loud
            # if agents exist — they're unsupervised: no respawn on STUCK,
            # no token rotation, no scheduled work generation.
            local _live_agents
            _live_agents=$(tmux ls 2>/dev/null | grep -cE '^(researcher-|enricher-|mechanic-|auditor-|aristotle-|seeker-|deployer|tester-|herald-|peer-reviewer-)' || echo 0)
            if [[ "$_live_agents" -gt 0 ]]; then
                echo -e "  Daemon: ${RED}NOT RUNNING${NC} — ${RED}${_live_agents} agent session(s) are unsupervised${NC}"
                echo -e "          ${YELLOW}Stuck agents will not be respawned; tokens will not rotate.${NC}"
                echo -e "          ${YELLOW}Start the supervisor:${NC}"
                echo -e "            ${BOLD}tmux new-session -d -s lean-daemon './scripts/lean/launch.sh daemon --monitor-only'${NC}"
            else
                echo -e "  Daemon: ${YELLOW}Not running${NC} (no agents active)"
            fi
        fi

        # Schedule window (if active)
        if [[ -f "$STATE_FILE" ]]; then
            local schedule_window
            schedule_window=$(jq -r '.schedule_window // ""' "$STATE_FILE" 2>/dev/null)
            if [[ -n "$schedule_window" ]]; then
                local schedule_time
                schedule_time=$(jq -r '.schedule_time // ""' "$STATE_FILE" 2>/dev/null)
                echo -e "  Schedule: ${CYAN}${schedule_window}${NC} (as of ${schedule_time})"
            fi
        fi
        echo ""

        # Work Queue
        echo -e "  ${CYAN}Work Queue:${NC}"
        echo "    Proofs needing enrichment: $enrichment_count"
        # Enrichment-saturation signal (issue #43008): when the queue is empty,
        # any running enrichers are idle or reduced to score-ceiling noise
        # (find-targets serving only 96+-quality entries). Flag it so operators
        # know enricher slots are better spent on researchers.
        if [[ "$enrichment_count" == "0" ]]; then
            echo -e "      ${YELLOW}Enrichment queue saturated — enricher capacity may be idle;${NC}"
            echo -e "      ${YELLOW}consider './scripts/lean/launch.sh scale enricher 1' and adding researchers.${NC}"
        fi
        echo "    Aristotle jobs pending: $aristotle_jobs"
        echo "    Aristotle candidates: $aristotle_candidates"
        echo "    Research problems available: $research_problems"
        echo "    PRs ready to merge: $ready_prs"

        # Aristotle yield (real success metrics from stats.sh)
        if [[ -x "scripts/aristotle/stats.sh" && -f "$ARISTOTLE_JOBS" ]]; then
            local aristotle_yield
            aristotle_yield=$(./scripts/aristotle/stats.sh --oneline 2>/dev/null || echo "")
            if [[ -n "$aristotle_yield" ]]; then
                echo "    Aristotle yield: $aristotle_yield"
            fi
        fi
        echo ""

        # Agent Pool
        echo -e "  ${CYAN}Agent Pool:${NC}"

        # Enrichers
        local enricher_count=${#enricher_sessions[@]}
        if [[ $enricher_count -gt 0 ]]; then
            echo -e "    ${BOLD}Enrichers:${NC} ${GREEN}$enricher_count active${NC}"
            for session in "${enricher_sessions[@]}"; do
                local name="${session%%:*}"
                local uptime="${session#*:}"
                echo "      $name: Running ($uptime)"
            done
        else
            echo -e "    ${BOLD}Enrichers:${NC} ${YELLOW}0 active${NC}"
        fi

        # Aristotle (issue #22471: surface SCALED_TO_ZERO so operators
        # know the missing session is intentional, not a crash).
        if [[ "${aristotle_status%%:*}" == "running" ]]; then
            echo -e "    ${BOLD}Aristotle:${NC} ${GREEN}1/1 active${NC}"
            echo "      aristotle-agent: Running (${aristotle_status#*:})"
        elif [[ "${aristotle_status%%:*}" == "scaled_to_zero" ]]; then
            echo -e "    ${BOLD}Aristotle:${NC} ${YELLOW}SCALED_TO_ZERO${NC} (daemon will respawn when queue has work)"
            echo "      aristotle-agent: scaled at ${aristotle_status#*:}"
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

        # Auditor
        local auditor_count=${#auditor_sessions[@]}
        if [[ $auditor_count -gt 0 ]]; then
            echo -e "    ${BOLD}Auditor:${NC} ${GREEN}$auditor_count active${NC}"
            for session in "${auditor_sessions[@]}"; do
                local name="${session%%:*}"
                local uptime="${session#*:}"
                echo "      $name: Running ($uptime)"
            done
        else
            echo -e "    ${BOLD}Auditor:${NC} ${YELLOW}0 active${NC}"
        fi

        # Peer Reviewer
        local peer_reviewer_count=${#peer_reviewer_sessions[@]}
        if [[ $peer_reviewer_count -gt 0 ]]; then
            echo -e "    ${BOLD}Peer Reviewer:${NC} ${GREEN}$peer_reviewer_count active${NC}"
            for session in "${peer_reviewer_sessions[@]}"; do
                local name="${session%%:*}"
                local uptime="${session#*:}"
                echo "      $name: Running ($uptime)"
            done
        else
            echo -e "    ${BOLD}Peer Reviewer:${NC} ${YELLOW}0 active${NC}"
        fi

        # Seeker
        if [[ "${seeker_status%%:*}" == "running" ]]; then
            echo -e "    ${BOLD}Seeker:${NC} ${GREEN}1/1 active${NC}"
            echo "      seeker-agent: Running (${seeker_status#*:})"
        else
            echo -e "    ${BOLD}Seeker:${NC} ${YELLOW}0/1 active${NC}"
        fi

        # Deployer
        if [[ "${deployer_status%%:*}" == "running" ]]; then
            echo -e "    ${BOLD}Deployer:${NC} ${GREEN}1/1 active${NC}"
            echo "      deployer: Running (${deployer_status#*:})"
        else
            echo -e "    ${BOLD}Deployer:${NC} ${YELLOW}0/1 active${NC}"
        fi

        # Tester
        if [[ "${tester_status%%:*}" == "running" ]]; then
            echo -e "    ${BOLD}Tester:${NC} ${GREEN}1/1 active${NC}"
            echo "      tester-agent: Running (${tester_status#*:})"
        else
            echo -e "    ${BOLD}Tester:${NC} ${YELLOW}0/1 active${NC}"
        fi

        # Herald
        if [[ "${herald_status%%:*}" == "running" ]]; then
            echo -e "    ${BOLD}Herald:${NC} ${GREEN}1/1 active${NC}"
            echo "      herald-agent: Running (${herald_status#*:})"
        else
            echo -e "    ${BOLD}Herald:${NC} ${YELLOW}0/1 active${NC}"
        fi

        # Mechanic
        local mechanic_count=${#mechanic_sessions[@]}
        if [[ $mechanic_count -gt 0 ]]; then
            echo -e "    ${BOLD}Mechanic:${NC} ${GREEN}$mechanic_count active${NC}"
            for session in "${mechanic_sessions[@]}"; do
                local name="${session%%:*}"
                local uptime="${session#*:}"
                echo "      $name: Running ($uptime)"
            done
        else
            echo -e "    ${BOLD}Mechanic:${NC} ${YELLOW}0 active${NC}"
        fi

        # Persistently-missing configured agents (#39652). The daemon records a
        # .missing_agents array when a configured agent has had no live session
        # for several consecutive cycles (e.g. a silently-dying launcher). Surface
        # it loudly instead of leaving it buried in the "0 active" rows above.
        if [[ -f "$STATE_FILE" ]] && jq empty "$STATE_FILE" >/dev/null 2>&1; then
            local missing_rows
            missing_rows=$(jq -r \
                '(.missing_agents // [])
                 | map("      \(.type): configured \(.configured), running \(.running) (\(.missing_cycles) cycles)")
                 | .[]' \
                "$STATE_FILE" 2>/dev/null || echo "")
            if [[ -n "$missing_rows" ]]; then
                echo ""
                echo -e "    ${RED}MISSING (configured but no session):${NC}"
                echo -e "${RED}${missing_rows}${NC}"
            fi
        fi
        echo ""

        # Session Stats
        echo -e "  ${CYAN}Session Stats:${NC}"
        echo "    Entries enriched: $entries_enriched"
        echo "    Proofs submitted: $proofs_submitted"
        echo "    Research completed: $research_completed"
        echo "    Problems selected: $problems_selected"
        echo "    Deployments: $deployments"

        echo -e "${BOLD}═══════════════════════════════════════════════════${NC}"
        echo ""

        # Commands hint
        echo -e "  ${BLUE}Commands:${NC}"
        echo "    /lean start --researcher 3              Start agents"
        echo "    /lean spawn researcher                  Add one Researcher"
        echo "    /lean spawn seeker                      Add seeker agent"
        echo "    /lean scale researcher 4                Scale to 4 Researchers"
        echo "    /lean stop                              Stop all agents"
        echo ""
    fi
}

# Run
gather_status
