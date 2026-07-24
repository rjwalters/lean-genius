#!/usr/bin/env bash
#
# Lean Genius Launch - Start/stop/scale the mathematical agent team
#
# Usage:
#   ./scripts/lean/launch.sh start [--enricher N] [--aristotle N] [--researcher N] [--seeker N] [--deployer N]
#   ./scripts/lean/launch.sh stop [type] [--force]
#   ./scripts/lean/launch.sh health
#   ./scripts/lean/launch.sh spawn enricher|aristotle|researcher|seeker|deployer
#   ./scripts/lean/launch.sh scale enricher|aristotle|researcher|seeker|deployer N
#   ./scripts/lean/launch.sh status
#   ./scripts/lean/launch.sh daemon [--interval N] [--enricher N] [--researcher N] [...]
#

set -euo pipefail

# Shared per-workflow worktree reclaim helper. Provides `remove_own_worktree`,
# which applies structural safety guards (1-5) before removing an agent's
# worktree instead of the unconditional `git worktree remove --force || rm -rf`
# that could silently destroy an in-flight agent's uncommitted work (#35255,
# follow-up to #35223 / PR #35237). Anchored to this script's own directory so
# it resolves regardless of the caller's cwd.
_LAUNCH_SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
# shellcheck source=../lib/worktree-cleanup.sh
source "$_LAUNCH_SCRIPT_DIR/../lib/worktree-cleanup.sh"

# Worktree-root resolver (LOOM_WORKTREE_ROOT env var / .loom/config.json
# worktree.root override; default $repo_root/.loom/worktrees). Respawned agent
# worktrees must land at the same resolved base the role launchers use.
# shellcheck source=../lib/worktree-root.sh
source "$_LAUNCH_SCRIPT_DIR/../lib/worktree-root.sh"

# Canonical completion-signal directory resolver. Producers (enricher,
# researcher, deployer, aristotle) run in worktrees; the daemon consumes signals
# from the main checkout. Both sides must resolve the SAME
# .loom/signals/completions or session_stats never increment (#41047).
# shellcheck source=../lib/completions-dir.sh
source "$_LAUNCH_SCRIPT_DIR/../lib/completions-dir.sh"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[0;33m'
BLUE='\033[0;34m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m'

# Config
STATE_FILE=".loom/lean-daemon-state.json"
OLD_STATE_FILE="research/lean-daemon-state.json"
SIGNALS_DIR=".loom/signals"
COMPLETIONS_DIR="$SIGNALS_DIR/completions"
STOP_SIGNAL_FILE="$SIGNALS_DIR/stop-lean-daemon"
DAEMON_PID_FILE="research/lean-daemon.pid"
DAEMON_LOG_FILE="research/lean-daemon.log"
SCHEDULE_FILE=".loom/lean-schedule.json"

# Aristotle scale-to-zero marker (issue #22471). Written by aristotle-agent.sh
# when it gracefully exits on an empty queue + idle threshold elapsed; read by
# get_agent_status / status display / dynamic spawn logic.
ARISTOTLE_SCALED_MARKER=".loom/state/aristotle-scaled-to-zero"

# Health check thresholds
STUCK_THRESHOLD_MINUTES=30
STUCK_CPU_THRESHOLD="0.5"
# Agent statuses: RUNNING, COMPLETED, STUCK, IDLE, SCALED_TO_ZERO, UNKNOWN
# IDLE = polling agent (deployer/seeker) that is healthy but waiting between cycles
# SCALED_TO_ZERO = aristotle gracefully exited due to empty queue (issue #22471).
#                  Distinct from STUCK/IDLE/COMPLETED — the daemon will respawn
#                  it when find-candidates.sh --count or submitted-job count > 0.

# Daemon defaults
DEFAULT_DAEMON_INTERVAL=60
RESPAWN_COOLDOWN_SECONDS=300  # 5 minutes between respawns of same agent

# Persistent-missing-session alerting (#39652). A configured agent whose session
# is absent for a single cycle is routine (mid-respawn, cooldown). Only after
# this many CONSECUTIVE cycles below target does the daemon escalate from a
# routine "pool gap" INFO to a MISSING WARN and surface a red row in
# `/lean health` / `/lean status`. Kept small so a genuine multi-cycle outage
# (e.g. the deployer that went unnoticed for 7 days) is caught within minutes.
MISSING_SESSION_ALERT_CYCLES=3

# Default pool sizes
# Rebalanced (issue #43008): 1 enricher, 3 researchers. The enrichment queue has
# been at its quality floor (find-targets serving only 96+-quality noise), so
# capacity moves back to research. Support agents sleep between cycles.
DEFAULT_ENRICHER=1
DEFAULT_ARISTOTLE=1
DEFAULT_RESEARCHER=3
DEFAULT_SEEKER=1
DEFAULT_DEPLOYER=1
DEFAULT_AUDITOR=1
DEFAULT_TESTER=1
DEFAULT_HERALD=1
DEFAULT_MECHANIC=1

# Max pool sizes
MAX_ENRICHER=5
MAX_ARISTOTLE=2
MAX_RESEARCHER=16
MAX_AUDITOR=3
MAX_SEEKER=1
MAX_DEPLOYER=1
MAX_TESTER=1
MAX_HERALD=1
MAX_MECHANIC=3

# Helper: Print usage
usage() {
    cat <<EOF
Lean Genius Launch - Mathematical Agent Orchestration

Usage:
  $0 start [options]     Start agents with specified pool sizes
  $0 stop [type] [--force]  Stop all agents or a specific type (graceful by default)
  $0 health              Show agent process health and detect stuck agents
  $0 spawn <type>        Spawn one additional agent
  $0 scale <type> <N>    Scale agent pool to N instances (supports scale-down)
  $0 status              Show current status
  $0 wake [type]         Wake a sleeping agent early (all, aristotle, researcher, deployer, seeker, enricher)
  $0 daemon [options]    Run continuous monitoring daemon

Start Options:
  --enricher N           Number of Enrichers (default: $DEFAULT_ENRICHER, max: $MAX_ENRICHER)
  --aristotle N          Number of Aristotle agents (default: $DEFAULT_ARISTOTLE, max: $MAX_ARISTOTLE)
  --researcher N         Number of Researchers (default: $DEFAULT_RESEARCHER, max: $MAX_RESEARCHER)
  --seeker N             Number of Seeker agents (default: $DEFAULT_SEEKER, max: $MAX_SEEKER)
  --deployer N           Number of Deployers (default: $DEFAULT_DEPLOYER, max: $MAX_DEPLOYER)
  --auditor N            Number of Auditors (default: $DEFAULT_AUDITOR, max: $MAX_AUDITOR)
  --tester N             Number of Testers (default: $DEFAULT_TESTER, max: $MAX_TESTER)
  --herald N             Number of Heralds (default: $DEFAULT_HERALD, max: $MAX_HERALD)
  --mechanic N           Number of Mechanics (default: $DEFAULT_MECHANIC, max: $MAX_MECHANIC)

Stop Options:
  <type>                 Stop only agents of this type (enricher, aristotle, etc.)
  --force                Kill tmux sessions immediately (skip graceful signal files)

Daemon Options:
  --monitor-only         Skip agent startup, only monitor/respawn existing sessions
  --interval N           Seconds between health check cycles (default: $DEFAULT_DAEMON_INTERVAL)
  --enricher N           Target Enricher count (default: $DEFAULT_ENRICHER, max: $MAX_ENRICHER)
  --aristotle N          Target Aristotle agent count (default: $DEFAULT_ARISTOTLE, max: $MAX_ARISTOTLE)
  --researcher N         Target Researcher count (default: $DEFAULT_RESEARCHER, max: $MAX_RESEARCHER)
  --auditor N            Target Auditor count (default: $DEFAULT_AUDITOR, max: $MAX_AUDITOR)
  --seeker N             Target Seeker agent count (default: $DEFAULT_SEEKER, max: $MAX_SEEKER)
  --deployer N           Target Deployer count (default: $DEFAULT_DEPLOYER, max: $MAX_DEPLOYER)
  --tester N             Target Tester count (default: $DEFAULT_TESTER, max: $MAX_TESTER)
  --herald N             Target Herald count (default: $DEFAULT_HERALD, max: $MAX_HERALD)
  --mechanic N           Target Mechanic count (default: $DEFAULT_MECHANIC, max: $MAX_MECHANIC)

Agent Types:
  enricher    Enriches proof gallery entries with deeper annotations and commentary
  aristotle   Manages proof search queue for Aristotle system
  researcher  Works on open mathematical problems
  auditor     Audits gallery integrity (proof claims vs Lean source files)
  seeker      Selects research problems when candidate pool runs low
  deployer    Merges PRs and deploys website
  tester      Tests random proof pages on the live site
  herald      Posts noteworthy results to Mathstodon
  mechanic    Repairs issues found by auditors and peer reviewers

Examples:
  $0 start                              # Start with defaults
  $0 start --researcher 3               # Custom pool sizes
  $0 start --enricher 1 --researcher 3  # Include Enrichers
  $0 spawn researcher                   # Add one Researcher
  $0 spawn seeker                       # Add seeker agent
  $0 scale researcher 4                 # Scale to 4 Researchers
  $0 scale enricher 1                   # Scale down to 1 Enricher
  $0 stop                               # Graceful stop all (signal files)
  $0 stop enricher                      # Graceful stop Enrichers only
  $0 stop --force                       # Force stop all (kill sessions)
  $0 stop enricher --force              # Force stop Enrichers only
  $0 health                             # Check agent health
  $0 daemon                             # Start agents + run daemon loop
  $0 daemon --monitor-only              # Monitor existing agents (no startup)
  $0 daemon --interval 30 --researcher 3  # Custom interval and pool
  $0 daemon --monitor-only --researcher 5 &  # Background monitor for 5 researchers
EOF
}

# Helper: Migrate state file from old location (research/) to new location (.loom/)
migrate_state_file() {
    if [[ -f "$OLD_STATE_FILE" && ! -f "$STATE_FILE" ]]; then
        echo -e "${BLUE}Migrating state file to .loom/${NC}"
        mkdir -p "$(dirname "$STATE_FILE")"
        mv "$OLD_STATE_FILE" "$STATE_FILE"
    fi
}

# Helper: Initialize state file
# Preserves session_stats and stopped_at from previous state across daemon restarts
init_state() {
    local enricher="${1:-$DEFAULT_ENRICHER}"
    local aristotle="${2:-$DEFAULT_ARISTOTLE}"
    local researcher="${3:-$DEFAULT_RESEARCHER}"
    local auditor="${4:-$DEFAULT_AUDITOR}"
    local seeker="${5:-$DEFAULT_SEEKER}"
    local deployer="${6:-$DEFAULT_DEPLOYER}"
    local tester="${7:-$DEFAULT_TESTER}"
    local herald="${8:-$DEFAULT_HERALD}"
    local mechanic="${9:-$DEFAULT_MECHANIC}"

    mkdir -p "$(dirname "$STATE_FILE")"

    # Preserve previous session stats if state file exists
    local prev_stats='{}'
    local prev_stopped_at=""
    if [[ -f "$STATE_FILE" ]]; then
        prev_stats=$(jq '.session_stats // {}' "$STATE_FILE" 2>/dev/null || echo '{}')
        prev_stopped_at=$(jq -r '.stopped_at // ""' "$STATE_FILE" 2>/dev/null || echo "")
    fi

    # Build new state JSON with jq for proper structure
    local new_state
    new_state=$(jq -n \
        --arg started_at "$(date -u +"%Y-%m-%dT%H:%M:%SZ")" \
        --argjson enricher "$enricher" \
        --argjson aristotle "$aristotle" \
        --argjson researcher "$researcher" \
        --argjson auditor "$auditor" \
        --argjson seeker "$seeker" \
        --argjson deployer "$deployer" \
        --argjson tester "$tester" \
        --argjson herald "$herald" \
        --argjson mechanic "$mechanic" \
        --argjson prev_stats "$prev_stats" \
        '{
            started_at: $started_at,
            running: true,
            config: {
                enricher: $enricher,
                aristotle: $aristotle,
                researcher: $researcher,
                auditor: $auditor,
                seeker: $seeker,
                deployer: $deployer,
                tester: $tester,
                herald: $herald,
                mechanic: $mechanic
            },
            agents: {},
            session_stats: (
                if ($prev_stats | length) > 0 then $prev_stats
                else {
                    entries_enriched: 0,
                    proofs_submitted: 0,
                    proofs_integrated: 0,
                    problems_selected: 0,
                    deployments: 0,
                    research_completed: 0
                }
                end
            )
        }')

    # Add previous_stopped_at if previous session had a stopped_at timestamp
    if [[ -n "$prev_stopped_at" ]]; then
        new_state=$(echo "$new_state" | jq --arg stopped "$prev_stopped_at" '.previous_stopped_at = $stopped')
    fi

    echo "$new_state" > "$STATE_FILE"
}

# Helper: Mark state as stopped, preserving all existing state data
set_stopped() {
    if [[ -f "$STATE_FILE" ]]; then
        local tmp
        tmp=$(mktemp)
        jq --arg ts "$(date -u +"%Y-%m-%dT%H:%M:%SZ")" \
           '.running = false | .stopped_at = $ts' \
           "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
    fi
}

# Helper: Update daemon state config for a specific agent type
# This prevents the daemon from respawning agents that were intentionally stopped/scaled down
update_daemon_config() {
    local agent_type="$1"
    local count="$2"

    if [[ -f "$STATE_FILE" ]]; then
        local tmp
        tmp=$(mktemp)
        jq --arg type "$agent_type" --argjson count "$count" \
           '.config[$type] = $count' \
           "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
    fi
}

# Helper: Get sessions for a specific agent type
get_sessions_for_type() {
    local agent_type="$1"
    local sessions=()

    case "$agent_type" in
        enricher)
            for i in 1 2 3 4 5; do
                if tmux has-session -t "enricher-$i" 2>/dev/null; then
                    sessions+=("enricher-$i")
                fi
            done
            ;;
        aristotle)
            if tmux has-session -t "aristotle-agent" 2>/dev/null; then
                sessions+=("aristotle-agent")
            fi
            ;;
        researcher)
            for i in $(seq 1 $MAX_RESEARCHER); do
                if tmux has-session -t "researcher-$i" 2>/dev/null; then
                    sessions+=("researcher-$i")
                fi
            done
            ;;
        seeker)
            if tmux has-session -t "seeker-agent" 2>/dev/null; then
                sessions+=("seeker-agent")
            fi
            ;;
        deployer)
            if tmux has-session -t "deployer" 2>/dev/null; then
                sessions+=("deployer")
            fi
            ;;
        auditor)
            if tmux has-session -t "auditor-agent" 2>/dev/null; then
                sessions+=("auditor-agent")
            fi
            ;;
        tester)
            if tmux has-session -t "tester-agent" 2>/dev/null; then
                sessions+=("tester-agent")
            fi
            ;;
        herald)
            if tmux has-session -t "herald-agent" 2>/dev/null; then
                sessions+=("herald-agent")
            fi
            ;;
        mechanic)
            for i in 1 2 3; do
                if tmux has-session -t "mechanic-$i" 2>/dev/null; then
                    sessions+=("mechanic-$i")
                fi
            done
            if tmux has-session -t "mechanic-agent" 2>/dev/null; then
                sessions+=("mechanic-agent")
            fi
            ;;
    esac

    if [[ ${#sessions[@]} -gt 0 ]]; then
        printf '%s\n' "${sessions[@]}"
    fi
}

# Helper: Gracefully stop a specific agent session with signal file
signal_stop_session() {
    local session="$1"
    local agent_type
    agent_type=$(get_agent_type "$session")

    mkdir -p "$SIGNALS_DIR"

    case "$agent_type" in
        enricher)
            local agent_num="${session##*-}"
            touch "$SIGNALS_DIR/stop-enricher-$agent_num"
            ;;
        aristotle)
            touch "$SIGNALS_DIR/stop-aristotle"
            ;;
        researcher)
            local agent_num="${session##*-}"
            touch "$SIGNALS_DIR/stop-researcher-$agent_num"
            ;;
        seeker)
            touch "$SIGNALS_DIR/stop-seeker"
            ;;
        deployer)
            touch "$SIGNALS_DIR/stop-deployer"
            ;;
        auditor)
            touch "$SIGNALS_DIR/stop-auditor"
            ;;
        tester)
            touch "$SIGNALS_DIR/stop-tester"
            ;;
        herald)
            touch "$SIGNALS_DIR/stop-herald"
            ;;
        mechanic)
            touch "$SIGNALS_DIR/stop-mechanic"
            ;;
    esac
}

# Helper: Wait for sessions to stop, with timeout and force-kill fallback
# Args: timeout_seconds session1 [session2 ...]
wait_or_force_kill() {
    local timeout="$1"
    shift
    local sessions=("$@")

    if [[ ${#sessions[@]} -eq 0 ]]; then
        return 0
    fi

    local start
    start=$(date +%s)

    echo -e "${BLUE}Waiting up to ${timeout}s for graceful shutdown...${NC}"

    while true; do
        local now
        now=$(date +%s)
        local elapsed=$((now - start))

        if [[ $elapsed -ge $timeout ]]; then
            local remaining=0
            for session in "${sessions[@]}"; do
                if tmux has-session -t "$session" 2>/dev/null; then
                    echo -e "${YELLOW}Timeout: force-killing $session${NC}"
                    kill_session_processes "$session"
                    remaining=$((remaining + 1))
                fi
            done
            if [[ $remaining -gt 0 ]]; then
                echo -e "${YELLOW}Force-killed $remaining agent(s) after ${timeout}s timeout${NC}"
            fi
            return 0
        fi

        local still_running=0
        for session in "${sessions[@]}"; do
            if tmux has-session -t "$session" 2>/dev/null; then
                still_running=$((still_running + 1))
            fi
        done

        if [[ $still_running -eq 0 ]]; then
            echo -e "${GREEN}All targeted agents stopped gracefully${NC}"
            return 0
        fi

        sleep 2
    done
}

# Helper: Check if script exists
check_script() {
    local script="$1"
    if [[ ! -x "$script" ]]; then
        echo -e "${RED}Error: Script not found or not executable: $script${NC}" >&2
        return 1
    fi
}

# Command: start
cmd_start() {
    local enricher=$DEFAULT_ENRICHER
    local aristotle=$DEFAULT_ARISTOTLE
    local researcher=$DEFAULT_RESEARCHER
    local seeker=$DEFAULT_SEEKER
    local deployer=$DEFAULT_DEPLOYER
    local auditor=$DEFAULT_AUDITOR
    local tester=$DEFAULT_TESTER
    local herald=$DEFAULT_HERALD
    local mechanic=$DEFAULT_MECHANIC

    # Apply time-based schedule (overrides defaults before CLI args)
    apply_schedule

    # Parse options (explicit CLI args override schedule)
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --enricher)
                enricher="$2"
                shift 2
                ;;
            --aristotle)
                aristotle="$2"
                shift 2
                ;;
            --researcher)
                researcher="$2"
                shift 2
                ;;
            --auditor)
                auditor="$2"
                shift 2
                ;;
            --seeker)
                seeker="$2"
                shift 2
                ;;
            --deployer)
                deployer="$2"
                shift 2
                ;;
            --tester)
                tester="$2"
                shift 2
                ;;
            --herald)
                herald="$2"
                shift 2
                ;;
            --mechanic)
                mechanic="$2"
                shift 2
                ;;
            *)
                echo -e "${RED}Unknown option: $1${NC}" >&2
                usage
                exit 1
                ;;
        esac
    done

    # Validate counts
    if [[ $enricher -gt $MAX_ENRICHER ]]; then
        echo -e "${YELLOW}Warning: Enricher count $enricher exceeds max $MAX_ENRICHER, using $MAX_ENRICHER${NC}"
        enricher=$MAX_ENRICHER
    fi
    if [[ $aristotle -gt $MAX_ARISTOTLE ]]; then
        echo -e "${YELLOW}Warning: Aristotle count $aristotle exceeds max $MAX_ARISTOTLE, using $MAX_ARISTOTLE${NC}"
        aristotle=$MAX_ARISTOTLE
    fi
    if [[ $researcher -gt $MAX_RESEARCHER ]]; then
        echo -e "${YELLOW}Warning: Researcher count $researcher exceeds max $MAX_RESEARCHER, using $MAX_RESEARCHER${NC}"
        researcher=$MAX_RESEARCHER
    fi
    if [[ $seeker -gt $MAX_SEEKER ]]; then
        echo -e "${YELLOW}Warning: Seeker count $seeker exceeds max $MAX_SEEKER, using $MAX_SEEKER${NC}"
        seeker=$MAX_SEEKER
    fi
    if [[ $auditor -gt $MAX_AUDITOR ]]; then
        echo -e "${YELLOW}Warning: Auditor count $auditor exceeds max $MAX_AUDITOR, using $MAX_AUDITOR${NC}"
        auditor=$MAX_AUDITOR
    fi
    if [[ $deployer -gt $MAX_DEPLOYER ]]; then
        echo -e "${YELLOW}Warning: Deployer count $deployer exceeds max $MAX_DEPLOYER, using $MAX_DEPLOYER${NC}"
        deployer=$MAX_DEPLOYER
    fi
    if [[ $tester -gt $MAX_TESTER ]]; then
        echo -e "${YELLOW}Warning: Tester count $tester exceeds max $MAX_TESTER, using $MAX_TESTER${NC}"
        tester=$MAX_TESTER
    fi
    if [[ $herald -gt $MAX_HERALD ]]; then
        echo -e "${YELLOW}Warning: Herald count $herald exceeds max $MAX_HERALD, using $MAX_HERALD${NC}"
        herald=$MAX_HERALD
    fi
    if [[ $mechanic -gt $MAX_MECHANIC ]]; then
        echo -e "${YELLOW}Warning: Mechanic count $mechanic exceeds max $MAX_MECHANIC, using $MAX_MECHANIC${NC}"
        mechanic=$MAX_MECHANIC
    fi

    echo -e "${BOLD}Starting Lean Genius Mathematical Orchestration${NC}"
    echo ""
    echo -e "Configuration:"
    echo "  Enrichers: $enricher"
    echo "  Aristotle Agents: $aristotle"
    echo "  Researchers: $researcher"
    echo "  Auditors: $auditor"
    echo "  Seekers: $seeker"
    echo "  Deployers: $deployer"
    echo "  Testers: $tester"
    echo "  Heralds: $herald"
    echo "  Mechanics: $mechanic"
    echo ""

    # Migrate state file from old location if needed
    migrate_state_file

    # Initialize state
    init_state "$enricher" "$aristotle" "$researcher" "$auditor" "$seeker" "$deployer" "$tester" "$herald" "$mechanic"

    # Start agents
    local started=0

    # Enrichers
    if [[ $enricher -gt 0 ]]; then
        echo -e "${BLUE}Starting $enricher Enricher(s)...${NC}"
        if check_script "./scripts/enricher/parallel-enrich.sh"; then
            ./scripts/enricher/parallel-enrich.sh "$enricher" &
            sleep 2
            echo -e "${GREEN}✓ Enrichers launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Aristotle
    if [[ $aristotle -gt 0 ]]; then
        echo -e "${BLUE}Starting Aristotle agent...${NC}"
        if check_script "./scripts/aristotle/launch-agent.sh"; then
            ./scripts/aristotle/launch-agent.sh &
            sleep 1
            echo -e "${GREEN}✓ Aristotle agent launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Researchers
    if [[ $researcher -gt 0 ]]; then
        echo -e "${BLUE}Starting $researcher Researcher(s)...${NC}"
        if check_script "./scripts/research/parallel-research.sh"; then
            ./scripts/research/parallel-research.sh "$researcher" &
            sleep 2
            echo -e "${GREEN}✓ Researchers launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Seeker
    if [[ $seeker -gt 0 ]]; then
        echo -e "${BLUE}Starting Seeker agent...${NC}"
        if check_script "./scripts/research/launch-seeker.sh"; then
            ./scripts/research/launch-seeker.sh &
            sleep 1
            echo -e "${GREEN}✓ Seeker agent launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Deployer
    if [[ $deployer -gt 0 ]]; then
        echo -e "${BLUE}Starting Deployer...${NC}"
        if check_script "./scripts/deploy/launch-agent.sh"; then
            ./scripts/deploy/launch-agent.sh &
            sleep 1
            echo -e "${GREEN}✓ Deployer launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Auditor
    if [[ $auditor -gt 0 ]]; then
        echo -e "${BLUE}Starting Auditor agent...${NC}"
        if check_script "./scripts/auditor/launch-agent.sh"; then
            ./scripts/auditor/launch-agent.sh &
            sleep 1
            echo -e "${GREEN}\xe2\x9c\x93 Auditor agent launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Mechanic
    if [[ $mechanic -gt 0 ]]; then
        echo -e "${BLUE}Starting Mechanic agent...${NC}"
        if check_script "./scripts/mechanic/launch-agent.sh"; then
            ./scripts/mechanic/launch-agent.sh &
            sleep 1
            echo -e "${GREEN}✓ Mechanic agent launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Tester
    if [[ $tester -gt 0 ]]; then
        echo -e "${BLUE}Starting Tester agent...${NC}"
        if check_script "./scripts/test/launch-agent.sh"; then
            ./scripts/test/launch-agent.sh &
            sleep 1
            echo -e "${GREEN}✓ Tester agent launched${NC}"
            started=$((started + 1))
        fi
    fi

    # Herald
    if [[ $herald -gt 0 ]]; then
        echo -e "${BLUE}Starting Herald agent...${NC}"
        if check_script "./scripts/herald/launch-agent.sh"; then
            ./scripts/herald/launch-agent.sh &
            sleep 1
            echo -e "${GREEN}✓ Herald agent launched${NC}"
            started=$((started + 1))
        fi
    fi

    echo ""
    if [[ $started -gt 0 ]]; then
        echo -e "${GREEN}${BOLD}✓ Lean Genius team started!${NC}"
        echo ""
        echo "Commands:"
        echo "  ./scripts/lean/status.sh        Show status"
        echo "  ./scripts/lean/launch.sh stop   Stop all agents"
    else
        echo -e "${RED}No agents were started. Check script paths.${NC}"
        exit 1
    fi
}

# Helper: Get all known agent tmux session names
get_all_agent_sessions() {
    local sessions=()
    # Enrichers
    for i in 1 2 3 4 5; do
        if tmux has-session -t "enricher-$i" 2>/dev/null; then
            sessions+=("enricher-$i")
        fi
    done
    # Aristotle
    if tmux has-session -t "aristotle-agent" 2>/dev/null; then
        sessions+=("aristotle-agent")
    fi
    # Researchers
    for i in $(seq 1 $MAX_RESEARCHER); do
        if tmux has-session -t "researcher-$i" 2>/dev/null; then
            sessions+=("researcher-$i")
        fi
    done
    # Seeker
    if tmux has-session -t "seeker-agent" 2>/dev/null; then
        sessions+=("seeker-agent")
    fi
    # Deployer
    if tmux has-session -t "deployer" 2>/dev/null; then
        sessions+=("deployer")
    fi
    # Auditor
    if tmux has-session -t "auditor-agent" 2>/dev/null; then
        sessions+=("auditor-agent")
    fi
    # Tester
    if tmux has-session -t "tester-agent" 2>/dev/null; then
        sessions+=("tester-agent")
    fi
    # Herald
    if tmux has-session -t "herald-agent" 2>/dev/null; then
        sessions+=("herald-agent")
    fi
    # Mechanic
    for i in 1 2 3; do
        if tmux has-session -t "mechanic-$i" 2>/dev/null; then
            sessions+=("mechanic-$i")
        fi
    done
    if tmux has-session -t "mechanic-agent" 2>/dev/null; then
        sessions+=("mechanic-agent")
    fi
    if [[ ${#sessions[@]} -gt 0 ]]; then
        printf '%s\n' "${sessions[@]}"
    fi
}

# Helper: Get the pane PID for a tmux session
get_pane_pid() {
    local session="$1"
    tmux list-panes -t "$session" -F '#{pane_pid}' 2>/dev/null | head -1
}

# Helper: Find child claude processes for a given PID
# Walks the entire process subtree rooted at parent_pid to find a claude process.
# This handles arbitrary nesting depth (e.g., shell -> wrapper -> timeout -> claude).
# Uses a single `ps` call to snapshot the process tree, then walks it via awk.
find_claude_child() {
    local parent_pid="$1"

    # Snapshot the entire process table once, then use awk to:
    # 1. Build a set of PIDs in the subtree rooted at parent_pid
    # 2. Return the first process whose command matches "claude"
    #
    # We make multiple passes over the data to handle arbitrary depth,
    # since ps output order is not guaranteed to be parent-before-child.
    ps -eo pid,ppid,comm 2>/dev/null | awk -v root="$parent_pid" '
        NR == 1 { next }  # Skip header
        {
            pid = $1 + 0
            ppid = $2 + 0
            cmd = $3
            pids[NR] = pid
            ppids[NR] = ppid
            cmds[NR] = cmd
            count = NR
        }
        END {
            # Seed the subtree with the root PID
            intree[root] = 1
            # Iteratively expand the subtree until no new PIDs are added.
            # Each pass discovers one more level of descendants.
            changed = 1
            while (changed) {
                changed = 0
                for (i = 2; i <= count; i++) {
                    if (!intree[pids[i]] && intree[ppids[i]]) {
                        intree[pids[i]] = 1
                        changed = 1
                    }
                }
            }
            # Now find the first claude process in the subtree (excluding root)
            for (i = 2; i <= count; i++) {
                if (intree[pids[i]] && pids[i] != root && cmds[i] ~ /claude/) {
                    print pids[i]
                    exit 0
                }
            }
        }
    '
}

# Helper: Collect every descendant PID of $1 (full process tree).
#
# Performs a breadth-first walk via repeated `pgrep -P` lookups so that
# grandchildren, great-grandchildren, and arbitrarily deep descendants
# (e.g. claude -> zsh shell-snapshot -> bash docker-build.sh -> docker)
# are all captured before we start signalling anything.
#
# Capturing the full set up-front (rather than recursing post-order)
# matters because once we start sending signals, descendants get
# re-parented to init (PPID=1) and a parent-based walk loses them.
#
# Echoes one PID per line, deepest descendants first, root pid last.
# See #15191 for the orphan-grandchildren bug this guards against.
collect_proc_tree() {
    local root="$1"
    [[ -z "$root" ]] && return 0

    local -a queue=("$root")
    local -a order=()
    local head=0
    while [[ $head -lt ${#queue[@]} ]]; do
        local cur="${queue[$head]}"
        head=$((head + 1))
        order+=("$cur")
        local kids
        kids=$(pgrep -P "$cur" 2>/dev/null || true)
        if [[ -n "$kids" ]]; then
            local k
            for k in $kids; do
                queue+=("$k")
            done
        fi
    done

    # Emit in reverse-BFS order so leaves are killed before their parents.
    local i
    for (( i=${#order[@]}-1; i>=0; i-- )); do
        echo "${order[$i]}"
    done
}

# Helper: Kill all processes in a tmux session before destroying it.
# This prevents orphaned claude/timeout processes when tmux SIGHUP
# doesn't propagate across process group boundaries.
#
# Walks the FULL process subtree (not just direct children) so that
# nested shells, docker-build.sh wrappers, and the docker CLI itself
# get signaled too. See #15191.
kill_proc_tree() {
    local pid="$1"
    local sig="${2:-TERM}"

    [[ -z "$pid" ]] && return 0
    kill -0 "$pid" 2>/dev/null || return 0

    local tree
    tree=$(collect_proc_tree "$pid")
    [[ -z "$tree" ]] && return 0

    local p
    while IFS= read -r p; do
        [[ -z "$p" ]] && continue
        kill "-$sig" "$p" 2>/dev/null || true
    done <<< "$tree"
}

# Helper: Kill every process matching $1 (pgrep -f pattern) AND all of
# their descendants. Standard `pkill -f` only signals the matched
# process, so grandchildren (zsh shell-snapshot -> bash -> docker) get
# orphaned to init and survive every "force stop". See #15191.
#
# $1 = pgrep -f pattern
# $2 = signal name (default TERM)
kill_pattern_tree() {
    local pattern="$1"
    local sig="${2:-TERM}"

    local matches
    matches=$(pgrep -f "$pattern" 2>/dev/null || true)
    [[ -z "$matches" ]] && return 0

    local m
    for m in $matches; do
        kill_proc_tree "$m" "$sig"
    done
}

kill_session_processes() {
    local session="$1"

    # Find and kill claude process before destroying the session
    local pane_pid
    pane_pid=$(tmux list-panes -t "$session" -F '#{pane_pid}' 2>/dev/null | head -1)

    if [[ -n "$pane_pid" ]]; then
        kill_proc_tree "$pane_pid" TERM
    fi

    # Now kill the tmux session
    tmux kill-session -t "$session" 2>/dev/null || true

    # Brief wait for processes to exit
    sleep 1

    if [[ -n "$pane_pid" ]] && kill -0 "$pane_pid" 2>/dev/null; then
        kill_proc_tree "$pane_pid" KILL
    fi
}

# Helper: Get process elapsed time in minutes
get_elapsed_minutes() {
    local pid="$1"
    local etime
    etime=$(ps -o etime= -p "$pid" 2>/dev/null | xargs) || return 1
    # etime format: [[DD-]HH:]MM:SS
    local days=0 hours=0 mins=0 secs=0
    if [[ "$etime" == *-* ]]; then
        days="${etime%%-*}"
        etime="${etime#*-}"
    fi
    # Count colons
    local colons
    colons=$(echo "$etime" | tr -cd ':' | wc -c | tr -d ' ')
    if [[ "$colons" -eq 2 ]]; then
        hours="${etime%%:*}"
        etime="${etime#*:}"
    fi
    mins="${etime%%:*}"
    secs="${etime#*:}"
    # Remove leading zeros
    days=$((10#$days))
    hours=$((10#$hours))
    mins=$((10#$mins))
    echo $(( days * 24 * 60 + hours * 60 + mins ))
}

# Helper: Get human-readable elapsed time
get_elapsed_human() {
    local pid="$1"
    ps -o etime= -p "$pid" 2>/dev/null | xargs || echo "N/A"
}

# Helper: Get CPU usage for a process
get_cpu_usage() {
    local pid="$1"
    ps -o %cpu= -p "$pid" 2>/dev/null | xargs || echo "0.0"
}

# Helper: Check if a process has active network connections
has_network() {
    local pid="$1"
    # Check for any established TCP connections
    if lsof -Pan -p "$pid" -i 2>/dev/null | grep -q ESTABLISHED; then
        return 0
    fi
    return 1
}

# Helper: Get the current command running in a tmux pane
get_pane_command() {
    local session="$1"
    tmux display-message -t "$session" -p '#{pane_current_command}' 2>/dev/null || echo "unknown"
}

# Helper: Check if a process has any child processes
has_child_processes() {
    local pid="$1"
    pgrep -P "$pid" > /dev/null 2>&1
}

# Helper: Check if an agent is a script-based (non-Claude) agent
is_script_based_agent() {
    local session="$1"
    local agent_type
    agent_type=$(get_agent_type "$session")
    [[ "$agent_type" == "aristotle" || "$agent_type" == "tester" ]]
}

# Helper: Check whether Aristotle is currently in scale-to-zero state
# (issue #22471). Returns 0 (true) iff the marker file exists AND no
# aristotle-agent tmux session is currently running. The "no session"
# clause guards against stale markers from a previous shutdown that
# wasn't cleaned up — if a session is alive, treat it as authoritative.
is_aristotle_scaled_to_zero() {
    [[ -f "$ARISTOTLE_SCALED_MARKER" ]] || return 1
    tmux has-session -t "aristotle-agent" 2>/dev/null && return 1
    return 0
}

# Helper: Clear the Aristotle scale-to-zero marker. Called when the
# daemon decides to respawn aristotle (work appeared) or when an operator
# forces a manual spawn — either case represents a fresh "scale up".
clear_aristotle_scaled_marker() {
    rm -f "$ARISTOTLE_SCALED_MARKER" 2>/dev/null || true
}

# Helper: Check if an agent is a polling agent that legitimately idles between cycles
# Polling agents (deployer, seeker) sleep between work cycles, so low CPU + no network
# is normal behavior, not a stuck state.
is_polling_agent() {
    local session="$1"
    local agent_type
    agent_type=$(get_agent_type "$session")
    [[ "$agent_type" == "deployer" || "$agent_type" == "seeker" || "$agent_type" == "auditor" || "$agent_type" == "tester" || "$agent_type" == "herald" || "$agent_type" == "mechanic" ]]
}

# Helper: Get consecutive failure count from agent log
get_consecutive_failures() {
    local session="$1"
    local log_dir=".loom/logs"
    local log_file=""
    case "$session" in
        researcher-*) log_file="$log_dir/${session}.log" ;;
        enricher-*)   log_file="$log_dir/${session}.log" ;;
        deployer)     log_file="$log_dir/deployer.log" ;;
        seeker-agent) log_file="$log_dir/seeker.log" ;;
        auditor-agent) log_file="$log_dir/auditor.log" ;;
        herald-agent) log_file="$log_dir/herald.log" ;;
        mechanic-*) log_file="$log_dir/${session}.log" ;;
        aristotle-agent) log_file="$log_dir/aristotle.log" ;;
        tester-agent) log_file="$log_dir/tester-agent.log" ;;
        *) echo "0"; return ;;
    esac
    if [[ ! -f "$log_file" ]]; then echo "0"; return; fi

    # Only count failures from the current daemon run (after the last "Cycle 1 start")
    local last_restart_line
    last_restart_line=$(grep -n "Cycle 1 start" "$log_file" | tail -1 | cut -d: -f1)

    local count
    if [[ -n "$last_restart_line" ]]; then
        count=$(tail -n +"$last_restart_line" "$log_file" | grep -o "consecutive failures: [0-9]*" | tail -1 | grep -o '[0-9]*$')
    else
        count=$(grep -o "consecutive failures: [0-9]*" "$log_file" | tail -1 | grep -o '[0-9]*$')
    fi
    echo "${count:-0}"
}
CONSECUTIVE_FAILURE_THRESHOLD=10

# Helper: Determine agent health status
# Returns: RUNNING, COMPLETED, STUCK, IDLE, or UNKNOWN
get_agent_status() {
    local session="$1"
    local pane_pid
    pane_pid=$(get_pane_pid "$session")

    if [[ -z "$pane_pid" ]]; then
        echo "UNKNOWN"
        return
    fi

    # Check current command in pane
    local pane_cmd
    pane_cmd=$(get_pane_command "$session")

    # Script-based agents (e.g., Aristotle) don't use Claude.
    # Check if the shell has any child processes still running.
    if is_script_based_agent "$session"; then
        if [[ "$pane_cmd" == "zsh" || "$pane_cmd" == "bash" || "$pane_cmd" == "sh" ]]; then
            if has_child_processes "$pane_pid"; then
                echo "RUNNING"
            else
                echo "COMPLETED"
            fi
            return
        fi
        # pane_cmd is something other than a shell - script is actively executing
        echo "RUNNING"
        return
    fi

    # Claude-based agents: find claude child process
    local claude_pid
    claude_pid=$(find_claude_child "$pane_pid" | head -1)

    if [[ -z "$claude_pid" ]]; then
        # No claude process - check if shell is at prompt
        if [[ "$pane_cmd" == "zsh" || "$pane_cmd" == "bash" || "$pane_cmd" == "sh" ]]; then
            echo "COMPLETED"
            return
        fi
        echo "UNKNOWN"
        return
    fi

    # Claude process exists - check if it's stuck
    local elapsed_mins
    elapsed_mins=$(get_elapsed_minutes "$claude_pid" 2>/dev/null || echo "0")
    local cpu
    cpu=$(get_cpu_usage "$claude_pid")

    # Check for stuck: long runtime, near-zero CPU, no network
    if [[ "$elapsed_mins" -ge "$STUCK_THRESHOLD_MINUTES" ]]; then
        # Compare CPU with threshold (using awk for float comparison)
        local is_low_cpu
        is_low_cpu=$(awk "BEGIN { print ($cpu < $STUCK_CPU_THRESHOLD) ? 1 : 0 }")
        if [[ "$is_low_cpu" -eq 1 ]] && ! has_network "$claude_pid"; then
            # Polling agents (deployer, seeker) legitimately idle between cycles
            if is_polling_agent "$session"; then
                echo "IDLE"
            else
                echo "STUCK"
            fi
            return
        fi
    fi

    echo "RUNNING"
}

# Helper: Render red MISSING rows for configured agents with no live session (#39652).
# Compares the daemon's pool config (STATE_FILE .config) against live tmux
# sessions and prints a table row for each configured-but-absent agent. Sets
# the global MISSING_AGENTS_FOUND to the number of missing agents. Callable even
# when NO other agent sessions are live, so a configured agent that is the only
# thing that should be running (and isn't) is still surfaced.
MISSING_AGENTS_FOUND=0
print_missing_agent_rows() {
    MISSING_AGENTS_FOUND=0
    { [[ -f "$STATE_FILE" ]] && jq empty "$STATE_FILE" >/dev/null 2>&1; } || return 0

    local aristotle_scaled_local=0
    is_aristotle_scaled_to_zero && aristotle_scaled_local=1

    local htype hcfg hrun hcyc cyc_note
    for htype in enricher researcher aristotle auditor seeker deployer herald mechanic tester; do
        hcfg=$(jq -r ".config.${htype} // 0" "$STATE_FILE" 2>/dev/null || echo 0)
        [[ "$hcfg" =~ ^[0-9]+$ ]] || hcfg=0
        [[ "$hcfg" -ge 1 ]] || continue
        # Aristotle scale-to-zero (issue #22471) is an intentional absence.
        if [[ "$htype" == "aristotle" ]] && [[ "$aristotle_scaled_local" -eq 1 ]]; then
            continue
        fi
        hrun=$(count_agent_sessions "$htype")
        if [[ "$hrun" -lt "$hcfg" ]]; then
            MISSING_AGENTS_FOUND=$((MISSING_AGENTS_FOUND + 1))
            # Consecutive-cycle count recorded by the daemon, if available.
            hcyc=$(jq -r --arg t "$htype" \
                '(.missing_agents // []) | map(select(.type == $t)) | .[0].missing_cycles // empty' \
                "$STATE_FILE" 2>/dev/null || echo "")
            cyc_note=""
            [[ -n "$hcyc" ]] && cyc_note=" ${hcyc} cycles"
            printf "%-22s %-8s %-10s %-7s %-5s %-6s " "$htype" "-" "-" "-" "-" "-"
            echo -e "${RED}MISSING${NC} (configured:${hcfg} running:${hrun})${cyc_note}"
        fi
    done
}

# Command: health - Show agent process health
cmd_health() {
    echo -e "${BOLD}Agent Health Check${NC}"
    echo ""

    local sessions
    sessions=$(get_all_agent_sessions)

    if [[ -z "$sessions" ]]; then
        # No live sessions at all -- but configured agents may still be MISSING
        # (e.g. the whole pool died). Surface those before returning (#39652).
        print_missing_agent_rows
        if [[ "$MISSING_AGENTS_FOUND" -gt 0 ]]; then
            echo ""
            echo -e "Summary: ${RED}$MISSING_AGENTS_FOUND missing${NC} (configured agents with no live session)"
            echo ""
            echo -e "${YELLOW}Configured agent(s) have no live session. The launcher may be dying silently (#39649).${NC}"
            echo -e "${YELLOW}Check the daemon log ($DAEMON_LOG_FILE) and restart the daemon if needed.${NC}"
            return 0
        fi
        echo "No agent tmux sessions found."
        return 0
    fi

    # Print table header
    printf "%-22s %-8s %-10s %-7s %-5s %-6s %-10s\n" "Agent" "PID" "Elapsed" "CPU" "Net" "Fails" "Status"
    printf "%-22s %-8s %-10s %-7s %-5s %-6s %-10s\n" "-----" "---" "-------" "---" "---" "-----" "------"

    local stuck_count=0
    local running_count=0
    local completed_count=0
    local idle_count=0
    local failing_count=0

    while IFS= read -r session; do
        [[ -z "$session" ]] && continue

        local pane_pid
        pane_pid=$(get_pane_pid "$session")

        if [[ -z "$pane_pid" ]]; then
            printf "%-22s %-8s %-10s %-7s %-5s %-10s\n" "$session" "-" "-" "-" "-" "NO PANE"
            continue
        fi

        local status
        status=$(get_agent_status "$session")

        # Get consecutive failure count
        local failures
        failures=$(get_consecutive_failures "$session")
        local fail_display="$failures"
        if [[ "$failures" -ge "$CONSECUTIVE_FAILURE_THRESHOLD" ]]; then
            fail_display="${RED}${failures}${NC}"
        fi

        # Script-based agents (e.g., Aristotle): show pane process info
        if is_script_based_agent "$session"; then
            local status_display
            case "$status" in
                RUNNING)
                    status_display="${GREEN}RUNNING${NC}"
                    running_count=$((running_count + 1))
                    ;;
                COMPLETED)
                    if [[ "$failures" -ge "$CONSECUTIVE_FAILURE_THRESHOLD" ]]; then
                        status_display="${RED}FAILING${NC}"
                        failing_count=$((failing_count + 1))
                    else
                        status_display="${GREEN}COMPLETED${NC}"
                        completed_count=$((completed_count + 1))
                    fi
                    ;;
                *)
                    status_display="${YELLOW}$status${NC}"
                    ;;
            esac
            local elapsed_human
            elapsed_human=$(get_elapsed_human "$pane_pid")
            printf "%-22s %-8s %-10s %-7s %-5s %-6b " "$session" "$pane_pid" "$elapsed_human" "-" "-" "$fail_display"
            echo -e "$status_display (script)"
            continue
        fi

        # Claude-based agents: find claude child process
        local claude_pid
        claude_pid=$(find_claude_child "$pane_pid" | head -1)

        if [[ -z "$claude_pid" ]]; then
            # No claude process
            local status_display
            if [[ "$status" == "COMPLETED" ]]; then
                if [[ "$failures" -ge "$CONSECUTIVE_FAILURE_THRESHOLD" ]]; then
                    status_display="${RED}FAILING${NC}"
                    failing_count=$((failing_count + 1))
                else
                    status_display="${GREEN}COMPLETED${NC}"
                    completed_count=$((completed_count + 1))
                fi
            else
                status_display="${YELLOW}$status${NC}"
            fi
            printf "%-22s %-8s %-10s %-7s %-5s %-6b " "$session" "-" "-" "-" "-" "$fail_display"
            echo -e "$status_display"
        else
            local elapsed_human
            elapsed_human=$(get_elapsed_human "$claude_pid")
            local cpu
            cpu=$(get_cpu_usage "$claude_pid")
            local net_status="none"
            if has_network "$claude_pid"; then
                net_status="yes"
            fi

            local status_display
            case "$status" in
                STUCK)
                    status_display="${RED}STUCK${NC}"
                    stuck_count=$((stuck_count + 1))
                    ;;
                IDLE)
                    if [[ "$failures" -ge "$CONSECUTIVE_FAILURE_THRESHOLD" ]]; then
                        status_display="${RED}FAILING${NC}"
                        failing_count=$((failing_count + 1))
                    else
                        status_display="${BLUE}IDLE${NC}"
                        idle_count=$((idle_count + 1))
                    fi
                    ;;
                RUNNING)
                    status_display="${GREEN}RUNNING${NC}"
                    running_count=$((running_count + 1))
                    ;;
                *)
                    status_display="${YELLOW}$status${NC}"
                    ;;
            esac

            printf "%-22s %-8s %-10s %-7s %-5s %-6b " "$session" "$claude_pid" "$elapsed_human" "${cpu}%" "$net_status" "$fail_display"
            echo -e "$status_display"
        fi
    done <<< "$sessions"

    # Surface Aristotle scale-to-zero (issue #22471) even though no tmux
    # session exists for it — get_all_agent_sessions only enumerates live
    # sessions, so we render an extra row when the marker is present.
    local aristotle_scaled=0
    if is_aristotle_scaled_to_zero; then
        aristotle_scaled=1
        printf "%-22s %-8s %-10s %-7s %-5s %-6s " "aristotle-agent" "-" "-" "-" "-" "-"
        echo -e "${YELLOW}SCALED_TO_ZERO${NC} (idle queue)"
    fi

    # Surface CONFIGURED agents that have no live session (#39652). Previously
    # health simply omitted them (get_all_agent_sessions only enumerates live
    # sessions), which let the deployer stay dead for 7 days unnoticed.
    print_missing_agent_rows
    local missing_count=$MISSING_AGENTS_FOUND

    echo ""
    local summary="Summary: ${GREEN}$running_count running${NC}, ${completed_count} completed"
    if [[ $idle_count -gt 0 ]]; then
        summary+=", ${BLUE}$idle_count idle${NC}"
    fi
    if [[ $aristotle_scaled -gt 0 ]]; then
        summary+=", ${YELLOW}1 scaled-to-zero${NC}"
    fi
    if [[ $failing_count -gt 0 ]]; then
        summary+=", ${RED}$failing_count failing${NC}"
    fi
    if [[ $missing_count -gt 0 ]]; then
        summary+=", ${RED}$missing_count missing${NC}"
    fi
    summary+=", ${RED}$stuck_count stuck${NC}"
    echo -e "$summary"

    if [[ $stuck_count -gt 0 ]]; then
        echo ""
        echo -e "${YELLOW}Stuck agents detected. Use './scripts/lean/launch.sh stop --force' to kill them.${NC}"
    fi
    if [[ $failing_count -gt 0 ]]; then
        echo ""
        echo -e "${YELLOW}Failing agents detected (${CONSECUTIVE_FAILURE_THRESHOLD}+ consecutive failures). Check logs and restart.${NC}"
    fi
    if [[ $missing_count -gt 0 ]]; then
        echo ""
        echo -e "${YELLOW}Configured agent(s) have no live session. The launcher may be dying silently (#39649).${NC}"
        echo -e "${YELLOW}Check the daemon log ($DAEMON_LOG_FILE) and restart the daemon if needed.${NC}"
    fi

    return $stuck_count
}

# Helper: Check for stuck agents and print warnings
# Returns: number of stuck agents
check_for_stuck_agents() {
    local sessions
    sessions=$(get_all_agent_sessions)

    if [[ -z "$sessions" ]]; then
        return 0
    fi

    local stuck_count=0
    local stuck_names=()

    while IFS= read -r session; do
        [[ -z "$session" ]] && continue
        local status
        status=$(get_agent_status "$session")
        if [[ "$status" == "STUCK" ]]; then
            stuck_count=$((stuck_count + 1))
            stuck_names+=("$session")
        fi
    done <<< "$sessions"

    if [[ $stuck_count -gt 0 ]]; then
        echo ""
        echo -e "${YELLOW}WARNING: Detected $stuck_count stuck agent(s) that may not respond to graceful shutdown:${NC}"
        for name in "${stuck_names[@]}"; do
            echo -e "  ${YELLOW}- $name${NC}"
        done
        echo ""
        echo -e "${YELLOW}Stuck agents have 0% CPU and no network activity for >$STUCK_THRESHOLD_MINUTES minutes.${NC}"
        echo -e "${YELLOW}They will not check signal files. Use '--force' to kill them:${NC}"
        echo -e "  ${BOLD}./scripts/lean/launch.sh stop --force${NC}"
        echo ""
    fi

    return $stuck_count
}

# =============================================================================
# Daemon: Continuous monitoring loop with agent respawning
# =============================================================================

# Associative array for tracking last respawn time per session (bash 4+)
# Fallback to flat variables for bash 3 (macOS default)
declare -A LAST_RESPAWN_TIME 2>/dev/null || true

# Helper: Get last respawn epoch for a session
get_last_respawn() {
    local session="$1"
    if declare -p LAST_RESPAWN_TIME &>/dev/null 2>&1; then
        echo "${LAST_RESPAWN_TIME[$session]:-0}"
    else
        # Fallback for bash 3: use a temp file
        local cache_file="/tmp/lean-daemon-respawn-${session}"
        if [[ -f "$cache_file" ]]; then
            cat "$cache_file"
        else
            echo "0"
        fi
    fi
}

# Helper: Set last respawn epoch for a session
set_last_respawn() {
    local session="$1"
    local epoch="$2"
    if declare -p LAST_RESPAWN_TIME &>/dev/null 2>&1; then
        LAST_RESPAWN_TIME[$session]="$epoch"
    else
        echo "$epoch" > "/tmp/lean-daemon-respawn-${session}"
    fi
}

# Consecutive-cycles-missing counter per agent type (#39652). Same bash 4+
# associative array with a bash 3 /tmp fallback as LAST_RESPAWN_TIME above.
declare -A MISSING_CYCLE_COUNT 2>/dev/null || true

# Helper: Get consecutive-missing cycle count for an agent type
get_missing_cycles() {
    local type="$1"
    if declare -p MISSING_CYCLE_COUNT &>/dev/null 2>&1; then
        echo "${MISSING_CYCLE_COUNT[$type]:-0}"
    else
        local cache_file="/tmp/lean-daemon-missing-${type}"
        if [[ -f "$cache_file" ]]; then cat "$cache_file"; else echo "0"; fi
    fi
}

# Helper: Set consecutive-missing cycle count for an agent type
set_missing_cycles() {
    local type="$1"
    local count="$2"
    if declare -p MISSING_CYCLE_COUNT &>/dev/null 2>&1; then
        MISSING_CYCLE_COUNT[$type]="$count"
    else
        echo "$count" > "/tmp/lean-daemon-missing-${type}"
    fi
}

# Helper: Count live tmux sessions for an agent type (#39652).
# Used by both the daemon detection loop and `cmd_health` so the two agree on
# what "running" means for each agent family.
count_agent_sessions() {
    local type="$1"
    local count=0
    local i
    case "$type" in
        enricher)
            for i in $(seq 1 "$MAX_ENRICHER"); do
                tmux has-session -t "enricher-$i" 2>/dev/null && count=$((count + 1))
            done ;;
        researcher)
            for i in $(seq 1 "$MAX_RESEARCHER"); do
                tmux has-session -t "researcher-$i" 2>/dev/null && count=$((count + 1))
            done ;;
        mechanic)
            for i in 1 2 3; do
                tmux has-session -t "mechanic-$i" 2>/dev/null && count=$((count + 1))
            done
            tmux has-session -t "mechanic-agent" 2>/dev/null && count=$((count + 1)) ;;
        aristotle) tmux has-session -t "aristotle-agent" 2>/dev/null && count=1 ;;
        auditor)   tmux has-session -t "auditor-agent" 2>/dev/null && count=1 ;;
        seeker)    tmux has-session -t "seeker-agent" 2>/dev/null && count=1 ;;
        deployer)  tmux has-session -t "deployer" 2>/dev/null && count=1 ;;
        herald)    tmux has-session -t "herald-agent" 2>/dev/null && count=1 ;;
        tester)    tmux has-session -t "tester-agent" 2>/dev/null && count=1 ;;
    esac
    echo "$count"
}

# Helper: Persist the set of persistently-missing agents to STATE_FILE (#39652).
# Consumed by `cmd_health` / `status.sh` so the absence stays visible between
# daemon cycles and after the daemon exits. Argument is a compact JSON array of
# {type, configured, running, missing_cycles} objects (may be "[]").
write_missing_agents() {
    local missing_json="$1"
    [[ -f "$STATE_FILE" ]] || return 0
    jq empty "$STATE_FILE" >/dev/null 2>&1 || return 0
    local tmp
    tmp=$(mktemp)
    if jq --argjson missing "$missing_json" \
          '.missing_agents = $missing' \
          "$STATE_FILE" > "$tmp" 2>/dev/null; then
        mv "$tmp" "$STATE_FILE"
    else
        rm -f "$tmp"
    fi
}

# Helper: Persistent-missing-session detection & alerting (#39652, #41509).
# Tracks how many CONSECUTIVE cycles each CONFIGURED agent has stayed below
# target; once the count crosses MISSING_SESSION_ALERT_CYCLES it escalates to a
# WARN and persists a MISSING record (via write_missing_agents) that
# /lean health & /lean status render as a red row instead of silently omitting
# the agent. Live counts come from count_agent_sessions so this is a single
# source of truth and can run in BOTH the normal daemon cycle AND the total-pool
# blackout path where get_all_agent_sessions is empty (#41509 -- otherwise the
# blackout early-continues before detection and /lean status stays empty).
# Args, in order:
#   enricher researcher aristotle auditor seeker deployer herald mechanic tester
detect_and_persist_missing_agents() {
    local enricher="$1" researcher="$2" aristotle="$3" auditor="$4" \
          seeker="$5" deployer="$6" herald="$7" mechanic="$8" tester="$9"
    local missing_json="[]"
    local mtype mtarget mactive mcycles
    for _pair in \
        "enricher $enricher" \
        "researcher $researcher" \
        "aristotle $aristotle" \
        "auditor $auditor" \
        "seeker $seeker" \
        "deployer $deployer" \
        "herald $herald" \
        "mechanic $mechanic" \
        "tester $tester"; do
        read -r mtype mtarget <<< "$_pair"

        # Only configured agents (target >= 1) can be "missing".
        if [[ "$mtarget" -lt 1 ]]; then
            set_missing_cycles "$mtype" 0
            continue
        fi

        # Aristotle scale-to-zero (issue #22471) is an intentional absence,
        # not a failed launch -- don't false-alarm on it.
        if [[ "$mtype" == "aristotle" ]] && [[ -f "$ARISTOTLE_SCALED_MARKER" ]]; then
            set_missing_cycles "$mtype" 0
            continue
        fi

        mactive=$(count_agent_sessions "$mtype")
        if [[ "$mactive" -lt "$mtarget" ]]; then
            mcycles=$(get_missing_cycles "$mtype")
            mcycles=$((mcycles + 1))
            set_missing_cycles "$mtype" "$mcycles"
            if [[ "$mcycles" -ge "$MISSING_SESSION_ALERT_CYCLES" ]]; then
                daemon_log "WARN" "Agent '$mtype' MISSING: configured=$mtarget running=$mactive for $mcycles consecutive cycles (respawn attempted, session still absent)"
                missing_json=$(echo "$missing_json" | jq -c \
                    --arg t "$mtype" --argjson cfg "$mtarget" \
                    --argjson run "$mactive" --argjson cyc "$mcycles" \
                    '. += [{type: $t, configured: $cfg, running: $run, missing_cycles: $cyc}]' \
                    2>/dev/null || echo "$missing_json")
            fi
        else
            set_missing_cycles "$mtype" 0
        fi
    done
    write_missing_agents "$missing_json"
}

# Helper: Daemon log with timestamp
daemon_log() {
    local level="$1"
    shift
    local msg="$*"
    local timestamp
    timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    echo "[$timestamp] $level: $msg"
}

guard_git_auto_gc() {
    git config gc.auto 0 2>/dev/null || daemon_log "WARN" "Could not set git gc.auto=0"
    git config maintenance.auto false 2>/dev/null || daemon_log "WARN" "Could not set git maintenance.auto=false"

    local stale_pids
    stale_pids=$(pgrep -f 'git (pack-objects.*--cruft|repack.*--cruft)' 2>/dev/null || true)
    [[ -z "$stale_pids" ]] && return 0

    local stale_count
    stale_count=$(echo "$stale_pids" | wc -l | tr -d ' ')
    if [[ "$stale_count" -gt 5 ]]; then
        daemon_log "WARN" "Found $stale_count stale git cruft repack process(es), killing"
        echo "$stale_pids" | xargs kill 2>/dev/null || true
    fi
}

# Helper: Apply time-based schedule overrides to pool targets
# Reads .loom/lean-schedule.json and adjusts pool variables based on current time
apply_schedule() {
    [[ ! -f "$SCHEDULE_FILE" ]] && return 0

    local enabled
    enabled=$(jq -r '.enabled // false' "$SCHEDULE_FILE" 2>/dev/null) || return 0
    [[ "$enabled" != "true" ]] && return 0

    local tz
    tz=$(jq -r '.timezone // "America/Los_Angeles"' "$SCHEDULE_FILE" 2>/dev/null)

    local current_time current_minutes
    current_time=$(TZ="$tz" date +%H:%M)
    current_minutes=$(( 10#$(echo "$current_time" | cut -d: -f1) * 60 + 10#$(echo "$current_time" | cut -d: -f2) ))

    # Find matching window
    local window_count matched_window=""
    window_count=$(jq '.windows | length' "$SCHEDULE_FILE" 2>/dev/null) || return 0

    for ((i=0; i<window_count; i++)); do
        local hours_range
        hours_range=$(jq -r ".windows[$i].hours // \"\"" "$SCHEDULE_FILE" 2>/dev/null)
        [[ -z "$hours_range" ]] && continue

        local start_str end_str
        start_str=$(echo "$hours_range" | cut -d- -f1)
        end_str=$(echo "$hours_range" | cut -d- -f2)

        local start_minutes end_minutes
        start_minutes=$(( 10#$(echo "$start_str" | cut -d: -f1) * 60 + 10#$(echo "$start_str" | cut -d: -f2) ))
        end_minutes=$(( 10#$(echo "$end_str" | cut -d: -f1) * 60 + 10#$(echo "$end_str" | cut -d: -f2) ))

        local in_window=false
        if [[ $start_minutes -le $end_minutes ]]; then
            # Normal range (e.g., 05:00-11:00)
            [[ $current_minutes -ge $start_minutes && $current_minutes -lt $end_minutes ]] && in_window=true
        else
            # Overnight range (e.g., 23:00-05:00)
            [[ $current_minutes -ge $start_minutes || $current_minutes -lt $end_minutes ]] && in_window=true
        fi

        if [[ "$in_window" == "true" ]]; then
            matched_window="$i"
            break
        fi
    done

    # Fall back to default window if no match
    if [[ -z "$matched_window" ]]; then
        for ((i=0; i<window_count; i++)); do
            local is_default
            is_default=$(jq -r ".windows[$i].default // false" "$SCHEDULE_FILE" 2>/dev/null)
            if [[ "$is_default" == "true" ]]; then
                matched_window="$i"
                break
            fi
        done
    fi

    [[ -z "$matched_window" ]] && return 0

    local window_name
    window_name=$(jq -r ".windows[$matched_window].name // \"unknown\"" "$SCHEDULE_FILE" 2>/dev/null)

    # Apply pool overrides (only for keys present in the window's pools)
    local pools
    pools=$(jq -c ".windows[$matched_window].pools // {}" "$SCHEDULE_FILE" 2>/dev/null)

    local new_val
    new_val=$(echo "$pools" | jq -r '.researcher // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && researcher=$(( new_val > MAX_RESEARCHER ? MAX_RESEARCHER : new_val ))

    new_val=$(echo "$pools" | jq -r '.enricher // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && enricher=$(( new_val > MAX_ENRICHER ? MAX_ENRICHER : new_val ))

    new_val=$(echo "$pools" | jq -r '.aristotle // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && aristotle=$(( new_val > MAX_ARISTOTLE ? MAX_ARISTOTLE : new_val ))

    new_val=$(echo "$pools" | jq -r '.seeker // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && seeker=$(( new_val > MAX_SEEKER ? MAX_SEEKER : new_val ))

    new_val=$(echo "$pools" | jq -r '.auditor // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && auditor=$(( new_val > MAX_AUDITOR ? MAX_AUDITOR : new_val ))

    new_val=$(echo "$pools" | jq -r '.deployer // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && deployer=$(( new_val > MAX_DEPLOYER ? MAX_DEPLOYER : new_val ))

    new_val=$(echo "$pools" | jq -r '.tester // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && tester=$(( new_val > MAX_TESTER ? MAX_TESTER : new_val ))

    new_val=$(echo "$pools" | jq -r '.herald // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && herald=$(( new_val > MAX_HERALD ? MAX_HERALD : new_val ))

    new_val=$(echo "$pools" | jq -r '.mechanic // empty' 2>/dev/null)
    [[ -n "$new_val" ]] && mechanic=$(( new_val > MAX_MECHANIC ? MAX_MECHANIC : new_val ))

    daemon_log "INFO" "Schedule: window=$window_name (${current_time} ${tz}), targets: enricher=$enricher, researcher=$researcher, aristotle=$aristotle"

    # Update state file config to reflect scheduled values
    if [[ -f "$STATE_FILE" ]]; then
        local tmp
        tmp=$(mktemp)
        jq \
            --argjson enricher "$enricher" \
            --argjson aristotle "$aristotle" \
            --argjson researcher "$researcher" \
            --argjson seeker "$seeker" \
            --argjson deployer "$deployer" \
            --arg schedule_window "$window_name" \
            --arg schedule_time "$current_time" \
            '.config.enricher = $enricher |
             .config.aristotle = $aristotle |
             .config.researcher = $researcher |
             .config.seeker = $seeker |
             .config.deployer = $deployer |
             .schedule_window = $schedule_window |
             .schedule_time = $schedule_time' \
            "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
    fi
}

# Helper: Determine agent type from session name
get_agent_type() {
    local session="$1"
    case "$session" in
        enricher-*) echo "enricher" ;;
        aristotle-agent)  echo "aristotle" ;;
        researcher-*)     echo "researcher" ;;
        seeker-agent)     echo "seeker" ;;
        auditor-agent)    echo "auditor" ;;
        deployer)         echo "deployer" ;;
        tester-agent)     echo "tester" ;;
        herald-agent)     echo "herald" ;;
        mechanic-*)       echo "mechanic" ;;
        *)                echo "unknown" ;;
    esac
}

# Helper: Respawn a single agent by session name
# Kills the old tmux session and spawns a fresh agent in its slot
# Runs in a subshell to prevent errors from killing the daemon (set -e)
respawn_agent() {
    local session="$1"
    local agent_type
    agent_type=$(get_agent_type "$session")

    daemon_log "INFO" "Respawning $agent_type agent (session: $session)"

    # Run the actual respawn in a subshell so git/tmux errors don't
    # propagate to the daemon loop via set -e
    ( _do_respawn_agent "$session" "$agent_type" )
    local rc=$?
    if [[ $rc -ne 0 ]]; then
        daemon_log "WARN" "Respawn of $session failed (exit code $rc), will retry next cycle"
        return 1
    fi
    set_last_respawn "$session" "$(date +%s)"
    return 0
}

# Internal: actual respawn logic (runs in subshell for error isolation)
_do_respawn_agent() {
    local session="$1"
    local agent_type="$2"

    # Kill old session and its processes
    kill_session_processes "$session"

    case "$agent_type" in
        enricher)
            # Spawn a specific enricher slot directly (parallel-enrich.sh refuses
            # to start if any enricher is already running, so we inline the logic)
            local agent_num="${session##*-}"
            local repo_root
            repo_root=$(pwd)
            # Resolved worktree base (LOOM_WORKTREE_ROOT / worktree.root
            # override; default $repo_root/.loom/worktrees).
            local wt_base
            wt_base="$(loom_worktree_root "$repo_root")"
            mkdir -p "$wt_base"
            local base_dir="$wt_base/enricher-$agent_num"
            local base_branch="feature/enricher-$agent_num"
            local worktree_dir="$base_dir"
            local branch="$base_branch"
            local enricher_id="enricher-$agent_num"
            local log_file=".loom/logs/$session.log"
            local prompt_file=".loom/logs/$session-prompt.md"

            # Reclaim any existing worktree at the primary path using the shared
            # safety guards instead of an unconditional force-delete.
            # `remove_own_worktree` returns 0 whether it removed OR preserved the
            # worktree, so re-test the directory afterwards to distinguish.
            if [[ -d "$worktree_dir" ]]; then
                remove_own_worktree "$worktree_dir"
            fi
            # If a guard preserved in-flight work, allocate a fresh,
            # non-colliding path/branch rather than discarding it.
            if [[ -d "$worktree_dir" ]]; then
                daemon_log "WARN" "Worktree $worktree_dir preserved (in-flight work); allocating fresh path"
                local suffix=2
                while [[ -d "$base_dir-$suffix" ]]; do
                    remove_own_worktree "$base_dir-$suffix"
                    [[ -d "$base_dir-$suffix" ]] || break
                    suffix=$((suffix + 1))
                done
                worktree_dir="$base_dir-$suffix"
                branch="$base_branch-$suffix"
            fi
            # Delete the target branch only when safe (`-d` refuses to drop a
            # branch with unmerged/unpushed commits or one still checked out).
            if git show-ref --verify --quiet "refs/heads/$branch" \
                && ! git branch -d "$branch" >/dev/null 2>&1; then
                daemon_log "WARN" "Branch $branch has unpushed work; allocating fresh branch"
                local bsuffix=2
                while git show-ref --verify --quiet "refs/heads/${base_branch}-$bsuffix"; do
                    bsuffix=$((bsuffix + 1))
                done
                branch="${base_branch}-$bsuffix"
            fi
            git worktree add "$worktree_dir" -b "$branch" main 2>/dev/null || {
                daemon_log "WARN" "Cannot create worktree for $session"
                return
            }
            if [[ -f "$worktree_dir/.gitmodules" ]]; then
                (cd "$worktree_dir" && git submodule update --init --recursive 2>/dev/null) || true
            fi

            # Create tmux session and launch Claude
            tmux new-session -d -s "$session" -c "$worktree_dir"
            sleep 0.3
            tmux send-keys -t "$session" "export ENRICHER_ID='$enricher_id'" Enter
            sleep 0.2
            tmux send-keys -t "$session" "export REPO_ROOT='$repo_root'" Enter
            sleep 0.2
            # Honour ENRICHER_CLAUDE_MODEL (per-role) > CLAUDE_MODEL (global),
            # mirroring initial-start in parallel-enrich.sh
            local enricher_model="${ENRICHER_CLAUDE_MODEL:-${CLAUDE_MODEL:-claude-opus-4-8}}"
            tmux send-keys -t "$session" "export CLAUDE_MODEL='$enricher_model'" Enter
            sleep 0.2
            local prompt="You are $enricher_id. Read $repo_root/$prompt_file for your instructions, then start the enrichment workflow."
            local wrapper_script="$repo_root/scripts/agents/claude-wrapper.sh"
            tmux send-keys -t "$session" "$wrapper_script --prompt '$prompt' --log '$repo_root/$log_file' --max-retries 5" Enter
            sleep 1
            daemon_log "INFO" "Enricher $agent_num respawned (session: $session)"
            ;;
        aristotle)
            if check_script "./scripts/aristotle/launch-agent.sh" 2>/dev/null; then
                ./scripts/aristotle/launch-agent.sh &
                sleep 1
                daemon_log "INFO" "Aristotle agent respawned"
            else
                daemon_log "WARN" "Cannot respawn aristotle: script not found"
            fi
            ;;
        researcher)
            # Respawn the specific researcher slot (mirrors enricher respawn pattern)
            local agent_num="${session##*-}"
            local repo_root
            repo_root=$(pwd)
            # Resolved worktree base (LOOM_WORKTREE_ROOT / worktree.root
            # override; default $repo_root/.loom/worktrees).
            local wt_base
            wt_base="$(loom_worktree_root "$repo_root")"
            mkdir -p "$wt_base"
            local base_dir="$wt_base/researcher-$agent_num"
            local base_branch="feature/researcher-$agent_num"
            local worktree_dir="$base_dir"
            local branch="$base_branch"
            local log_file=".loom/logs/$session.log"
            local prompt_file=".loom/logs/$session-prompt.md"

            # Reclaim any existing worktree at the primary path using the shared
            # safety guards instead of an unconditional force-delete.
            # `remove_own_worktree` returns 0 whether it removed OR preserved the
            # worktree, so re-test the directory afterwards to distinguish.
            if [[ -d "$worktree_dir" ]]; then
                remove_own_worktree "$worktree_dir"
            fi
            # If a guard preserved in-flight work, allocate a fresh,
            # non-colliding path/branch rather than discarding it.
            if [[ -d "$worktree_dir" ]]; then
                daemon_log "WARN" "Worktree $worktree_dir preserved (in-flight work); allocating fresh path"
                local suffix=2
                while [[ -d "$base_dir-$suffix" ]]; do
                    remove_own_worktree "$base_dir-$suffix"
                    [[ -d "$base_dir-$suffix" ]] || break
                    suffix=$((suffix + 1))
                done
                worktree_dir="$base_dir-$suffix"
                branch="$base_branch-$suffix"
            fi
            # Delete the target branch only when safe (`-d` refuses to drop a
            # branch with unmerged/unpushed commits or one still checked out).
            if git show-ref --verify --quiet "refs/heads/$branch" \
                && ! git branch -d "$branch" >/dev/null 2>&1; then
                daemon_log "WARN" "Branch $branch has unpushed work; allocating fresh branch"
                local bsuffix=2
                while git show-ref --verify --quiet "refs/heads/${base_branch}-$bsuffix"; do
                    bsuffix=$((bsuffix + 1))
                done
                branch="${base_branch}-$bsuffix"
            fi
            git worktree add "$worktree_dir" -b "$branch" main 2>/dev/null || {
                daemon_log "WARN" "Cannot create worktree for $session"
                return
            }
            if [[ -f "$worktree_dir/.gitmodules" ]]; then
                (cd "$worktree_dir" && git submodule update --init --recursive 2>/dev/null) || true
            fi

            # Symlink .lake for fast Lean builds
            if [[ -d "$repo_root/proofs/.lake" ]] && [[ -d "$worktree_dir/proofs" ]]; then
                rm -rf "$worktree_dir/proofs/.lake" 2>/dev/null || true
                ln -s "$repo_root/proofs/.lake" "$worktree_dir/proofs/.lake"
            fi

            # Create tmux session and launch Claude
            tmux new-session -d -s "$session" -c "$worktree_dir"
            sleep 0.3
            tmux send-keys -t "$session" "export ENHANCER_ID='researcher-$agent_num'" Enter
            sleep 0.2
            tmux send-keys -t "$session" "export REPO_ROOT='$repo_root'" Enter
            sleep 0.2
            tmux send-keys -t "$session" "export CLAUDE_TIMEOUT=14400" Enter
            sleep 0.2
            # Model resolution chain (mirroring initial-start in parallel-research.sh):
            #   1. RESEARCHER_${slot}_CLAUDE_MODEL  — per-slot pin survives respawn
            #   2. RESEARCHER_CLAUDE_MODEL          — per-role override (whole pool)
            #   3. CLAUDE_MODEL                      — global override
            #   4. claude-opus-4-8                   — wrapper default
            # The per-slot pin only works if the daemon's own shell env has it
            # exported; otherwise the respawn falls through to the pool default.
            local slot_model_var="RESEARCHER_${agent_num}_CLAUDE_MODEL"
            local researcher_model="${!slot_model_var:-${RESEARCHER_CLAUDE_MODEL:-${CLAUDE_MODEL:-claude-opus-4-8}}}"
            tmux send-keys -t "$session" "export CLAUDE_MODEL='$researcher_model'" Enter
            sleep 0.2
            local prompt="You are researcher-$agent_num. Read $repo_root/$prompt_file for your instructions, then start the research workflow."
            local wrapper_script="$repo_root/scripts/agents/claude-wrapper.sh"
            tmux send-keys -t "$session" "$wrapper_script --daemon --prompt '$prompt' --log '$repo_root/$log_file'" Enter
            sleep 1
            daemon_log "INFO" "Researcher $agent_num respawned (session: $session)"
            ;;
        seeker)
            if check_script "./scripts/research/launch-seeker.sh" 2>/dev/null; then
                ./scripts/research/launch-seeker.sh &
                sleep 1
                daemon_log "INFO" "Seeker agent respawned"
            else
                daemon_log "WARN" "Cannot respawn seeker: script not found"
            fi
            ;;
        auditor)
            if check_script "./scripts/auditor/launch-agent.sh" 2>/dev/null; then
                ./scripts/auditor/launch-agent.sh &
                sleep 1
                daemon_log "INFO" "Auditor agent respawned"
            else
                daemon_log "WARN" "Cannot respawn auditor: script not found"
            fi
            ;;
        deployer)
            if check_script "./scripts/deploy/launch-agent.sh" 2>/dev/null; then
                ./scripts/deploy/launch-agent.sh &
                sleep 1
                daemon_log "INFO" "Deployer respawned"
            else
                daemon_log "WARN" "Cannot respawn deployer: script not found"
            fi
            ;;
        tester)
            if check_script "./scripts/test/launch-agent.sh" 2>/dev/null; then
                ./scripts/test/launch-agent.sh &
                sleep 1
                daemon_log "INFO" "Tester agent respawned"
            else
                daemon_log "WARN" "Cannot respawn tester: script not found"
            fi
            ;;
        herald)
            if check_script "./scripts/herald/launch-agent.sh" 2>/dev/null; then
                ./scripts/herald/launch-agent.sh &
                sleep 1
                daemon_log "INFO" "Herald agent respawned"
            else
                daemon_log "WARN" "Cannot respawn herald: script not found"
            fi
            ;;
        mechanic)
            if check_script "./scripts/mechanic/launch-agent.sh" 2>/dev/null; then
                SESSION_NAME="$session" ./scripts/mechanic/launch-agent.sh &
                sleep 1
                daemon_log "INFO" "Mechanic agent respawned (session: $session)"
            else
                daemon_log "WARN" "Cannot respawn mechanic: script not found"
            fi
            ;;
        *)
            daemon_log "WARN" "Unknown agent type for session: $session"
            ;;
    esac
}

# Helper: Kill a stuck agent and respawn it
kill_and_respawn() {
    local session="$1"
    daemon_log "WARN" "Force-killing stuck session: $session"
    kill_session_processes "$session"
    respawn_agent "$session" || daemon_log "WARN" "Failed to respawn $session after kill (will retry next cycle)"
}

# Helper: Check if respawn cooldown has elapsed for a session
is_cooldown_elapsed() {
    local session="$1"
    local now
    now=$(date +%s)
    local last
    last=$(get_last_respawn "$session")
    local elapsed=$((now - last))
    if [[ $elapsed -ge $RESPAWN_COOLDOWN_SECONDS ]]; then
        return 0
    else
        return 1
    fi
}

# Helper: Get work queue stats (with timeout protection)
get_work_queue_stats() {
    local enrichment_targets="?"
    local candidates="0"
    local aristotle_jobs="0"
    local ready_prs="0"

    # Enrichment targets count (with 10s timeout)
    if command -v npx &>/dev/null && [[ -f "scripts/enricher/find-targets.ts" ]]; then
        enrichment_targets=$(timeout 10 npx tsx scripts/enricher/find-targets.ts --stats 2>/dev/null | grep -oE "Entries needing enrichment: +[0-9]+" | grep -oE "[0-9]+" || echo "?")
    fi

    # Research candidates
    if [[ -f ".lean/state/candidate-pool.json" ]]; then
        candidates=$(jq '[.candidates[] | select(.status == "available")] | length' ".lean/state/candidate-pool.json" 2>/dev/null || echo "0")
    fi

    # Aristotle jobs
    if [[ -f "research/aristotle-jobs.json" ]]; then
        aristotle_jobs=$(jq '[.jobs[] | select(.status == "submitted")] | length' "research/aristotle-jobs.json" 2>/dev/null || echo "0")
    fi

    # Aristotle candidates (files with sorries eligible for submission)
    local aristotle_candidates="0"
    if [[ -x "scripts/aristotle/find-candidates.sh" ]]; then
        aristotle_candidates=$(timeout 10 ./scripts/aristotle/find-candidates.sh --count 2>/dev/null || echo "0")
    fi

    # PRs in the deployer's real merge queue (#39651).
    # Counting only `loom:pr` masked a 537-PR backlog during the #39649 deployer
    # outage: math agents (Researcher/Enricher/Aristotle/Auditor) do NOT label
    # their PRs `loom:pr` — the deployer merges them by their content labels
    # (enrichment/research/loom:auditor/aristotle-integration) directly. Count
    # every OPEN PR carrying any deployer-merged label (math labels + loom:pr) so
    # a stalled deployer surfaces as a large number here, not 0. One API call,
    # OR-filtered in jq; `timeout 10` + `|| echo 0` keep a slow/failing gh safe.
    ready_prs=$(timeout 10 gh pr list --state open --limit 1000 --json labels 2>/dev/null \
        | jq '[.[] | select(any(.labels[].name;
              . == "loom:pr" or . == "enrichment" or . == "research"
              or . == "loom:auditor" or . == "aristotle-integration"))] | length' 2>/dev/null \
        || echo "0")

    echo "$enrichment_targets $candidates $aristotle_jobs $aristotle_candidates $ready_prs"
}

# Helper: Write daemon state to state file
# Helper: Derive the daemon process start time as an ISO-8601 UTC timestamp.
# Uses the running daemon PID (arg > $DAEMON_PID_FILE > $$) so a recreated
# STATE_FILE reflects the ACTUAL uptime rather than a false 0 from `date` now.
# Handles both macOS/BSD (`ps -o lstart=`, `date -j`) and GNU date (Linux).
daemon_start_time_iso() {
    local pid="${1:-}"
    if [[ -z "$pid" && -f "$DAEMON_PID_FILE" ]]; then
        pid=$(cat "$DAEMON_PID_FILE" 2>/dev/null || echo "")
    fi
    [[ -z "$pid" ]] && pid=$$

    local lstart epoch iso
    # `ps -o lstart=` prints local-time wall clock, e.g. "Mon Jul 21 08:15:30 2026"
    lstart=$(ps -o lstart= -p "$pid" 2>/dev/null | sed 's/^[[:space:]]*//;s/[[:space:]]*$//')
    if [[ -n "$lstart" ]]; then
        # BSD/macOS: parse local-time string -> epoch, then format as UTC.
        epoch=$(date -j -f "%a %b %e %H:%M:%S %Y" "$lstart" +%s 2>/dev/null)
        if [[ -n "$epoch" ]]; then
            iso=$(date -u -r "$epoch" +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null)
        else
            # GNU date fallback (Linux)
            iso=$(date -u -d "$lstart" +"%Y-%m-%dT%H:%M:%SZ" 2>/dev/null)
        fi
        if [[ -n "$iso" ]]; then
            echo "$iso"
            return 0
        fi
    fi
    # Last resort: now (better a fresh uptime than a bogus multi-day one).
    date -u +"%Y-%m-%dT%H:%M:%SZ"
}

# Helper: Recreate a missing/corrupt daemon STATE_FILE in place (#41048).
# The state file lives under .loom/ (Loom-managed); a Loom reinstall's uninstall
# phase can delete it, after which update_daemon_state() would no-op forever and
# `/lean status` would report a bogus multi-day uptime with zeroed stats. This
# rebuilds the same schema init_state() writes, deriving started_at from the real
# daemon process start time and preserving pool config from the daemon's live
# in-memory args (exposed as DAEMON_CONFIG_* globals by cmd_daemon).
recreate_daemon_state() {
    mkdir -p "$(dirname "$STATE_FILE")"

    # Preserve session_stats only if a corrupt-but-readable file remains. A fully
    # deleted file means stats are genuinely lost (acceptable); a still-present
    # file must not be clobbered.
    local prev_stats='{}'
    if [[ -f "$STATE_FILE" ]]; then
        prev_stats=$(jq '.session_stats // {}' "$STATE_FILE" 2>/dev/null || echo '{}')
    fi

    local started_at
    started_at="$(daemon_start_time_iso)"

    local new_state tmp
    new_state=$(jq -n \
        --arg started_at "$started_at" \
        --argjson enricher "${DAEMON_CONFIG_ENRICHER:-$DEFAULT_ENRICHER}" \
        --argjson aristotle "${DAEMON_CONFIG_ARISTOTLE:-$DEFAULT_ARISTOTLE}" \
        --argjson researcher "${DAEMON_CONFIG_RESEARCHER:-$DEFAULT_RESEARCHER}" \
        --argjson auditor "${DAEMON_CONFIG_AUDITOR:-$DEFAULT_AUDITOR}" \
        --argjson seeker "${DAEMON_CONFIG_SEEKER:-$DEFAULT_SEEKER}" \
        --argjson deployer "${DAEMON_CONFIG_DEPLOYER:-$DEFAULT_DEPLOYER}" \
        --argjson tester "${DAEMON_CONFIG_TESTER:-$DEFAULT_TESTER}" \
        --argjson herald "${DAEMON_CONFIG_HERALD:-$DEFAULT_HERALD}" \
        --argjson mechanic "${DAEMON_CONFIG_MECHANIC:-$DEFAULT_MECHANIC}" \
        --argjson prev_stats "$prev_stats" \
        '{
            started_at: $started_at,
            running: true,
            config: {
                enricher: $enricher,
                aristotle: $aristotle,
                researcher: $researcher,
                auditor: $auditor,
                seeker: $seeker,
                deployer: $deployer,
                tester: $tester,
                herald: $herald,
                mechanic: $mechanic
            },
            agents: {},
            session_stats: (
                if ($prev_stats | length) > 0 then $prev_stats
                else {
                    entries_enriched: 0,
                    proofs_submitted: 0,
                    proofs_integrated: 0,
                    problems_selected: 0,
                    deployments: 0,
                    research_completed: 0
                }
                end
            )
        }')

    # Atomic write (temp-file + mv), matching the existing update patterns.
    tmp=$(mktemp)
    printf '%s\n' "$new_state" > "$tmp" && mv "$tmp" "$STATE_FILE"

    if declare -F daemon_log >/dev/null 2>&1; then
        daemon_log "WARN" "STATE_FILE was missing/corrupt; self-healed with started_at=$started_at (#41048)"
    fi
}

update_daemon_state() {
    local cycle_count="$1"
    local respawn_count="$2"

    # Self-heal: if the state file was deleted (e.g. a Loom reinstall wiped
    # .loom/) or corrupted, recreate it instead of silently no-op'ing (#41048).
    if [[ ! -f "$STATE_FILE" ]] || ! jq empty "$STATE_FILE" >/dev/null 2>&1; then
        recreate_daemon_state
    fi

    if [[ -f "$STATE_FILE" ]]; then
        local tmp
        tmp=$(mktemp)
        jq \
            --argjson cycle "$cycle_count" \
            --argjson respawns "$respawn_count" \
            --arg last_cycle "$(date -u +"%Y-%m-%dT%H:%M:%SZ")" \
            '.daemon_cycles = $cycle | .daemon_respawns = $respawns | .last_daemon_cycle = $last_cycle' \
            "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
    fi
}

# Helper: Process completion signals and update session stats
# Agents create signal files when they complete work, daemon consumes them and updates counters
process_completion_signals() {
    # Resolve the canonical completions directory (shared main checkout), NOT a
    # daemon-cwd-relative path -- producers in worktrees write here too (#41047).
    local comp_dir
    comp_dir="$(resolve_completions_dir)"

    # Ensure completions directory exists
    mkdir -p "$comp_dir/archive"

    local enriched=0
    local proofs=0
    local integrated=0
    local selected=0
    local deploys=0
    local researched=0

    # Count signals by type (use find to avoid glob expansion issues)
    enriched=$(find "$comp_dir" -maxdepth 1 -name 'enrichment-completed-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    proofs=$(find "$comp_dir" -maxdepth 1 -name 'proof-submitted-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    integrated=$(find "$comp_dir" -maxdepth 1 -name 'proof-integrated-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    selected=$(find "$comp_dir" -maxdepth 1 -name 'problem-selected-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    deploys=$(find "$comp_dir" -maxdepth 1 -name 'deployment-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    researched=$(find "$comp_dir" -maxdepth 1 -name 'research-completed-*' -type f 2>/dev/null | wc -l | tr -d ' ')

    local total=$((enriched + proofs + integrated + selected + deploys + researched))

    # Update state file if any completions
    if [[ $total -gt 0 ]]; then
        if [[ -f "$STATE_FILE" ]]; then
            local tmp
            tmp=$(mktemp)
            jq \
                --argjson enriched "$enriched" \
                --argjson proofs "$proofs" \
                --argjson integrated "$integrated" \
                --argjson selected "$selected" \
                --argjson deploys "$deploys" \
                --argjson researched "$researched" \
                '.session_stats.entries_enriched += $enriched |
                 .session_stats.proofs_submitted += $proofs |
                 .session_stats.proofs_integrated += $integrated |
                 .session_stats.problems_selected += $selected |
                 .session_stats.deployments += $deploys |
                 .session_stats.research_completed += $researched' \
                "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
        fi

        daemon_log "INFO" "Stats updated: +$enriched enriched, +$proofs proofs, +$integrated integrated, +$selected selected, +$deploys deploys, +$researched researched"

        # Archive signals (preserve for debugging but don't recount)
        find "$comp_dir" -maxdepth 1 -type f -name 'enrichment-completed-*' -exec mv {} "$comp_dir/archive/" \; 2>/dev/null || true
        find "$comp_dir" -maxdepth 1 -type f -name 'proof-submitted-*' -exec mv {} "$comp_dir/archive/" \; 2>/dev/null || true
        find "$comp_dir" -maxdepth 1 -type f -name 'proof-integrated-*' -exec mv {} "$comp_dir/archive/" \; 2>/dev/null || true
        find "$comp_dir" -maxdepth 1 -type f -name 'problem-selected-*' -exec mv {} "$comp_dir/archive/" \; 2>/dev/null || true
        find "$comp_dir" -maxdepth 1 -type f -name 'deployment-*' -exec mv {} "$comp_dir/archive/" \; 2>/dev/null || true
        find "$comp_dir" -maxdepth 1 -type f -name 'research-completed-*' -exec mv {} "$comp_dir/archive/" \; 2>/dev/null || true
    fi
}

# Helper: Clean up daemon PID file and signal handler
daemon_cleanup() {
    daemon_log "INFO" "Daemon shutting down (PID $$)"
    rm -f "$DAEMON_PID_FILE"
    # Clean up temp respawn cache files
    rm -f /tmp/lean-daemon-respawn-* 2>/dev/null || true
    set_stopped
}

# Command: daemon - Continuous monitoring loop
cmd_daemon() {
    local interval=$DEFAULT_DAEMON_INTERVAL
    local enricher=$DEFAULT_ENRICHER
    local aristotle=$DEFAULT_ARISTOTLE
    local researcher=$DEFAULT_RESEARCHER
    local seeker=$DEFAULT_SEEKER
    local deployer=$DEFAULT_DEPLOYER
    local auditor=$DEFAULT_AUDITOR
    local tester=$DEFAULT_TESTER
    local herald=$DEFAULT_HERALD
    local mechanic=$DEFAULT_MECHANIC
    local monitor_only=false

    # Apply time-based schedule (overrides defaults before CLI args)
    apply_schedule

    # Parse options (explicit CLI args override schedule)
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --monitor-only)
                monitor_only=true
                shift
                ;;
            --interval)
                interval="$2"
                shift 2
                ;;
            --enricher)
                enricher="$2"
                shift 2
                ;;
            --aristotle)
                aristotle="$2"
                shift 2
                ;;
            --researcher)
                researcher="$2"
                shift 2
                ;;
            --auditor)
                auditor="$2"
                shift 2
                ;;
            --seeker)
                seeker="$2"
                shift 2
                ;;
            --deployer)
                deployer="$2"
                shift 2
                ;;
            --tester)
                tester="$2"
                shift 2
                ;;
            --herald)
                herald="$2"
                shift 2
                ;;
            --mechanic)
                mechanic="$2"
                shift 2
                ;;
            *)
                echo -e "${RED}Unknown daemon option: $1${NC}" >&2
                usage
                exit 1
                ;;
        esac
    done

    # Expose the daemon's live pool config as globals so recreate_daemon_state()
    # can rebuild a deleted/corrupt STATE_FILE without a full restart (#41048).
    DAEMON_CONFIG_ENRICHER="$enricher"
    DAEMON_CONFIG_ARISTOTLE="$aristotle"
    DAEMON_CONFIG_RESEARCHER="$researcher"
    DAEMON_CONFIG_AUDITOR="$auditor"
    DAEMON_CONFIG_SEEKER="$seeker"
    DAEMON_CONFIG_DEPLOYER="$deployer"
    DAEMON_CONFIG_TESTER="$tester"
    DAEMON_CONFIG_HERALD="$herald"
    DAEMON_CONFIG_MECHANIC="$mechanic"

    # Check for existing daemon
    if [[ -f "$DAEMON_PID_FILE" ]]; then
        local existing_pid
        existing_pid=$(cat "$DAEMON_PID_FILE" 2>/dev/null || echo "")
        if [[ -n "$existing_pid" ]] && kill -0 "$existing_pid" 2>/dev/null; then
            echo -e "${RED}Daemon already running (PID: $existing_pid)${NC}" >&2
            echo "Stop it first: $0 stop"
            exit 1
        else
            daemon_log "WARN" "Stale PID file found (PID $existing_pid not running), removing"
            rm -f "$DAEMON_PID_FILE"
        fi
    fi

    # Remove stale stop signal if present from a previous run
    rm -f "$STOP_SIGNAL_FILE" 2>/dev/null || true

    # Ensure completions directory exists for session stats tracking
    mkdir -p "$(resolve_completions_dir)/archive"

    # Write PID file
    mkdir -p "$(dirname "$DAEMON_PID_FILE")"
    echo $$ > "$DAEMON_PID_FILE"

    # Set up signal handlers for clean shutdown
    trap daemon_cleanup EXIT
    trap 'daemon_log "INFO" "Received SIGTERM"; exit 0' TERM
    trap 'daemon_log "INFO" "Received SIGINT"; exit 0' INT

    daemon_log "INFO" "Starting daemon (PID $$, interval ${interval}s, monitor_only=$monitor_only)"
    daemon_log "INFO" "Pool config: enricher=$enricher, aristotle=$aristotle, researcher=$researcher, auditor=$auditor, seeker=$seeker, deployer=$deployer, tester=$tester, herald=$herald, mechanic=$mechanic"
    guard_git_auto_gc

    if [[ "$monitor_only" == "true" ]]; then
        daemon_log "INFO" "Monitor-only mode: skipping agent startup, monitoring existing sessions"
        # Update state file with target config so pool gap detection works
        if [[ -f "$STATE_FILE" ]]; then
            local tmp
            tmp=$(mktemp)
            jq \
                --argjson enricher "$enricher" \
                --argjson aristotle "$aristotle" \
                --argjson researcher "$researcher" \
                --argjson seeker "$seeker" \
                --argjson deployer "$deployer" \
                '.config.enricher = $enricher |
                 .config.aristotle = $aristotle |
                 .config.researcher = $researcher |
                 .config.seeker = $seeker |
                 .config.deployer = $deployer' \
                "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
        fi
    else
        # Start initial agents via cmd_start
        cmd_start --enricher "$enricher" --aristotle "$aristotle" --researcher "$researcher" --auditor "$auditor" --seeker "$seeker" --deployer "$deployer" --tester "$tester" --herald "$herald" --mechanic "$mechanic"
    fi

    local cycle_count=0
    local total_respawns=0

    # Main monitoring loop
    while true; do
        sleep "$interval"

        cycle_count=$((cycle_count + 1))

        # 1. Check stop signal
        if [[ -f "$STOP_SIGNAL_FILE" ]]; then
            daemon_log "INFO" "Stop signal detected ($STOP_SIGNAL_FILE), shutting down agents..."
            daemon_log "INFO" "Signal file details: $(ls -la "$STOP_SIGNAL_FILE" 2>&1)"
            daemon_log "INFO" "Signal file stat: $(stat -f 'created=%SB modified=%Sm owner=%Su' "$STOP_SIGNAL_FILE" 2>/dev/null || stat --format='modified=%y owner=%U' "$STOP_SIGNAL_FILE" 2>/dev/null || echo 'N/A')"
            cmd_stop --force
            rm -f "$STOP_SIGNAL_FILE" 2>/dev/null || true
            daemon_log "INFO" "Daemon stopped after $cycle_count cycles, $total_respawns total respawns"
            break
        fi

        # Re-read target config from state file each cycle, then apply the
        # time-based schedule. Done BEFORE the health check so both the normal
        # path and the total-blackout early-continue (#41509) see the same
        # scheduled targets -- otherwise a scheduled scale-to-zero during a
        # blackout would false-alarm on stale config.
        # (This ensures scale-down / stop commands are respected without a
        # daemon restart.)
        if [[ -f "$STATE_FILE" ]]; then
            enricher=$(jq -r '.config.enricher // 0' "$STATE_FILE" 2>/dev/null || echo "$enricher")
            aristotle=$(jq -r '.config.aristotle // 0' "$STATE_FILE" 2>/dev/null || echo "$aristotle")
            researcher=$(jq -r '.config.researcher // 0' "$STATE_FILE" 2>/dev/null || echo "$researcher")
            seeker=$(jq -r '.config.seeker // 0' "$STATE_FILE" 2>/dev/null || echo "$seeker")
            auditor=$(jq -r '.config.auditor // 0' "$STATE_FILE" 2>/dev/null || echo "$auditor")
            deployer=$(jq -r '.config.deployer // 0' "$STATE_FILE" 2>/dev/null || echo "$deployer")
            herald=$(jq -r '.config.herald // 0' "$STATE_FILE" 2>/dev/null || echo "$herald")
            mechanic=$(jq -r '.config.mechanic // 0' "$STATE_FILE" 2>/dev/null || echo "$mechanic")
        fi

        # Apply time-based schedule overrides
        apply_schedule

        # 2. Health check all agent sessions
        local sessions
        sessions=$(get_all_agent_sessions)

        if [[ -z "$sessions" ]]; then
            daemon_log "WARN" "No agent sessions found, cycle $cycle_count"
            # Total-pool blackout (#41509): the health-check / pool-gap / respawn
            # logic below is intentionally skipped when there are zero sessions,
            # but persistent-missing detection must still fire so .missing_agents
            # is persisted and /lean status shows MISSING rows (not just the live
            # /lean health view). Reuse the same helper as the normal path.
            detect_and_persist_missing_agents \
                "$enricher" "$researcher" "$aristotle" "$auditor" \
                "$seeker" "$deployer" "$herald" "$mechanic" "$tester"
            update_daemon_state "$cycle_count" "$total_respawns"
            continue
        fi

        local cycle_respawns=0
        local running_count=0
        local completed_count=0
        local stuck_count=0
        local idle_count=0

        while IFS= read -r session; do
            [[ -z "$session" ]] && continue

            local status
            status=$(get_agent_status "$session")

            # Failure-loop check: wrapper retries on its own (e.g. 5min cooldown),
            # so an agent can stay RUNNING/IDLE while every cycle errors. Force a
            # respawn once consecutive_failures crosses the threshold.
            local failures
            failures=$(get_consecutive_failures "$session")
            if [[ "$status" == "RUNNING" || "$status" == "IDLE" ]] && \
               [[ "$failures" -ge "$CONSECUTIVE_FAILURE_THRESHOLD" ]]; then
                if is_cooldown_elapsed "$session"; then
                    daemon_log "WARN" "Agent $session FAILING (${failures} consecutive failures), killing and respawning..."
                    if kill_and_respawn "$session"; then
                        cycle_respawns=$((cycle_respawns + 1))
                    fi
                    continue
                else
                    local last_f
                    last_f=$(get_last_respawn "$session")
                    local now_f
                    now_f=$(date +%s)
                    local remaining_f=$(( RESPAWN_COOLDOWN_SECONDS - (now_f - last_f) ))
                    daemon_log "WARN" "Agent $session FAILING (${failures}) but in cooldown (${remaining_f}s remaining)"
                fi
            fi

            case "$status" in
                RUNNING)
                    running_count=$((running_count + 1))
                    ;;
                IDLE)
                    # Polling agents (deployer, seeker) are healthy but waiting between cycles
                    idle_count=$((idle_count + 1))
                    ;;
                COMPLETED)
                    completed_count=$((completed_count + 1))
                    if is_cooldown_elapsed "$session"; then
                        daemon_log "INFO" "Agent $session COMPLETED, respawning..."
                        if respawn_agent "$session"; then
                            cycle_respawns=$((cycle_respawns + 1))
                        fi
                    else
                        local last
                        last=$(get_last_respawn "$session")
                        local now
                        now=$(date +%s)
                        local remaining=$(( RESPAWN_COOLDOWN_SECONDS - (now - last) ))
                        daemon_log "INFO" "Agent $session COMPLETED but in cooldown (${remaining}s remaining)"
                    fi
                    ;;
                STUCK)
                    stuck_count=$((stuck_count + 1))
                    if is_cooldown_elapsed "$session"; then
                        daemon_log "WARN" "Agent $session STUCK, killing and respawning..."
                        if kill_and_respawn "$session"; then
                            cycle_respawns=$((cycle_respawns + 1))
                        fi
                    else
                        local last
                        last=$(get_last_respawn "$session")
                        local now
                        now=$(date +%s)
                        local remaining=$(( RESPAWN_COOLDOWN_SECONDS - (now - last) ))
                        daemon_log "WARN" "Agent $session STUCK but in cooldown (${remaining}s remaining)"
                    fi
                    ;;
                *)
                    daemon_log "WARN" "Agent $session has status: $status"
                    ;;
            esac
        done <<< "$sessions"

        total_respawns=$((total_respawns + cycle_respawns))

        # 2a. Periodic research DB sync (JSON -> DB, every 10 cycles)
        if [[ $((cycle_count % 10)) -eq 1 ]]; then
            if [[ -f "research/db/sync_from_json.py" ]] && [[ -f "research/db/knowledge.db" ]]; then
                daemon_log "INFO" "Running research DB sync (JSON -> DB)..."
                if python3 research/db/sync_from_json.py 2>&1 | while IFS= read -r line; do daemon_log "INFO" "sync_from_json: $line"; done; then
                    # Regenerate candidate pool from updated DB
                    if python3 research/db/sync_pool.py 2>&1 | while IFS= read -r line; do daemon_log "INFO" "sync_pool: $line"; done; then
                        daemon_log "INFO" "Research DB sync complete"
                    fi
                else
                    daemon_log "WARN" "Research DB sync failed (non-fatal)"
                fi
            fi
        fi

        # 2a-post. Sweep for orphaned claude processes (detached from any tmux session)
        local orphan_pids
        orphan_pids=$(ps aux | grep '[c]laude -p.*\(researcher\|enricher\|deployer\|seeker\|aristotle\|auditor\|mechanic\)' | awk '$7 == "??" {print $2}')
        if [[ -n "$orphan_pids" ]]; then
            local orphan_count
            orphan_count=$(echo "$orphan_pids" | wc -l | tr -d ' ')
            daemon_log "WARN" "Found $orphan_count orphaned claude process(es), killing..."
            echo "$orphan_pids" | xargs kill 2>/dev/null || true
        fi

        # 2b. Pool gap detection: spawn missing agents whose sessions vanished
        # (get_all_agent_sessions only returns existing sessions, so if a session
        # exits entirely, the health check above never sees it). Target config
        # was already re-read from STATE_FILE + schedule-adjusted at the top of
        # this cycle (before the blackout early-continue).

        local enricher_active=0 researcher_active=0 aristotle_active=0 auditor_active=0 seeker_active=0 deployer_active=0 herald_active=0 mechanic_active=0
        for i in $(seq 1 $MAX_ENRICHER); do
            tmux has-session -t "enricher-$i" 2>/dev/null && enricher_active=$((enricher_active + 1))
        done
        for i in $(seq 1 $MAX_RESEARCHER); do
            tmux has-session -t "researcher-$i" 2>/dev/null && researcher_active=$((researcher_active + 1))
        done
        tmux has-session -t "aristotle-agent" 2>/dev/null && aristotle_active=1
        tmux has-session -t "auditor-agent" 2>/dev/null && auditor_active=1
        tmux has-session -t "seeker-agent" 2>/dev/null && seeker_active=1
        tmux has-session -t "deployer" 2>/dev/null && deployer_active=1
        tmux has-session -t "herald-agent" 2>/dev/null && herald_active=1
        for i in 1 2 3; do
            tmux has-session -t "mechanic-$i" 2>/dev/null && mechanic_active=$((mechanic_active + 1))
        done
        tmux has-session -t "mechanic-agent" 2>/dev/null && mechanic_active=$((mechanic_active + 1))

        if [[ $enricher_active -lt $enricher ]]; then
            local missing_enricher=$((enricher - enricher_active))
            daemon_log "INFO" "Pool gap: enricher has $enricher_active/$enricher, spawning $missing_enricher"
            for i in $(seq 1 5); do
                [[ $missing_enricher -le 0 ]] && break
                if ! tmux has-session -t "enricher-$i" 2>/dev/null; then
                    if is_cooldown_elapsed "enricher-$i"; then
                        if respawn_agent "enricher-$i"; then
                            total_respawns=$((total_respawns + 1))
                            missing_enricher=$((missing_enricher - 1))
                        fi
                    fi
                fi
            done
        fi

        if [[ $researcher_active -lt $researcher ]]; then
            local missing_res=$((researcher - researcher_active))
            daemon_log "INFO" "Pool gap: researcher has $researcher_active/$researcher, spawning $missing_res"
            for i in $(seq 1 $MAX_RESEARCHER); do
                [[ $missing_res -le 0 ]] && break
                if ! tmux has-session -t "researcher-$i" 2>/dev/null; then
                    if is_cooldown_elapsed "researcher-$i"; then
                        if respawn_agent "researcher-$i"; then
                            total_respawns=$((total_respawns + 1))
                            missing_res=$((missing_res - 1))
                        fi
                    fi
                fi
            done
        fi

        if [[ $aristotle_active -lt $aristotle ]] && is_cooldown_elapsed "aristotle-agent"; then
            # Scale-to-zero gate (issue #22471): if the marker file is
            # present, treat the missing session as intentional and skip
            # the pool gap respawn. The dedicated dynamic-spawn block
            # below (step 4b) will respawn the moment real work appears.
            if [[ -f "$ARISTOTLE_SCALED_MARKER" ]]; then
                daemon_log "INFO" "Pool gap: aristotle scaled-to-zero, deferring respawn until queue has work"
            else
                daemon_log "INFO" "Pool gap: aristotle has 0/$aristotle, spawning"
                if respawn_agent "aristotle-agent"; then
                    total_respawns=$((total_respawns + 1))
                fi
            fi
        fi

        if [[ $seeker_active -lt $seeker ]] && is_cooldown_elapsed "seeker-agent"; then
            daemon_log "INFO" "Pool gap: seeker has 0/$seeker, spawning"
            if respawn_agent "seeker-agent"; then
                total_respawns=$((total_respawns + 1))
            fi
        fi

        if [[ $auditor_active -lt $auditor ]] && is_cooldown_elapsed "auditor-agent"; then
            daemon_log "INFO" "Pool gap: auditor has 0/$auditor, spawning"
            if respawn_agent "auditor-agent"; then
                total_respawns=$((total_respawns + 1))
            fi
        fi

        if [[ $deployer_active -lt $deployer ]] && is_cooldown_elapsed "deployer"; then
            daemon_log "INFO" "Pool gap: deployer has 0/$deployer, spawning"
            if respawn_agent "deployer"; then
                total_respawns=$((total_respawns + 1))
            fi
        fi
        if [[ $herald_active -lt $herald ]] && is_cooldown_elapsed "herald-agent"; then
            daemon_log "INFO" "Pool gap: herald has 0/$herald, spawning"
            if respawn_agent "herald-agent"; then
                total_respawns=$((total_respawns + 1))
            fi
        fi

        if [[ $mechanic_active -lt $mechanic ]]; then
            local missing_mech=$((mechanic - mechanic_active))
            daemon_log "INFO" "Pool gap: mechanic has $mechanic_active/$mechanic, spawning $missing_mech"
            for i in 1 2 3; do
                [[ $missing_mech -le 0 ]] && break
                if ! tmux has-session -t "mechanic-$i" 2>/dev/null; then
                    if is_cooldown_elapsed "mechanic-$i"; then
                        if respawn_agent "mechanic-$i"; then
                            total_respawns=$((total_respawns + 1))
                            missing_mech=$((missing_mech - 1))
                        fi
                    fi
                fi
            done
        fi

        # 2c. Persistent-missing-session detection & alerting (#39652).
        # The pool-gap respawns above try to bring absent agents back every
        # cycle, but when the launcher dies silently (#39649) a CONFIGURED
        # agent can stay session-less indefinitely with only routine INFO
        # "pool gap" noise -- exactly how the deployer went unnoticed for 7
        # days. detect_and_persist_missing_agents tracks consecutive absent
        # cycles per configured agent, escalates to a WARN past the threshold,
        # and persists the MISSING set that /lean health & /lean status render
        # as a red row. (The same helper also runs on the total-blackout
        # early-continue path above -- #41509.)
        detect_and_persist_missing_agents \
            "$enricher" "$researcher" "$aristotle" "$auditor" \
            "$seeker" "$deployer" "$herald" "$mechanic" "$tester"

        # 3. Work queue assessment (with timeout protection)
        local queue_stats
        queue_stats=$(get_work_queue_stats)
        local enrichment_targets candidates aristotle_jobs aristotle_candidates ready_prs
        read -r enrichment_targets candidates aristotle_jobs aristotle_candidates ready_prs <<< "$queue_stats"

        # 4. Process completion signals and update session stats
        process_completion_signals

        # 4b. Dynamic Aristotle: spawn when candidates or jobs exist but no agent running.
        # Scale-to-zero (issue #22471) is the inverse: when the agent has
        # exited because both queues are empty + idle threshold elapsed,
        # this block is the only path that brings it back. We always
        # clear the marker on respawn so the next "fresh start clears
        # marker" handshake in aristotle-agent.sh is a no-op (idempotent).
        if [[ $aristotle_active -eq 0 ]] && [[ "$aristotle_jobs" -gt 0 || "$aristotle_candidates" -gt 0 ]]; then
            if is_cooldown_elapsed "aristotle-agent"; then
                if [[ -f "$ARISTOTLE_SCALED_MARKER" ]]; then
                    daemon_log "INFO" "Scale-up Aristotle: work appeared (jobs=$aristotle_jobs, candidates=$aristotle_candidates), clearing scale-to-zero marker"
                    clear_aristotle_scaled_marker
                else
                    daemon_log "INFO" "Auto-spawning Aristotle: $aristotle_jobs pending jobs, $aristotle_candidates candidates"
                fi
                if respawn_agent "aristotle-agent"; then
                    total_respawns=$((total_respawns + 1))
                fi
            fi
        fi

        # 5. Log cycle summary
        daemon_log "INFO" "Cycle $cycle_count: running=$running_count, idle=$idle_count, completed=$completed_count, stuck=$stuck_count, respawned=$cycle_respawns | queues: enrichment=$enrichment_targets, candidates=$candidates, aristotle_jobs=$aristotle_jobs, aristotle_candidates=$aristotle_candidates, prs=$ready_prs"

        # 6. Update state file with daemon stats
        update_daemon_state "$cycle_count" "$total_respawns"

        # 7. Re-check stop signal after respawning (race condition prevention)
        if [[ -f "$STOP_SIGNAL_FILE" ]]; then
            daemon_log "INFO" "Stop signal detected after respawn, shutting down..."
            daemon_log "INFO" "Signal file details: $(ls -la "$STOP_SIGNAL_FILE" 2>&1)"
            daemon_log "INFO" "Signal file stat: $(stat -f 'created=%SB modified=%Sm owner=%Su' "$STOP_SIGNAL_FILE" 2>/dev/null || stat --format='modified=%y owner=%U' "$STOP_SIGNAL_FILE" 2>/dev/null || echo 'N/A')"
            cmd_stop --force
            rm -f "$STOP_SIGNAL_FILE" 2>/dev/null || true
            daemon_log "INFO" "Daemon stopped after $cycle_count cycles, $total_respawns total respawns"
            break
        fi
    done
}

# Command: stop [type] [--force]
# If type is provided, only stop agents of that type.
# If no type is provided, stop all agents.
cmd_stop() {
    local force=false
    local agent_type=""

    # Parse stop options
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --force|-f)
                force=true
                shift
                ;;
            enricher|aristotle|researcher|auditor|seeker|deployer|herald|mechanic)
                agent_type="$1"
                shift
                ;;
            *)
                echo -e "${RED}Unknown stop option: $1${NC}" >&2
                echo "Usage: $0 stop [enricher|aristotle|researcher|auditor|seeker|deployer|herald|mechanic] [--force]"
                exit 1
                ;;
        esac
    done

    # If a specific agent type is requested, delegate to per-type stop
    if [[ -n "$agent_type" ]]; then
        cmd_stop_type "$agent_type" "$force"
        return
    fi

    if [[ "$force" == "true" ]]; then
        echo -e "${BOLD}Force-Stopping Lean Genius Mathematical Orchestration${NC}"
        echo ""

        # ============================================================
        # STEP 1: Kill the daemon FIRST to prevent respawning
        # ============================================================
        echo -e "${BLUE}Stopping daemon (prevents respawning)...${NC}"

        # Create stop signal file immediately
        mkdir -p "$SIGNALS_DIR"
        touch "$STOP_SIGNAL_FILE" 2>/dev/null || true

        # Kill daemon process via PID file
        if [[ -f "$DAEMON_PID_FILE" ]]; then
            local daemon_pid
            daemon_pid=$(cat "$DAEMON_PID_FILE" 2>/dev/null || echo "")
            if [[ -n "$daemon_pid" ]] && kill -0 "$daemon_pid" 2>/dev/null; then
                echo -e "  Killing daemon PID: $daemon_pid"
                kill "$daemon_pid" 2>/dev/null || true
            fi
            rm -f "$DAEMON_PID_FILE" 2>/dev/null || true
        fi

        # Kill the lean-daemon tmux session (the respawner)
        if tmux has-session -t "lean-daemon" 2>/dev/null; then
            echo -e "  Killing lean-daemon tmux session"
            kill_session_processes "lean-daemon"
        fi

        local stopped=0

        # ============================================================
        # STEP 2: Stop agent groups via their stop scripts
        # ============================================================
        echo -e "${BLUE}Killing Enricher sessions...${NC}"
        if [[ -x "./scripts/enricher/parallel-enrich.sh" ]]; then
            ./scripts/enricher/parallel-enrich.sh --stop 2>/dev/null || true
            stopped=$((stopped + 1))
        fi

        echo -e "${BLUE}Killing Aristotle agent session...${NC}"
        if [[ -x "./scripts/aristotle/launch-agent.sh" ]]; then
            ./scripts/aristotle/launch-agent.sh --stop 2>/dev/null || true
            stopped=$((stopped + 1))
        fi

        echo -e "${BLUE}Killing Researcher sessions...${NC}"
        if [[ -x "./scripts/research/parallel-research.sh" ]]; then
            ./scripts/research/parallel-research.sh --stop 2>/dev/null || true
            stopped=$((stopped + 1))
        fi

        echo -e "${BLUE}Killing Seeker agent session...${NC}"
        if tmux has-session -t "seeker-agent" 2>/dev/null; then
            kill_session_processes "seeker-agent"
            stopped=$((stopped + 1))
        fi

        echo -e "${BLUE}Killing Deployer session...${NC}"
        if [[ -x "./scripts/deploy/launch-agent.sh" ]]; then
            ./scripts/deploy/launch-agent.sh --stop 2>/dev/null || true
            stopped=$((stopped + 1))
        fi

        # ============================================================
        # STEP 3: Kill ALL agent tmux sessions (catch-all)
        # ============================================================
        echo -e "${BLUE}Catch-all: cleaning remaining agent sessions...${NC}"
        local remaining_sessions
        remaining_sessions=$(tmux list-sessions -F '#{session_name}' 2>/dev/null | grep -E '^(lean-daemon$|enricher-|researcher-|mechanic-|aristotle-agent$|auditor-agent$|mechanic-agent$|seeker-agent$|deployer$|herald-agent$|tester-agent$)' || true)
        if [[ -n "$remaining_sessions" ]]; then
            while IFS= read -r session; do
                echo -e "  Killing stale session: $session"
                kill_session_processes "$session"
            done <<< "$remaining_sessions"
        fi

        # ============================================================
        # STEP 4: pkill sweep — kill ALL agent processes by pattern
        # This catches processes regardless of TTY or tmux state
        # ============================================================
        echo -e "${BLUE}Sweeping all agent processes (pkill)...${NC}"
        local sweep_count=0

        # Kill claude -p agent processes (any TTY, not just orphans)
        local agent_pids
        agent_pids=$(ps aux | grep '[c]laude -p.*dangerously-skip-permissions.*\(researcher\|enricher\|deployer\|seeker\|aristotle\|auditor\|mechanic\|herald\|tester\)' | awk '{print $2}')
        if [[ -n "$agent_pids" ]]; then
            sweep_count=$(echo "$agent_pids" | wc -l | tr -d ' ')
            echo -e "  Killing $sweep_count claude agent process(es)"
            echo "$agent_pids" | xargs kill 2>/dev/null || true
        fi

        # Kill timeout wrappers AND their full descendant tree.
        # Bare `pkill -f` would leave grandchildren (zsh shell-snapshot ->
        # bash docker-build.sh -> docker CLI) orphaned to init. See #15191.
        kill_pattern_tree 'timeout.*claude -p.*dangerously-skip-permissions' TERM

        # Kill claude-wrapper.sh scripts and their full subtree
        kill_pattern_tree 'claude-wrapper.sh.*(researcher|enricher|deployer|seeker|aristotle|auditor|mechanic|herald|tester)' TERM

        # Kill aristotle-agent.sh and its full subtree
        kill_pattern_tree 'aristotle-agent.sh' TERM

        # ============================================================
        # STEP 5: Orphan sweep — catch already-reparented descendants
        # whose parent agent was killed in an earlier cycle. These have
        # PPID=1 now, so no parent-based walk can find them. We match
        # against known orphan signatures from the lean-genius tree.
        # See #15191 for the postmortem.
        # ============================================================
        local repo_root_pat
        repo_root_pat="$(pwd)"
        local orphan_patterns=(
            "docker-build.sh.*Proofs"
            "lean-build-[0-9]+"
            "/bin/zsh.*shell-snapshots.*${repo_root_pat}"
            "bash .*proofs/scripts/docker-build.sh"
        )
        local pat
        for pat in "${orphan_patterns[@]}"; do
            kill_pattern_tree "$pat" TERM
        done

        # Brief wait, then force-kill any survivors
        sleep 2
        local survivors
        survivors=$(ps aux | grep '[c]laude -p.*dangerously-skip-permissions.*\(researcher\|enricher\|deployer\|seeker\|aristotle\|auditor\|mechanic\|herald\|tester\)' | awk '{print $2}')
        if [[ -n "$survivors" ]]; then
            local survivor_count
            survivor_count=$(echo "$survivors" | wc -l | tr -d ' ')
            echo -e "  Force-killing $survivor_count surviving process(es)"
            echo "$survivors" | xargs kill -9 2>/dev/null || true
            kill_pattern_tree 'timeout.*claude -p.*dangerously-skip-permissions' KILL
            kill_pattern_tree 'claude-wrapper.sh.*(researcher|enricher|deployer|seeker|aristotle|auditor|mechanic|herald|tester)' KILL
        fi

        # Force-kill orphan survivors regardless of claude survivors
        local orphan_survivors=0
        for pat in "${orphan_patterns[@]}"; do
            local n
            n=$(pgrep -f "$pat" 2>/dev/null | wc -l | tr -d ' ')
            if [[ "$n" -gt 0 ]]; then
                orphan_survivors=$((orphan_survivors + n))
                kill_pattern_tree "$pat" KILL
            fi
        done

        if [[ -z "$survivors" && "$orphan_survivors" -eq 0 ]]; then
            echo -e "  ${GREEN}All agent processes confirmed dead${NC}"
        elif [[ "$orphan_survivors" -gt 0 ]]; then
            echo -e "  Force-killed $orphan_survivors orphan descendant(s)"
        fi

        # Update state (preserves agents, session_stats, etc.)
        set_stopped

        echo ""
        echo -e "${GREEN}${BOLD}All agent sessions killed${NC}"
    else
        echo -e "${BOLD}Gracefully Stopping Lean Genius Mathematical Orchestration${NC}"
        echo ""

        # Create signal files for graceful shutdown
        mkdir -p "$SIGNALS_DIR"
        touch "$SIGNALS_DIR/stop-all"
        echo -e "${GREEN}Created stop-all signal file${NC}"

        # Also signal each agent type through their own mechanisms
        echo -e "${BLUE}Signaling Enrichers...${NC}"
        if [[ -x "./scripts/enricher/parallel-enrich.sh" ]]; then
            ./scripts/enricher/parallel-enrich.sh --graceful-stop 2>/dev/null || true
        fi

        echo -e "${BLUE}Signaling Aristotle agent...${NC}"
        if [[ -x "./scripts/aristotle/launch-agent.sh" ]]; then
            ./scripts/aristotle/launch-agent.sh --graceful-stop 2>/dev/null || true
        fi

        echo -e "${BLUE}Signaling Researchers...${NC}"
        if [[ -x "./scripts/research/parallel-research.sh" ]]; then
            ./scripts/research/parallel-research.sh --graceful-stop 2>/dev/null || true
        fi

        echo -e "${BLUE}Signaling Auditor agent...${NC}"
        touch "$SIGNALS_DIR/stop-auditor" 2>/dev/null || true

        echo -e "${BLUE}Signaling Mechanic agent(s)...${NC}"
        touch "$SIGNALS_DIR/stop-mechanic" 2>/dev/null || true

        echo -e "${BLUE}Signaling Seeker agent...${NC}"
        touch "$SIGNALS_DIR/stop-seeker" 2>/dev/null || true

        echo -e "${BLUE}Signaling Deployer...${NC}"
        # Deployer's --stop already creates signal + kills, so just create signal
        touch "$SIGNALS_DIR/stop-deployer" 2>/dev/null || true

        # Update state (preserves agents, session_stats, etc.)
        set_stopped

        # Create stop signal file (also stops the daemon loop if running)
        touch "$STOP_SIGNAL_FILE" 2>/dev/null || true

        echo ""
        echo -e "${GREEN}${BOLD}Signal files created for graceful shutdown${NC}"
        echo ""
        echo "Agents will finish their current work before stopping."
        if [[ -f "$DAEMON_PID_FILE" ]]; then
            echo "Daemon will detect stop signal and exit on next cycle."
        fi
        echo "Use './scripts/lean/status.sh' to monitor shutdown progress."

        # Check for stuck agents and warn
        check_for_stuck_agents || true
    fi
}

# Command: stop <type> - Stop agents of a specific type only
cmd_stop_type() {
    local agent_type="$1"
    local force="${2:-false}"

    # Update daemon state config FIRST to prevent respawn race
    update_daemon_config "$agent_type" 0

    # Get current sessions for this type
    local sessions
    sessions=$(get_sessions_for_type "$agent_type")

    if [[ -z "$sessions" ]]; then
        echo -e "${GREEN}No ${agent_type} agents currently running${NC}"
        return 0
    fi

    local count=0
    while IFS= read -r s; do
        [[ -n "$s" ]] && count=$((count + 1))
    done <<< "$sessions"

    echo -e "${BOLD}Stopping $count ${agent_type} agent(s)${NC}"

    if [[ "$force" == "true" ]]; then
        # Force stop: kill sessions directly
        while IFS= read -r session; do
            [[ -z "$session" ]] && continue
            echo -e "${BLUE}Killing $session...${NC}"
            kill_session_processes "$session"
        done <<< "$sessions"
        echo -e "${GREEN}${BOLD}All ${agent_type} agents killed${NC}"
    else
        # Graceful stop: create signal files, then wait with timeout
        local session_list=()
        while IFS= read -r session; do
            [[ -z "$session" ]] && continue
            signal_stop_session "$session"
            session_list+=("$session")
        done <<< "$sessions"
        echo -e "${GREEN}Signal files created for ${agent_type} agent(s)${NC}"

        # Also call sub-script graceful-stop API if available
        case "$agent_type" in
            enricher)
                if [[ -x "./scripts/enricher/parallel-enrich.sh" ]]; then
                    ./scripts/enricher/parallel-enrich.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
            aristotle)
                if [[ -x "./scripts/aristotle/launch-agent.sh" ]]; then
                    ./scripts/aristotle/launch-agent.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
            researcher)
                if [[ -x "./scripts/research/parallel-research.sh" ]]; then
                    ./scripts/research/parallel-research.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
            auditor)
                if [[ -x "./scripts/auditor/launch-agent.sh" ]]; then
                    ./scripts/auditor/launch-agent.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
            seeker)
                if [[ -x "./scripts/research/launch-seeker.sh" ]]; then
                    ./scripts/research/launch-seeker.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
            tester)
                if [[ -x "./scripts/test/launch-agent.sh" ]]; then
                    ./scripts/test/launch-agent.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
            herald)
                if [[ -x "./scripts/herald/launch-agent.sh" ]]; then
                    ./scripts/herald/launch-agent.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
            mechanic)
                if [[ -x "./scripts/mechanic/launch-agent.sh" ]]; then
                    ./scripts/mechanic/launch-agent.sh --graceful-stop 2>/dev/null || true
                fi
                ;;
        esac

        # Wait up to 60s for graceful shutdown, then force-kill
        wait_or_force_kill 60 "${session_list[@]}"
    fi
}

# Command: spawn
cmd_spawn() {
    local agent_type="${1:-}"

    if [[ -z "$agent_type" ]]; then
        echo -e "${RED}Error: Must specify agent type (enricher, aristotle, researcher, deployer, tester, herald)${NC}" >&2
        exit 1
    fi

    case "$agent_type" in
        enricher)
            echo -e "${BLUE}Spawning additional Enricher...${NC}"
            # Find next available slot
            for i in 1 2 3 4 5; do
                if ! tmux has-session -t "enricher-$i" 2>/dev/null; then
                    ./scripts/enricher/parallel-enrich.sh --slot "$i" &
                    sleep 2
                    echo -e "${GREEN}✓ Enricher spawned (slot $i)${NC}"
                    exit 0
                fi
            done
            echo -e "${YELLOW}All Enricher slots are full (max: $MAX_ENRICHER)${NC}"
            ;;
        aristotle)
            echo -e "${BLUE}Spawning Aristotle agent...${NC}"
            if tmux has-session -t "aristotle-agent" 2>/dev/null; then
                echo -e "${YELLOW}Aristotle agent already running${NC}"
            else
                # Manual spawn bypasses scale-to-zero (issue #22471).
                # Operator explicitly asked for an agent, so wipe the
                # marker and reset the idle clock so the new agent gets
                # a full cycle before any idle check can fire.
                if [[ -f "$ARISTOTLE_SCALED_MARKER" ]]; then
                    echo -e "${BLUE}  Clearing scale-to-zero marker (forced respawn)${NC}"
                    clear_aristotle_scaled_marker
                fi
                # Reset last-cycle timestamp so the new agent gets a
                # fresh idle-threshold window before scale-to-zero can re-fire.
                mkdir -p .loom/state
                touch .loom/state/aristotle-last-cycle 2>/dev/null || true
                ./scripts/aristotle/launch-agent.sh &
                sleep 1
                echo -e "${GREEN}✓ Aristotle agent spawned${NC}"
            fi
            ;;
        researcher)
            echo -e "${BLUE}Spawning additional Researcher...${NC}"
            for i in $(seq 1 $MAX_RESEARCHER); do
                if ! tmux has-session -t "researcher-$i" 2>/dev/null; then
                    ./scripts/research/parallel-research.sh --slot "$i" &
                    sleep 2
                    echo -e "${GREEN}✓ Researcher spawned (slot $i)${NC}"
                    exit 0
                fi
            done
            echo -e "${YELLOW}All Researcher slots are full (max: $MAX_RESEARCHER)${NC}"
            ;;
        seeker)
            echo -e "${BLUE}Spawning Seeker agent...${NC}"
            if tmux has-session -t "seeker-agent" 2>/dev/null; then
                echo -e "${YELLOW}Seeker agent already running${NC}"
            else
                ./scripts/research/launch-seeker.sh &
                sleep 1
                echo -e "${GREEN}✓ Seeker agent spawned${NC}"
            fi
            ;;
        deployer)
            echo -e "${BLUE}Spawning Deployer...${NC}"
            if tmux has-session -t "deployer" 2>/dev/null; then
                echo -e "${YELLOW}Deployer already running${NC}"
            else
                ./scripts/deploy/launch-agent.sh &
                sleep 1
                echo -e "${GREEN}✓ Deployer spawned${NC}"
            fi
            ;;
        tester)
            echo -e "${BLUE}Spawning Tester agent...${NC}"
            if tmux has-session -t "tester-agent" 2>/dev/null; then
                echo -e "${YELLOW}Tester agent already running${NC}"
            else
                ./scripts/test/launch-agent.sh &
                sleep 1
                echo -e "${GREEN}✓ Tester agent spawned${NC}"
            fi
            ;;
        herald)
            echo -e "${BLUE}Spawning Herald agent...${NC}"
            if tmux has-session -t "herald-agent" 2>/dev/null; then
                echo -e "${YELLOW}Herald agent already running${NC}"
            else
                ./scripts/herald/launch-agent.sh &
                sleep 1
                echo -e "${GREEN}✓ Herald agent spawned${NC}"
            fi
            ;;
        auditor)
            echo -e "${BLUE}Spawning additional Auditor...${NC}"
            for i in 1 2 3; do
                local sname="auditor-$i"
                if ! tmux has-session -t "$sname" 2>/dev/null; then
                    SESSION_NAME="$sname" ./scripts/auditor/launch-agent.sh &
                    sleep 2
                    echo -e "${GREEN}✓ Auditor spawned (slot $i)${NC}"
                    exit 0
                fi
            done
            # Check legacy singleton name too
            if tmux has-session -t "auditor-agent" 2>/dev/null; then
                echo -e "${YELLOW}All Auditor slots are full (max: $MAX_AUDITOR)${NC}"
            else
                SESSION_NAME="auditor-agent" ./scripts/auditor/launch-agent.sh &
                sleep 2
                echo -e "${GREEN}✓ Auditor spawned (legacy slot)${NC}"
            fi
            ;;
        mechanic)
            echo -e "${BLUE}Spawning additional Mechanic...${NC}"
            for i in 1 2 3; do
                local sname="mechanic-$i"
                if ! tmux has-session -t "$sname" 2>/dev/null; then
                    SESSION_NAME="$sname" ./scripts/mechanic/launch-agent.sh &
                    sleep 2
                    echo -e "${GREEN}✓ Mechanic spawned (slot $i)${NC}"
                    exit 0
                fi
            done
            # Check legacy singleton name too
            if tmux has-session -t "mechanic-agent" 2>/dev/null; then
                echo -e "${YELLOW}All Mechanic slots are full (max: $MAX_MECHANIC)${NC}"
            else
                SESSION_NAME="mechanic-agent" ./scripts/mechanic/launch-agent.sh &
                sleep 2
                echo -e "${GREEN}✓ Mechanic spawned (legacy slot)${NC}"
            fi
            ;;
        peer-reviewer)
            echo -e "${BLUE}Spawning Peer Reviewer...${NC}"
            for i in 1 2; do
                if ! tmux has-session -t "peer-reviewer-$i" 2>/dev/null; then
                    ./scripts/peer-reviewer/launch-agent.sh --slot "$i" &
                    sleep 2
                    echo -e "${GREEN}✓ Peer Reviewer spawned (slot $i)${NC}"
                    exit 0
                fi
            done
            echo -e "${YELLOW}All Peer Reviewer slots are full (max: 2)${NC}"
            ;;
        *)
            echo -e "${RED}Unknown agent type: $agent_type${NC}" >&2
            echo "Valid types: enricher, aristotle, researcher, auditor, mechanic, seeker, deployer, tester, herald, peer-reviewer"
            exit 1
            ;;
    esac
}

# Helper: Scale down multi-instance agents (enricher, researcher)
# Stops highest-numbered slots first to reach target count
scale_down_multi() {
    local agent_type="$1"
    local prefix="$2"
    local current="$3"
    local target="$4"

    local to_remove=$((current - target))
    echo -e "${BLUE}Scaling ${agent_type}s from $current to $target (removing $to_remove)...${NC}"

    # Update daemon state FIRST to prevent respawn race
    update_daemon_config "$agent_type" "$target"

    # Stop highest-numbered slots first
    local sessions_to_stop=()
    for i in 5 4 3 2 1; do
        [[ ${#sessions_to_stop[@]} -ge $to_remove ]] && break
        if tmux has-session -t "${prefix}-$i" 2>/dev/null; then
            signal_stop_session "${prefix}-$i"
            sessions_to_stop+=("${prefix}-$i")
            echo -e "  Signaling ${prefix}-$i to stop"
        fi
    done

    # Wait up to 60s for graceful shutdown, then force-kill
    if [[ ${#sessions_to_stop[@]} -gt 0 ]]; then
        wait_or_force_kill 60 "${sessions_to_stop[@]}"
    fi

    echo -e "${GREEN}✓ Scaled to $target ${agent_type}(s)${NC}"
}

# Command: scale
cmd_scale() {
    local agent_type="${1:-}"
    local count="${2:-}"

    if [[ -z "$agent_type" || -z "$count" ]]; then
        echo -e "${RED}Error: Must specify agent type and count${NC}" >&2
        echo "Usage: $0 scale <enricher|researcher|aristotle|seeker|deployer> <count>"
        exit 1
    fi

    case "$agent_type" in
        enricher)
            if [[ $count -gt $MAX_ENRICHER ]]; then
                echo -e "${YELLOW}Count $count exceeds max $MAX_ENRICHER, using $MAX_ENRICHER${NC}"
                count=$MAX_ENRICHER
            fi

            # Count current
            local current=0
            for i in 1 2 3 4 5; do
                if tmux has-session -t "enricher-$i" 2>/dev/null; then
                    current=$((current + 1))
                fi
            done

            if [[ $count -gt $current ]]; then
                local to_add=$((count - current))
                echo -e "${BLUE}Scaling Enrichers from $current to $count (adding $to_add)...${NC}"
                update_daemon_config "enricher" "$count"
                local added=0
                for i in 1 2 3 4 5; do
                    [[ $added -ge $to_add ]] && break
                    if ! tmux has-session -t "enricher-$i" 2>/dev/null; then
                        ./scripts/enricher/parallel-enrich.sh --slot "$i" &
                        sleep 2
                        added=$((added + 1))
                    fi
                done
                echo -e "${GREEN}✓ Scaled to $count Enrichers${NC}"
            elif [[ $count -lt $current ]]; then
                scale_down_multi "enricher" "enricher" "$current" "$count"
            else
                echo -e "${GREEN}Already at $count Enrichers${NC}"
            fi
            ;;
        researcher)
            if [[ $count -gt $MAX_RESEARCHER ]]; then
                echo -e "${YELLOW}Count $count exceeds max $MAX_RESEARCHER, using $MAX_RESEARCHER${NC}"
                count=$MAX_RESEARCHER
            fi

            local current=0
            for i in $(seq 1 $MAX_RESEARCHER); do
                if tmux has-session -t "researcher-$i" 2>/dev/null; then
                    current=$((current + 1))
                fi
            done

            if [[ $count -gt $current ]]; then
                local to_add=$((count - current))
                echo -e "${BLUE}Scaling Researchers from $current to $count (adding $to_add)...${NC}"
                update_daemon_config "researcher" "$count"
                local added=0
                for i in $(seq 1 $MAX_RESEARCHER); do
                    [[ $added -ge $to_add ]] && break
                    if ! tmux has-session -t "researcher-$i" 2>/dev/null; then
                        ./scripts/research/parallel-research.sh --slot "$i" &
                        sleep 2
                        added=$((added + 1))
                    fi
                done
                echo -e "${GREEN}✓ Scaled to $count Researchers${NC}"
            elif [[ $count -lt $current ]]; then
                scale_down_multi "researcher" "researcher" "$current" "$count"
            else
                echo -e "${GREEN}Already at $count Researchers${NC}"
            fi
            ;;
        mechanic)
            if [[ $count -gt $MAX_MECHANIC ]]; then
                echo -e "${YELLOW}Count $count exceeds max $MAX_MECHANIC, using $MAX_MECHANIC${NC}"
                count=$MAX_MECHANIC
            fi

            local current=0
            for i in 1 2 3; do
                if tmux has-session -t "mechanic-$i" 2>/dev/null; then
                    current=$((current + 1))
                fi
            done
            if tmux has-session -t "mechanic-agent" 2>/dev/null; then
                current=$((current + 1))
            fi

            if [[ $count -gt $current ]]; then
                local to_add=$((count - current))
                echo -e "${BLUE}Scaling Mechanics from $current to $count (adding $to_add)...${NC}"
                update_daemon_config "mechanic" "$count"
                local added=0
                for i in 1 2 3; do
                    [[ $added -ge $to_add ]] && break
                    if ! tmux has-session -t "mechanic-$i" 2>/dev/null; then
                        SESSION_NAME="mechanic-$i" ./scripts/mechanic/launch-agent.sh &
                        sleep 2
                        added=$((added + 1))
                    fi
                done
                echo -e "${GREEN}✓ Scaled to $count Mechanics${NC}"
            elif [[ $count -lt $current ]]; then
                scale_down_multi "mechanic" "mechanic" "$current" "$count"
            else
                echo -e "${GREEN}Already at $count Mechanics${NC}"
            fi
            ;;
        auditor|aristotle|seeker|deployer|tester|herald)
            if [[ $count -gt 1 ]]; then
                echo -e "${YELLOW}$agent_type can only have 0 or 1 instance, using 1${NC}"
                count=1
            fi

            local current_sessions
            current_sessions=$(get_sessions_for_type "$agent_type")
            local current_count=0
            if [[ -n "$current_sessions" ]]; then
                current_count=$(echo "$current_sessions" | wc -l | tr -d ' ')
            fi

            if [[ $count -eq 0 ]]; then
                if [[ $current_count -eq 0 ]]; then
                    echo -e "${GREEN}No ${agent_type} agents running${NC}"
                else
                    echo -e "${BLUE}Scaling ${agent_type} from $current_count to 0...${NC}"
                    cmd_stop_type "$agent_type" "false"
                fi
            elif [[ $count -eq 1 && $current_count -eq 0 ]]; then
                echo -e "${BLUE}Scaling ${agent_type} from 0 to 1...${NC}"
                update_daemon_config "$agent_type" 1
                cmd_spawn "$agent_type"
            else
                echo -e "${GREEN}Already at $count ${agent_type}${NC}"
            fi
            ;;
        *)
            echo -e "${RED}Unknown agent type: $agent_type${NC}" >&2
            echo "Valid types: enricher, researcher, mechanic, aristotle, auditor, seeker, deployer, tester, herald"
            exit 1
            ;;
    esac
}

# Command: wake - signal sleeping agent(s) to start their next cycle early
cmd_wake() {
    local agent_type="${1:-all}"

    mkdir -p "$SIGNALS_DIR"

    case "$agent_type" in
        all)
            touch "$SIGNALS_DIR/wake-all"
            echo -e "${GREEN}Wake signal sent to all agents${NC}"
            ;;
        aristotle)
            touch "$SIGNALS_DIR/wake-aristotle"
            echo -e "${GREEN}Wake signal sent to aristotle-agent${NC}"
            ;;
        researcher)
            for i in $(seq 1 $MAX_RESEARCHER); do
                if tmux has-session -t "researcher-$i" 2>/dev/null; then
                    touch "$SIGNALS_DIR/wake-researcher-$i"
                    echo -e "${GREEN}Wake signal sent to researcher-$i${NC}"
                fi
            done
            ;;
        auditor)
            touch "$SIGNALS_DIR/wake-auditor-agent"
            echo -e "${GREEN}Wake signal sent to auditor-agent${NC}"
            ;;
        deployer)
            touch "$SIGNALS_DIR/wake-deployer"
            echo -e "${GREEN}Wake signal sent to deployer${NC}"
            ;;
        seeker)
            touch "$SIGNALS_DIR/wake-seeker-agent"
            echo -e "${GREEN}Wake signal sent to seeker-agent${NC}"
            ;;
        enricher)
            for i in 1 2 3 4 5; do
                if tmux has-session -t "enricher-$i" 2>/dev/null; then
                    touch "$SIGNALS_DIR/wake-enricher-$i"
                    echo -e "${GREEN}Wake signal sent to enricher-$i${NC}"
                fi
            done
            ;;
        tester)
            touch "$SIGNALS_DIR/wake-tester-agent"
            echo -e "${GREEN}Wake signal sent to tester-agent${NC}"
            ;;
        herald)
            touch "$SIGNALS_DIR/wake-herald-agent"
            echo -e "${GREEN}Wake signal sent to herald-agent${NC}"
            ;;
        mechanic)
            for i in 1 2 3; do
                if tmux has-session -t "mechanic-$i" 2>/dev/null; then
                    touch "$SIGNALS_DIR/wake-mechanic-$i"
                    echo -e "${GREEN}Wake signal sent to mechanic-$i${NC}"
                fi
            done
            if tmux has-session -t "mechanic-agent" 2>/dev/null; then
                touch "$SIGNALS_DIR/wake-mechanic-agent"
                echo -e "${GREEN}Wake signal sent to mechanic-agent${NC}"
            fi
            ;;
        *)
            echo -e "${RED}Unknown agent type: $agent_type${NC}" >&2
            echo "Valid types: all, aristotle, researcher, auditor, mechanic, deployer, seeker, enricher, tester, herald"
            exit 1
            ;;
    esac
}

# Command: status
cmd_status() {
    ./scripts/lean/status.sh
}

# Main
main() {
    local cmd="${1:-}"

    case "$cmd" in
        start)
            shift
            cmd_start "$@"
            ;;
        stop)
            shift
            cmd_stop "$@"
            ;;
        health)
            cmd_health
            ;;
        spawn)
            shift
            cmd_spawn "$@"
            ;;
        scale)
            shift
            cmd_scale "$@"
            ;;
        status)
            cmd_status
            ;;
        wake)
            shift
            cmd_wake "$@"
            ;;
        daemon)
            shift
            cmd_daemon "$@"
            ;;
        -h|--help|help)
            usage
            ;;
        "")
            # Default: show status
            cmd_status
            ;;
        *)
            echo -e "${RED}Unknown command: $cmd${NC}" >&2
            usage
            exit 1
            ;;
    esac
}

# Only run main when executed directly, not when sourced (e.g. by tests such as
# scripts/tests/daemon-missing-agent.test.sh, which exercise the missing-session
# detection helpers in isolation). #39652.
if [[ "${BASH_SOURCE[0]}" == "${0}" ]]; then
    main "$@"
fi
