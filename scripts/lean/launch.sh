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

# Health check thresholds
STUCK_THRESHOLD_MINUTES=30
STUCK_CPU_THRESHOLD="0.5"
# Agent statuses: RUNNING, COMPLETED, STUCK, IDLE, UNKNOWN
# IDLE = polling agent (deployer/seeker) that is healthy but waiting between cycles

# Daemon defaults
DEFAULT_DAEMON_INTERVAL=60
RESPAWN_COOLDOWN_SECONDS=300  # 5 minutes between respawns of same agent

# Default pool sizes
# Balanced team: 5 researchers (continuous), 8 support agents (sleeping between cycles)
# ~72 active min/hr across 9 accounts = ~8 min/hr per account
DEFAULT_ENRICHER=1
DEFAULT_ARISTOTLE=1
DEFAULT_RESEARCHER=5
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
  $0 start --enricher 2 --researcher 1  # Include Enrichers
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
                    tmux kill-session -t "$session" 2>/dev/null || true
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

# Helper: Kill all processes in a tmux session before destroying it.
# This prevents orphaned claude/timeout processes when tmux SIGHUP
# doesn't propagate across process group boundaries.
kill_session_processes() {
    local session="$1"

    # Find and kill claude process before destroying the session
    local pane_pid
    pane_pid=$(tmux list-panes -t "$session" -F '#{pane_pid}' 2>/dev/null | head -1)

    if [[ -n "$pane_pid" ]]; then
        # Kill entire process tree under the pane
        local children
        children=$(pgrep -P "$pane_pid" 2>/dev/null || true)
        if [[ -n "$children" ]]; then
            echo "$children" | xargs kill 2>/dev/null || true
        fi
        # Also kill the pane process itself
        kill "$pane_pid" 2>/dev/null || true
    fi

    # Now kill the tmux session
    tmux kill-session -t "$session" 2>/dev/null || true

    # Brief wait for processes to exit
    sleep 1
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

# Command: health - Show agent process health
cmd_health() {
    echo -e "${BOLD}Agent Health Check${NC}"
    echo ""

    local sessions
    sessions=$(get_all_agent_sessions)

    if [[ -z "$sessions" ]]; then
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

    echo ""
    local summary="Summary: ${GREEN}$running_count running${NC}, ${completed_count} completed"
    if [[ $idle_count -gt 0 ]]; then
        summary+=", ${BLUE}$idle_count idle${NC}"
    fi
    if [[ $failing_count -gt 0 ]]; then
        summary+=", ${RED}$failing_count failing${NC}"
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

# Helper: Daemon log with timestamp
daemon_log() {
    local level="$1"
    shift
    local msg="$*"
    local timestamp
    timestamp=$(date -u +"%Y-%m-%dT%H:%M:%SZ")
    echo "[$timestamp] $level: $msg"
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
            local worktree_dir=".loom/worktrees/enricher-$agent_num"
            local branch="feature/enricher-$agent_num"
            local enricher_id="enricher-$agent_num"
            local log_file=".loom/logs/$session.log"
            local prompt_file=".loom/logs/$session-prompt.md"
            local repo_root
            repo_root=$(pwd)

            # Recreate worktree from current main
            if [[ -d "$worktree_dir" ]]; then
                git worktree remove "$worktree_dir" --force 2>/dev/null || rm -rf "$worktree_dir"
            fi
            git branch -D "$branch" 2>/dev/null || true
            git worktree add "$worktree_dir" -b "$branch" main 2>/dev/null || {
                daemon_log "WARN" "Cannot create worktree for $session"
                return
            }
            if [[ -f "$worktree_dir/.gitmodules" ]]; then
                (cd "$worktree_dir" && git submodule update --init --recursive 2>/dev/null) || true
            fi

            # Create tmux session and launch Claude
            tmux new-session -d -s "$session" -c "$repo_root/$worktree_dir"
            sleep 0.3
            tmux send-keys -t "$session" "export ENRICHER_ID='$enricher_id'" Enter
            sleep 0.2
            tmux send-keys -t "$session" "export REPO_ROOT='$repo_root'" Enter
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
            local worktree_dir=".loom/worktrees/researcher-$agent_num"
            local branch="feature/researcher-$agent_num"
            local log_file=".loom/logs/$session.log"
            local prompt_file=".loom/logs/$session-prompt.md"
            local repo_root
            repo_root=$(pwd)

            # Recreate worktree from current main
            if [[ -d "$worktree_dir" ]]; then
                git worktree remove "$worktree_dir" --force 2>/dev/null || rm -rf "$worktree_dir"
            fi
            git branch -D "$branch" 2>/dev/null || true
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
            tmux new-session -d -s "$session" -c "$repo_root/$worktree_dir"
            sleep 0.3
            tmux send-keys -t "$session" "export ENHANCER_ID='researcher-$agent_num'" Enter
            sleep 0.2
            tmux send-keys -t "$session" "export REPO_ROOT='$repo_root'" Enter
            sleep 0.2
            tmux send-keys -t "$session" "export CLAUDE_TIMEOUT=14400" Enter
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

    # PRs ready to merge
    ready_prs=$(timeout 10 gh pr list --label "loom:pr" --json number 2>/dev/null | jq 'length' 2>/dev/null || echo "0")

    echo "$enrichment_targets $candidates $aristotle_jobs $aristotle_candidates $ready_prs"
}

# Helper: Write daemon state to state file
update_daemon_state() {
    local cycle_count="$1"
    local respawn_count="$2"

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
    # Ensure completions directory exists
    mkdir -p "$COMPLETIONS_DIR/archive"

    local enriched=0
    local proofs=0
    local integrated=0
    local selected=0
    local deploys=0
    local researched=0

    # Count signals by type (use find to avoid glob expansion issues)
    enriched=$(find "$COMPLETIONS_DIR" -maxdepth 1 -name 'enrichment-completed-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    proofs=$(find "$COMPLETIONS_DIR" -maxdepth 1 -name 'proof-submitted-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    integrated=$(find "$COMPLETIONS_DIR" -maxdepth 1 -name 'proof-integrated-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    selected=$(find "$COMPLETIONS_DIR" -maxdepth 1 -name 'problem-selected-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    deploys=$(find "$COMPLETIONS_DIR" -maxdepth 1 -name 'deployment-*' -type f 2>/dev/null | wc -l | tr -d ' ')
    researched=$(find "$COMPLETIONS_DIR" -maxdepth 1 -name 'research-completed-*' -type f 2>/dev/null | wc -l | tr -d ' ')

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
        find "$COMPLETIONS_DIR" -maxdepth 1 -type f -name 'enrichment-completed-*' -exec mv {} "$COMPLETIONS_DIR/archive/" \; 2>/dev/null || true
        find "$COMPLETIONS_DIR" -maxdepth 1 -type f -name 'proof-submitted-*' -exec mv {} "$COMPLETIONS_DIR/archive/" \; 2>/dev/null || true
        find "$COMPLETIONS_DIR" -maxdepth 1 -type f -name 'proof-integrated-*' -exec mv {} "$COMPLETIONS_DIR/archive/" \; 2>/dev/null || true
        find "$COMPLETIONS_DIR" -maxdepth 1 -type f -name 'problem-selected-*' -exec mv {} "$COMPLETIONS_DIR/archive/" \; 2>/dev/null || true
        find "$COMPLETIONS_DIR" -maxdepth 1 -type f -name 'deployment-*' -exec mv {} "$COMPLETIONS_DIR/archive/" \; 2>/dev/null || true
        find "$COMPLETIONS_DIR" -maxdepth 1 -type f -name 'research-completed-*' -exec mv {} "$COMPLETIONS_DIR/archive/" \; 2>/dev/null || true
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
    mkdir -p "$COMPLETIONS_DIR/archive"

    # Write PID file
    mkdir -p "$(dirname "$DAEMON_PID_FILE")"
    echo $$ > "$DAEMON_PID_FILE"

    # Set up signal handlers for clean shutdown
    trap daemon_cleanup EXIT
    trap 'daemon_log "INFO" "Received SIGTERM"; exit 0' TERM
    trap 'daemon_log "INFO" "Received SIGINT"; exit 0' INT

    daemon_log "INFO" "Starting daemon (PID $$, interval ${interval}s, monitor_only=$monitor_only)"
    daemon_log "INFO" "Pool config: enricher=$enricher, aristotle=$aristotle, researcher=$researcher, auditor=$auditor, seeker=$seeker, deployer=$deployer, tester=$tester, herald=$herald, mechanic=$mechanic"

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

        # 2. Health check all agent sessions
        local sessions
        sessions=$(get_all_agent_sessions)

        if [[ -z "$sessions" ]]; then
            daemon_log "WARN" "No agent sessions found, cycle $cycle_count"
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
        # exits entirely, the health check above never sees it)

        # Re-read target config from state file each cycle.
        # This ensures scale-down / stop commands are respected by the daemon
        # without needing to restart it.
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
            daemon_log "INFO" "Pool gap: aristotle has 0/$aristotle, spawning"
            if respawn_agent "aristotle-agent"; then
                total_respawns=$((total_respawns + 1))
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

        # 3. Work queue assessment (with timeout protection)
        local queue_stats
        queue_stats=$(get_work_queue_stats)
        local enrichment_targets candidates aristotle_jobs aristotle_candidates ready_prs
        read -r enrichment_targets candidates aristotle_jobs aristotle_candidates ready_prs <<< "$queue_stats"

        # 4. Process completion signals and update session stats
        process_completion_signals

        # 4b. Dynamic Aristotle: spawn when candidates or jobs exist but no agent running
        if [[ $aristotle_active -eq 0 ]] && [[ "$aristotle_jobs" -gt 0 || "$aristotle_candidates" -gt 0 ]]; then
            if is_cooldown_elapsed "aristotle-agent"; then
                daemon_log "INFO" "Auto-spawning Aristotle: $aristotle_jobs pending jobs, $aristotle_candidates candidates"
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
            tmux kill-session -t "lean-daemon" 2>/dev/null || true
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
            tmux kill-session -t "seeker-agent" 2>/dev/null || true
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

        # Kill timeout wrappers around agent processes
        pkill -f 'timeout.*claude -p.*dangerously-skip-permissions' 2>/dev/null || true

        # Kill claude-wrapper.sh scripts
        pkill -f 'claude-wrapper.sh.*\(researcher\|enricher\|deployer\|seeker\|aristotle\|auditor\|mechanic\|herald\|tester\)' 2>/dev/null || true

        # Kill aristotle-agent.sh
        pkill -f 'aristotle-agent.sh' 2>/dev/null || true

        # Brief wait, then force-kill any survivors
        sleep 2
        local survivors
        survivors=$(ps aux | grep '[c]laude -p.*dangerously-skip-permissions.*\(researcher\|enricher\|deployer\|seeker\|aristotle\|auditor\|mechanic\|herald\|tester\)' | awk '{print $2}')
        if [[ -n "$survivors" ]]; then
            local survivor_count
            survivor_count=$(echo "$survivors" | wc -l | tr -d ' ')
            echo -e "  Force-killing $survivor_count surviving process(es)"
            echo "$survivors" | xargs kill -9 2>/dev/null || true
            pkill -9 -f 'timeout.*claude -p.*dangerously-skip-permissions' 2>/dev/null || true
            pkill -9 -f 'claude-wrapper.sh.*\(researcher\|enricher\|deployer\|seeker\|aristotle\|auditor\|mechanic\|herald\|tester\)' 2>/dev/null || true
        else
            echo -e "  ${GREEN}All agent processes confirmed dead${NC}"
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
            tmux kill-session -t "$session" 2>/dev/null || true
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

main "$@"
