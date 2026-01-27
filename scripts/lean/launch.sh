#!/usr/bin/env bash
#
# Lean Genius Launch - Start/stop/scale the mathematical agent team
#
# Usage:
#   ./scripts/lean/launch.sh start [--erdos N] [--aristotle N] [--researcher N] [--deployer N]
#   ./scripts/lean/launch.sh stop [--force]
#   ./scripts/lean/launch.sh health
#   ./scripts/lean/launch.sh spawn erdos|aristotle|researcher|deployer
#   ./scripts/lean/launch.sh scale erdos|researcher N
#   ./scripts/lean/launch.sh status
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
STATE_FILE="research/lean-daemon-state.json"
SIGNALS_DIR=".loom/signals"

# Health check thresholds
STUCK_THRESHOLD_MINUTES=30
STUCK_CPU_THRESHOLD="0.5"

# Default pool sizes
DEFAULT_ERDOS=2
DEFAULT_ARISTOTLE=1
DEFAULT_RESEARCHER=1
DEFAULT_DEPLOYER=1

# Max pool sizes
MAX_ERDOS=5
MAX_ARISTOTLE=2
MAX_RESEARCHER=3
MAX_DEPLOYER=1

# Helper: Print usage
usage() {
    cat <<EOF
Lean Genius Launch - Mathematical Agent Orchestration

Usage:
  $0 start [options]     Start agents with specified pool sizes
  $0 stop [--force]      Stop all agents (graceful by default, --force kills immediately)
  $0 health              Show agent process health and detect stuck agents
  $0 spawn <type>        Spawn one additional agent
  $0 scale <type> <N>    Scale agent pool to N instances
  $0 status              Show current status

Start Options:
  --erdos N              Number of Erdős enhancers (default: $DEFAULT_ERDOS, max: $MAX_ERDOS)
  --aristotle N          Number of Aristotle agents (default: $DEFAULT_ARISTOTLE, max: $MAX_ARISTOTLE)
  --researcher N         Number of Researchers (default: $DEFAULT_RESEARCHER, max: $MAX_RESEARCHER)
  --deployer N           Number of Deployers (default: $DEFAULT_DEPLOYER, max: $MAX_DEPLOYER)

Stop Options:
  --force                Kill tmux sessions immediately (skip graceful signal files)

Agent Types:
  erdos       Enhances Erdős problem stubs with Lean formalizations
  aristotle   Manages proof search queue for Aristotle system
  researcher  Works on open mathematical problems
  deployer    Merges PRs and deploys website

Examples:
  $0 start                              # Start with defaults
  $0 start --erdos 3 --researcher 2     # Custom pool sizes
  $0 spawn erdos                        # Add one Erdős enhancer
  $0 scale erdos 4                      # Scale to 4 enhancers
  $0 stop                               # Graceful stop (signal files)
  $0 stop --force                       # Force stop (kill sessions)
  $0 health                             # Check agent health
EOF
}

# Helper: Initialize state file
init_state() {
    local erdos="${1:-$DEFAULT_ERDOS}"
    local aristotle="${2:-$DEFAULT_ARISTOTLE}"
    local researcher="${3:-$DEFAULT_RESEARCHER}"
    local deployer="${4:-$DEFAULT_DEPLOYER}"

    mkdir -p "$(dirname "$STATE_FILE")"

    cat > "$STATE_FILE" <<EOF
{
  "started_at": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "running": true,
  "config": {
    "erdos": $erdos,
    "aristotle": $aristotle,
    "researcher": $researcher,
    "deployer": $deployer
  },
  "agents": {},
  "session_stats": {
    "stubs_enhanced": 0,
    "proofs_submitted": 0,
    "proofs_integrated": 0,
    "deployments": 0
  }
}
EOF
}

# Helper: Update state running flag
set_running() {
    local running="$1"
    if [[ -f "$STATE_FILE" ]]; then
        local tmp
        tmp=$(mktemp)
        jq ".running = $running" "$STATE_FILE" > "$tmp" && mv "$tmp" "$STATE_FILE"
    fi
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
    local erdos=$DEFAULT_ERDOS
    local aristotle=$DEFAULT_ARISTOTLE
    local researcher=$DEFAULT_RESEARCHER
    local deployer=$DEFAULT_DEPLOYER

    # Parse options
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --erdos)
                erdos="$2"
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
            --deployer)
                deployer="$2"
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
    if [[ $erdos -gt $MAX_ERDOS ]]; then
        echo -e "${YELLOW}Warning: Erdős count $erdos exceeds max $MAX_ERDOS, using $MAX_ERDOS${NC}"
        erdos=$MAX_ERDOS
    fi
    if [[ $aristotle -gt $MAX_ARISTOTLE ]]; then
        echo -e "${YELLOW}Warning: Aristotle count $aristotle exceeds max $MAX_ARISTOTLE, using $MAX_ARISTOTLE${NC}"
        aristotle=$MAX_ARISTOTLE
    fi
    if [[ $researcher -gt $MAX_RESEARCHER ]]; then
        echo -e "${YELLOW}Warning: Researcher count $researcher exceeds max $MAX_RESEARCHER, using $MAX_RESEARCHER${NC}"
        researcher=$MAX_RESEARCHER
    fi
    if [[ $deployer -gt $MAX_DEPLOYER ]]; then
        echo -e "${YELLOW}Warning: Deployer count $deployer exceeds max $MAX_DEPLOYER, using $MAX_DEPLOYER${NC}"
        deployer=$MAX_DEPLOYER
    fi

    echo -e "${BOLD}Starting Lean Genius Mathematical Orchestration${NC}"
    echo ""
    echo -e "Configuration:"
    echo "  Erdős Enhancers: $erdos"
    echo "  Aristotle Agents: $aristotle"
    echo "  Researchers: $researcher"
    echo "  Deployers: $deployer"
    echo ""

    # Initialize state
    init_state "$erdos" "$aristotle" "$researcher" "$deployer"

    # Start agents
    local started=0

    # Erdős enhancers
    if [[ $erdos -gt 0 ]]; then
        echo -e "${BLUE}Starting $erdos Erdős enhancer(s)...${NC}"
        if check_script "./scripts/erdos/parallel-enhance.sh"; then
            ./scripts/erdos/parallel-enhance.sh "$erdos" &
            sleep 2
            echo -e "${GREEN}✓ Erdős enhancers launched${NC}"
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
    # Erdős enhancers
    for i in 1 2 3 4 5; do
        if tmux has-session -t "erdos-enhancer-$i" 2>/dev/null; then
            sessions+=("erdos-enhancer-$i")
        fi
    done
    # Aristotle
    if tmux has-session -t "aristotle-agent" 2>/dev/null; then
        sessions+=("aristotle-agent")
    fi
    # Researchers
    for i in 1 2 3; do
        if tmux has-session -t "researcher-$i" 2>/dev/null; then
            sessions+=("researcher-$i")
        fi
    done
    # Deployer
    if tmux has-session -t "deployer" 2>/dev/null; then
        sessions+=("deployer")
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
# Outputs the PID of the first claude child/grandchild found, or nothing
find_claude_child() {
    local parent_pid="$1"
    local children
    children=$(pgrep -P "$parent_pid" 2>/dev/null) || true

    if [[ -z "$children" ]]; then
        return 0
    fi

    local child
    while IFS= read -r child; do
        [[ -z "$child" ]] && continue
        local cmd
        cmd=$(ps -o comm= -p "$child" 2>/dev/null || true)
        if [[ "$cmd" == *claude* ]]; then
            echo "$child"
            return 0
        fi
        # Also check grandchildren (claude may be launched via wrapper)
        local grandchildren
        grandchildren=$(pgrep -P "$child" 2>/dev/null) || true
        if [[ -n "$grandchildren" ]]; then
            local grandchild
            while IFS= read -r grandchild; do
                [[ -z "$grandchild" ]] && continue
                local gcmd
                gcmd=$(ps -o comm= -p "$grandchild" 2>/dev/null || true)
                if [[ "$gcmd" == *claude* ]]; then
                    echo "$grandchild"
                    return 0
                fi
            done <<< "$grandchildren"
        fi
    done <<< "$children"
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

# Helper: Determine agent health status
# Returns: RUNNING, COMPLETED, STUCK, or UNKNOWN
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

    # Find claude child process
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
            echo "STUCK"
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
    printf "%-22s %-8s %-10s %-7s %-5s %-10s\n" "Agent" "PID" "Elapsed" "CPU" "Net" "Status"
    printf "%-22s %-8s %-10s %-7s %-5s %-10s\n" "-----" "---" "-------" "---" "---" "------"

    local stuck_count=0
    local running_count=0
    local completed_count=0

    while IFS= read -r session; do
        [[ -z "$session" ]] && continue

        local pane_pid
        pane_pid=$(get_pane_pid "$session")

        if [[ -z "$pane_pid" ]]; then
            printf "%-22s %-8s %-10s %-7s %-5s %-10s\n" "$session" "-" "-" "-" "-" "NO PANE"
            continue
        fi

        # Find claude child
        local claude_pid
        claude_pid=$(find_claude_child "$pane_pid" | head -1)

        local status
        status=$(get_agent_status "$session")

        if [[ -z "$claude_pid" ]]; then
            # No claude process
            local status_display
            if [[ "$status" == "COMPLETED" ]]; then
                status_display="${GREEN}COMPLETED${NC}"
                completed_count=$((completed_count + 1))
            else
                status_display="${YELLOW}$status${NC}"
            fi
            printf "%-22s %-8s %-10s %-7s %-5s " "$session" "-" "-" "-" "-"
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
                RUNNING)
                    status_display="${GREEN}RUNNING${NC}"
                    running_count=$((running_count + 1))
                    ;;
                *)
                    status_display="${YELLOW}$status${NC}"
                    ;;
            esac

            printf "%-22s %-8s %-10s %-7s %-5s " "$session" "$claude_pid" "$elapsed_human" "${cpu}%" "$net_status"
            echo -e "$status_display"
        fi
    done <<< "$sessions"

    echo ""
    echo -e "Summary: ${GREEN}$running_count running${NC}, ${completed_count} completed, ${RED}$stuck_count stuck${NC}"

    if [[ $stuck_count -gt 0 ]]; then
        echo ""
        echo -e "${YELLOW}Stuck agents detected. Use './scripts/lean/launch.sh stop --force' to kill them.${NC}"
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

# Command: stop (graceful by default, --force for immediate kill)
cmd_stop() {
    local force=false

    # Parse stop options
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --force|-f)
                force=true
                shift
                ;;
            *)
                echo -e "${RED}Unknown stop option: $1${NC}" >&2
                echo "Usage: $0 stop [--force]"
                exit 1
                ;;
        esac
    done

    if [[ "$force" == "true" ]]; then
        echo -e "${BOLD}Force-Stopping Lean Genius Mathematical Orchestration${NC}"
        echo ""

        local stopped=0

        # Force stop: kill tmux sessions directly
        echo -e "${BLUE}Killing Erdős enhancer sessions...${NC}"
        if [[ -x "./scripts/erdos/parallel-enhance.sh" ]]; then
            ./scripts/erdos/parallel-enhance.sh --stop 2>/dev/null || true
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

        echo -e "${BLUE}Killing Deployer session...${NC}"
        if [[ -x "./scripts/deploy/launch-agent.sh" ]]; then
            ./scripts/deploy/launch-agent.sh --stop 2>/dev/null || true
            stopped=$((stopped + 1))
        fi

        # Update state
        set_running false

        # Create stop signal file
        touch research/lean-stop-daemon 2>/dev/null || true

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
        echo -e "${BLUE}Signaling Erdős enhancers...${NC}"
        if [[ -x "./scripts/erdos/parallel-enhance.sh" ]]; then
            ./scripts/erdos/parallel-enhance.sh --graceful-stop 2>/dev/null || true
        fi

        echo -e "${BLUE}Signaling Aristotle agent...${NC}"
        if [[ -x "./scripts/aristotle/launch-agent.sh" ]]; then
            ./scripts/aristotle/launch-agent.sh --graceful-stop 2>/dev/null || true
        fi

        echo -e "${BLUE}Signaling Researchers...${NC}"
        if [[ -x "./scripts/research/parallel-research.sh" ]]; then
            ./scripts/research/parallel-research.sh --graceful-stop 2>/dev/null || true
        fi

        echo -e "${BLUE}Signaling Deployer...${NC}"
        # Deployer's --stop already creates signal + kills, so just create signal
        touch "$SIGNALS_DIR/stop-deployer" 2>/dev/null || true

        # Update state
        set_running false

        # Create stop signal file
        touch research/lean-stop-daemon 2>/dev/null || true

        echo ""
        echo -e "${GREEN}${BOLD}Signal files created for graceful shutdown${NC}"
        echo ""
        echo "Agents will finish their current work before stopping."
        echo "Use './scripts/lean/status.sh' to monitor shutdown progress."

        # Check for stuck agents and warn
        check_for_stuck_agents || true
    fi
}

# Command: spawn
cmd_spawn() {
    local agent_type="${1:-}"

    if [[ -z "$agent_type" ]]; then
        echo -e "${RED}Error: Must specify agent type (erdos, aristotle, researcher, deployer)${NC}" >&2
        exit 1
    fi

    case "$agent_type" in
        erdos)
            echo -e "${BLUE}Spawning additional Erdős enhancer...${NC}"
            # Find next available slot
            for i in 1 2 3 4 5; do
                if ! tmux has-session -t "erdos-enhancer-$i" 2>/dev/null; then
                    # Spawn single enhancer
                    ./scripts/erdos/parallel-enhance.sh 1 &
                    sleep 2
                    echo -e "${GREEN}✓ Erdős enhancer spawned${NC}"
                    exit 0
                fi
            done
            echo -e "${YELLOW}All Erdős slots are full (max: $MAX_ERDOS)${NC}"
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
            for i in 1 2 3; do
                if ! tmux has-session -t "researcher-$i" 2>/dev/null; then
                    ./scripts/research/parallel-research.sh 1 &
                    sleep 2
                    echo -e "${GREEN}✓ Researcher spawned${NC}"
                    exit 0
                fi
            done
            echo -e "${YELLOW}All Researcher slots are full (max: $MAX_RESEARCHER)${NC}"
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
        *)
            echo -e "${RED}Unknown agent type: $agent_type${NC}" >&2
            echo "Valid types: erdos, aristotle, researcher, deployer"
            exit 1
            ;;
    esac
}

# Command: scale
cmd_scale() {
    local agent_type="${1:-}"
    local count="${2:-}"

    if [[ -z "$agent_type" || -z "$count" ]]; then
        echo -e "${RED}Error: Must specify agent type and count${NC}" >&2
        echo "Usage: $0 scale <erdos|researcher> <count>"
        exit 1
    fi

    case "$agent_type" in
        erdos)
            if [[ $count -gt $MAX_ERDOS ]]; then
                echo -e "${YELLOW}Count $count exceeds max $MAX_ERDOS, using $MAX_ERDOS${NC}"
                count=$MAX_ERDOS
            fi

            # Count current
            local current=0
            for i in 1 2 3 4 5; do
                if tmux has-session -t "erdos-enhancer-$i" 2>/dev/null; then
                    ((current++))
                fi
            done

            if [[ $count -gt $current ]]; then
                local to_add=$((count - current))
                echo -e "${BLUE}Scaling Erdős enhancers from $current to $count (adding $to_add)...${NC}"
                ./scripts/erdos/parallel-enhance.sh "$to_add" &
                sleep 2
                echo -e "${GREEN}✓ Scaled to $count Erdős enhancers${NC}"
            elif [[ $count -lt $current ]]; then
                echo -e "${YELLOW}Scale down not implemented - stop agents manually${NC}"
                echo "Current: $current, Requested: $count"
            else
                echo -e "${GREEN}Already at $count Erdős enhancers${NC}"
            fi
            ;;
        researcher)
            if [[ $count -gt $MAX_RESEARCHER ]]; then
                echo -e "${YELLOW}Count $count exceeds max $MAX_RESEARCHER, using $MAX_RESEARCHER${NC}"
                count=$MAX_RESEARCHER
            fi

            local current=0
            for i in 1 2 3; do
                if tmux has-session -t "researcher-$i" 2>/dev/null; then
                    ((current++))
                fi
            done

            if [[ $count -gt $current ]]; then
                local to_add=$((count - current))
                echo -e "${BLUE}Scaling Researchers from $current to $count (adding $to_add)...${NC}"
                ./scripts/research/parallel-research.sh "$to_add" &
                sleep 2
                echo -e "${GREEN}✓ Scaled to $count Researchers${NC}"
            elif [[ $count -lt $current ]]; then
                echo -e "${YELLOW}Scale down not implemented - stop agents manually${NC}"
                echo "Current: $current, Requested: $count"
            else
                echo -e "${GREEN}Already at $count Researchers${NC}"
            fi
            ;;
        aristotle|deployer)
            echo -e "${YELLOW}$agent_type can only have 0 or 1 instance${NC}"
            echo "Use 'spawn' or 'stop' to control single-instance agents"
            ;;
        *)
            echo -e "${RED}Unknown agent type: $agent_type${NC}" >&2
            echo "Scalable types: erdos, researcher"
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
