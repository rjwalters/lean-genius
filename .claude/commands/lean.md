# Lean

Assume the Lean Daemon role and run the **continuous** mathematical orchestration system.

## Process

1. **Parse arguments**: Extract command and options
2. **Initialize state**: Load or create `research/lean-daemon-state.json`
3. **Run continuous loop**: Spawn mathematical agents, monitor progress, scale pools
4. **Run until cancelled**: Continue until Ctrl+C or stop signal

## Work Scope

As the **Lean Daemon**, you **continuously** orchestrate the mathematical agent team:

- **Spawn Erdős enhancers** to upgrade gallery stubs with Lean formalizations
- **Spawn Aristotle agents** to manage proof search queue
- **Spawn Researchers** to work on open mathematical problems
- **Spawn Seekers** to select research problems when the candidate pool runs low
- **Spawn Deployers** to merge PRs and deploy the website
- **Monitor progress** by checking tmux sessions and work queues
- **Scale pools** based on available work
- **Track state** in `research/lean-daemon-state.json` for crash recovery

You don't do the mathematical work yourself - you spawn worker agents to do the work in parallel.

## Usage

```
/lean                     # Start daemon with default pool (2 erdos, 1 aristotle, 1 researcher, 1 seeker, 1 deployer)
/lean status              # Report current system state only
/lean start --erdos 3 --researcher 2    # Start with custom pool sizes
/lean spawn erdos         # Manually spawn one Erdős enhancer
/lean spawn aristotle     # Manually spawn Aristotle agent
/lean spawn researcher    # Manually spawn Researcher agent
/lean spawn seeker        # Manually spawn Seeker agent
/lean spawn deployer      # Manually spawn Deployer agent
/lean scale erdos 3       # Scale Erdős pool to 3 agents
/lean stop                # Graceful shutdown of all agents
```

## Commands

| Command | Description |
|---------|-------------|
| (none) | Start continuous daemon loop with defaults |
| `status` | Report system state without starting loop |
| `start [options]` | Start daemon with custom pool configuration |
| `spawn <type>` | Manually spawn one agent of specified type |
| `scale <type> <count>` | Scale agent pool to specified count |
| `stop` | Graceful shutdown of all agents |

## Start Options

| Option | Default | Description |
|--------|---------|-------------|
| `--erdos N` | 2 | Number of Erdős enhancer agents |
| `--aristotle N` | 1 | Number of Aristotle agents |
| `--researcher N` | 1 | Number of Researcher agents |
| `--seeker N` | 1 | Number of Seeker agents |
| `--deployer N` | 1 | Number of Deployer agents |

## Pool Configuration

```json
{
  "erdos": { "min": 0, "max": 5, "default": 2 },
  "aristotle": { "min": 0, "max": 2, "default": 1 },
  "researcher": { "min": 0, "max": 3, "default": 1 },
  "seeker": { "min": 0, "max": 1, "default": 1 },
  "deployer": { "min": 0, "max": 1, "default": 1 }
}
```

## Status Command

The `status` command displays the current system state without taking any action.

**To run status**, execute the helper script:

```bash
# Display formatted status
./scripts/lean/status.sh

# Get status as JSON for scripting
./scripts/lean/status.sh --json
```

**Status shows**:
- Daemon status (running/stopped, uptime)
- Work queue depths for each agent type
- Agent pool status (active/idle, current work)
- Session statistics (stubs enhanced, proofs submitted, deployments)

## Continuous Loop

The daemon runs **continuously** until cancelled:

```
while not cancelled:
    1. Check for shutdown signal (research/lean-stop-daemon)
    2. Assess work queues (stubs, proofs, research problems, PRs)
    3. Check agent completions (tmux session status)
    4. Spawn/scale agents based on work availability
    5. Print status report
    6. Sleep 60 seconds, repeat
```

## Spawning Agents

Agents are spawned via the existing launch scripts which create tmux sessions:

```bash
# Spawn Erdős enhancers
./scripts/erdos/parallel-enhance.sh N

# Spawn Aristotle agent
./scripts/aristotle/launch-agent.sh

# Spawn Researchers
./scripts/research/parallel-research.sh N

# Spawn Seeker agent
./scripts/research/launch-seeker.sh

# Spawn Deployer
./scripts/deploy/launch-agent.sh
```

The daemon monitors these tmux sessions to track agent status.

## Work Queue Monitoring

| Agent Type | Work Source | Check Command |
|------------|-------------|---------------|
| Erdős | Stubs needing enhancement | `npx tsx scripts/erdos/find-stubs.ts --stats` |
| Aristotle | Pending proof search jobs | `jq '.jobs \| map(select(.status=="submitted")) \| length' research/aristotle-jobs.json` |
| Researcher | Available research problems | `jq '.candidates \| map(select(.status=="available")) \| length' research/candidate-pool.json` |
| Seeker | Low candidate pool | `jq '.candidates \| map(select(.status=="available")) \| length' research/candidate-pool.json` (triggers when < 5) |
| Deployer | PRs ready to merge | `gh pr list --label "loom:pr" --json number \| jq length` |

## Status Report

```
═══════════════════════════════════════════════════
  LEAN GENIUS STATUS
═══════════════════════════════════════════════════
  Daemon: Running (uptime: 2h 15m)

  Work Queue:
    Stubs needing enhancement: 127 (with sources)
    Aristotle jobs pending: 5
    Research problems available: 12
    PRs ready to merge: 2

  Agent Pool:
    Erdős Enhancers: 2/2 active
      erdos-enhancer-1: Running (45m)
      erdos-enhancer-2: Running (12m)
    Aristotle: 1/1 active
      aristotle-agent: Running
    Researcher: 1/1 active
      researcher-1: Running (1h 20m)
    Seeker: 1/1 active
      seeker-agent: Running (15m cycle)
    Deployer: 1/1 active
      deployer: Last cycle 30m ago

  Session Stats:
    Stubs enhanced: 5
    Proofs submitted: 3
    Problems selected: 2
    Deployments: 1
═══════════════════════════════════════════════════
```

## State Persistence

State tracked in `research/lean-daemon-state.json`:

```json
{
  "started_at": "2026-01-24T10:00:00Z",
  "running": true,
  "config": {
    "erdos": 2,
    "aristotle": 1,
    "researcher": 1,
    "seeker": 1,
    "deployer": 1
  },
  "agents": {
    "erdos-enhancer-1": { "status": "running", "started": "2026-01-24T10:00:00Z" },
    "erdos-enhancer-2": { "status": "running", "started": "2026-01-24T10:05:00Z" },
    "aristotle-agent": { "status": "running", "started": "2026-01-24T10:00:00Z" },
    "researcher-1": { "status": "running", "started": "2026-01-24T10:00:00Z" },
    "seeker-agent": { "status": "running", "started": "2026-01-24T10:00:00Z" },
    "deployer": { "status": "running", "started": "2026-01-24T10:00:00Z" }
  },
  "session_stats": {
    "stubs_enhanced": 5,
    "proofs_submitted": 3,
    "proofs_integrated": 2,
    "problems_selected": 2,
    "deployments": 1
  }
}
```

## Graceful Shutdown

```bash
# Option 1: Create stop signal
touch research/lean-stop-daemon

# Option 2: Use command
/lean stop

# Daemon will:
# 1. Stop spawning new agents
# 2. Send graceful stop to all agents
# 3. Wait for agents to complete current work (max 5 min)
# 4. Clean up state
# 5. Exit
```

## Agent Coordination

### Erdős Enhancers
- Use random stub selection to avoid collisions
- Each agent works in isolated worktree
- Creates PR when stub is enhanced

### Aristotle
- Single agent manages proof search queue
- Submits jobs, retrieves results, integrates proofs
- Runs on 30-minute cycle

### Researchers
- Claim problems atomically via claim files
- Each works in isolated worktree
- Creates PR with proof progress

### Seeker
- Monitors candidate pool depth (triggers when < 5 available)
- Selects problems using knowledge score + tractability ranking
- Initializes research workspaces for new problems
- Runs on 15-minute cycle
- Single instance (max 1 agent)

### Deployer
- Merges approved PRs (`loom:pr` label)
- Syncs data and deploys to Cloudflare
- Runs on 30-minute cycle

## Layer Architecture

| Layer | Role | Purpose |
|-------|------|---------|
| Layer 2 | **Lean Daemon** (`/lean`) | Spawns workers, manages pools, monitors progress |
| Layer 1 | **Workers** (`/erdos`, `/aristotle`, `/research`, `/scout`, `/seeker`, `/deploy`) | Execute mathematical work |

Use `/erdos`, `/aristotle`, `/research`, `/scout`, `/seeker`, or `/deploy` for single-agent work.
Use `/lean` to run the continuous orchestrator that manages the full team.

## Integration with Loom

The Lean Daemon coexists with the Loom Daemon:
- `/loom` orchestrates development work (Builder, Judge, Curator)
- `/lean` orchestrates mathematical work (Erdős, Aristotle, Researcher, Seeker, Deployer)

They share:
- Worktree infrastructure (`.loom/worktrees/`)
- PR workflow (PRs get `loom:review-requested` for Judge review)
- GitHub coordination (labels, issues)

## Example Session

```bash
# Start the mathematical team
/lean start --erdos 2 --aristotle 1 --researcher 1 --seeker 1 --deployer 1

# Check status periodically
/lean status

# Scale up Erdős enhancers if many stubs available
/lean scale erdos 4

# Add another researcher
/lean spawn researcher

# Graceful shutdown when done
/lean stop
```

ARGUMENTS: $ARGUMENTS
