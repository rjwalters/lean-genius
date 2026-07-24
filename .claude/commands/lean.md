# Lean

Dispatch mathematical orchestration commands via the shell daemon (`launch.sh`).

## Important: Use the Shell Daemon

The shell daemon (`./scripts/lean/launch.sh daemon`) is the primary orchestration system. It runs continuously in a tmux session, handles token rotation, health checks, respawning, and crash recovery autonomously.

**Do NOT try to implement a continuous loop using Claude Code subagents.** That approach requires manual cycling, suffers from auth expiration, and reinvents what `launch.sh` already does.

## Dispatch Logic

Parse `$ARGUMENTS` and route:

### No arguments, `start`, or `daemon` → Start the shell daemon

```bash
# Check if already running
./scripts/lean/launch.sh health

# Start in tmux via the keeper (recommended — runs autonomously AND auto-restarts
# the daemon if it crashes; the daemon runs under `set -euo pipefail` and can die
# on any unguarded non-zero in its loop, which leaves agents orphaned).
tmux new-session -d -s lean-daemon './scripts/lean/daemon-keeper.sh --enricher 1 --researcher 3 --deployer 1'

# Or with custom pool
tmux new-session -d -s lean-daemon './scripts/lean/daemon-keeper.sh --enricher 1 --researcher 3 --aristotle 1 --seeker 1 --deployer 1 --auditor 1 --mechanic 1'

# Adopt an already-running fleet without tearing it down (keeper + monitor-only):
tmux new-session -d -s lean-daemon './scripts/lean/daemon-keeper.sh --monitor-only --interval 60 --enricher 1 --researcher 3 --aristotle 1 --auditor 1 --seeker 1 --deployer 1 --tester 1 --herald 1 --mechanic 1'
```

> **Pool ratio (issue #43008):** default is 1 enricher / 3 researchers. The
> enrichment queue sits at its quality floor — when `launch.sh status` shows
> "Proofs needing enrichment: 0" (or find-targets serves only 96+-quality
> score-ceiling noise), extra enricher capacity is wasted; keep enrichers at 1
> and spend the slots on researchers instead.

> The keeper supervises the supervisor: it restarts `launch.sh daemon` on any
> non-clean exit, with crash-loop backoff, and logs lifecycle events to
> `research/lean-daemon-keeper.log` (the daemon's own `daemon_log` only echoes to
> its tmux pane, which is lost when it dies). A clean stop (`touch
> .loom/signals/stop-lean-daemon`) makes the keeper exit too.

### `status` → Show system state

```bash
./scripts/lean/launch.sh health
./scripts/lean/launch.sh status
```

### `stop` → Stop the daemon and agents

```bash
./scripts/lean/launch.sh stop --force
```

### `spawn <type>` → Spawn one agent

```bash
./scripts/lean/launch.sh spawn <type>
```

Or for a one-shot Claude subagent (independent of the daemon pool), use the Agent tool with `isolation: "worktree"`.

### `scale <type> <N>` → Scale pool

```bash
./scripts/lean/launch.sh scale <type> <N>
```

### `health` → Health check

```bash
./scripts/lean/launch.sh health
```

### `wake [type]` → Wake sleeping agent

```bash
./scripts/lean/launch.sh wake [type]
```

## Account Allowlist

Control which OAuth accounts agents use:
```bash
./scripts/agents/pin-account.sh status                  # Show current state
./scripts/agents/pin-account.sh allow agent-6 agent-7   # Only use these accounts
./scripts/agents/pin-account.sh add agent-8             # Add to allowlist
./scripts/agents/pin-account.sh remove agent-6          # Remove from allowlist
./scripts/agents/pin-account.sh reset                   # Use all accounts (default)
```

## Quick Reference

| User says | You do |
|-----------|--------|
| `/lean` | Start shell daemon in tmux with defaults |
| `/lean start --researcher 3` | Start shell daemon with custom pool |
| `/lean status` | Run `launch.sh status` + `launch.sh health` |
| `/lean stop` | Run `launch.sh stop --force` |
| `/lean spawn researcher` | Run `launch.sh spawn researcher` |
| `/lean scale enricher 4` | Run `launch.sh scale enricher 4` |

## What NOT to do

- Don't implement a continuous monitoring loop inside Claude Code's conversation
- Don't spawn multiple background Agent tool subagents and manually cycle them
- Don't reinvent health checks, respawning, or token rotation — `launch.sh` handles all of it

ARGUMENTS: $ARGUMENTS
