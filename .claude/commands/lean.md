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

# Start in tmux (recommended — runs autonomously)
tmux new-session -d -s lean-daemon './scripts/lean/launch.sh daemon --enricher 2 --researcher 1 --deployer 1'

# Or with custom pool
tmux new-session -d -s lean-daemon './scripts/lean/launch.sh daemon --enricher 2 --researcher 3 --aristotle 1 --seeker 1 --deployer 1 --auditor 1 --mechanic 1'
```

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
