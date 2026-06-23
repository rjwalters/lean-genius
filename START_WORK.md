# Start Work Session

Recipe for launching the agent team. Run these commands at the start of a work session.

## 1. Check Current State

```bash
# See what's already running
tmux list-sessions

# Check for any issues
make status
```

## 2. Launch Agent Team (5 agents)

```bash
# Erdős problem agents (2) - build/enhance the problem library
make enhance N=2

# Aristotle agent (1) - manage proof search queue
make aristotle

# Research agent (1) - deep problem analysis
make research N=1

# Deployer agent (1) - merge PRs and deploy website
make deployer
```

**One-liner:**
```bash
make enhance N=2 && make aristotle && make research N=1 && make deployer
```

## 3. Verify All Running

```bash
tmux list-sessions
# Should show: erdos-enhancer-1, erdos-enhancer-2, aristotle-agent, researcher-1, deployer
```

## 4. Quick Status Check

```bash
make status
```

## After API Limit Reset

If agents stopped due to API limits:
```bash
make restart-all
```

## Monitor During Session

```bash
# Watch an agent work
tmux attach -t erdos-enhancer-1  # Detach: Ctrl+B, D

# Check progress
make status

# View logs
tail -f .loom/logs/deployer.log
```

## Expected Outputs

| Agent | What It Does |
|-------|--------------|
| erdos-enhancer-1/2 | Creates PRs enhancing Erdős problem stubs |
| aristotle-agent | Submits proofs to Aristotle, integrates results |
| researcher-1 | Creates PRs with deep problem analysis |
| deployer | Merges PRs every 30min, deploys to Cloudflare |
