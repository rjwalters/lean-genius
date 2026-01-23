# Lean Genius Work Session

Quick reference for running agent teams within API limits.

## Recommended Team (5 agents)

| Agent | Count | Purpose |
|-------|-------|---------|
| Erdős Enhancers | 2 | Build complete Erdős problem library |
| Aristotle | 1 | Manage proof search queue (~20 active jobs) |
| Researcher | 1 | Deep research on problems with knowledge |
| Deployer | 1 | Merge PRs, sync data, deploy website |

## Quick Start

```bash
# Launch the full team
make enhance N=2
make aristotle
make research N=1
make deployer
```

Or as a single command:
```bash
make enhance N=2 && make aristotle && make research N=1 && make deployer
```

## Check Status

```bash
# All agents at once
make status

# Individual status
make status-enhancers
make status-research
make status-aristotle
make deployer-status

# List running sessions
tmux list-sessions
```

## After API Limit Reset

```bash
# Restart any stopped agents
make restart-all
```

## Stop All Agents

```bash
# Graceful stop (finish current work)
make stop

# Force stop immediately
./scripts/erdos/parallel-enhance.sh --stop
./scripts/research/parallel-research.sh --stop
./scripts/aristotle/launch-agent.sh --stop
./scripts/deploy/launch-agent.sh --stop
```

## Monitor Progress

```bash
# Erdős stub enhancement progress
enhanced=$(find src/data/proofs/erdos-* -name "annotations.json" -exec sh -c 'test $(wc -l < "$1") -ge 90 && echo 1' _ {} \; | wc -l)
total=$(ls src/data/proofs/erdos-*/annotations.json | wc -l)
echo "Enhanced: $enhanced / $total"

# Research pool status
cat research/candidate-pool.json | jq '{completed: [.candidates[] | select(.status == "completed")] | length, pending: [.candidates[] | select(.status == "pending")] | length}'

# Open PRs
gh pr list --limit 20
```

## Attach to Agent Sessions

```bash
# Watch an agent work
tmux attach -t erdos-enhancer-1
tmux attach -t researcher-1
tmux attach -t aristotle-agent
tmux attach -t deployer

# Detach: Ctrl+B, then D
```

## Current Progress

### Erdős Problems
- **Total problems**: 1,135
- **Stubs created**: 821
- **Missing (can be created)**: 314
- **Goal**: Complete library with enhanced annotations

### Research
- **Pool size**: 355 problems
- **Completed**: ~30
- **Goal**: Deep knowledge extraction for all problems

### Aristotle
- **Target**: 20 active proof search jobs
- **Candidates**: 470+
- **Goal**: Automated proof discovery

## Troubleshooting

### Agents stopped after API limit
```bash
make restart-all
```

### Large PR diffs (branch divergence)
```bash
# Clean up and restart researchers
./scripts/research/parallel-research.sh --cleanup
make research N=1
```

### Stale claims blocking work
```bash
./scripts/erdos/claim-stub.sh cleanup
./scripts/research/claim-problem.sh cleanup
```

### Check agent logs
```bash
tail -50 .loom/logs/enhancer-1.actions.log
tail -50 .loom/logs/researcher-1.log
tail -50 .loom/logs/deployer.log
```

## Manual Operations

### Deploy website manually
```bash
make deploy
# Or: ./scripts/deploy/sync-and-deploy.sh
```

### Merge PRs manually
```bash
gh pr list --limit 50
gh pr merge <number> --squash
```

### Create missing Erdős stub
```bash
./scripts/erdos/create-stub.sh 42  # Specific problem
./scripts/erdos/create-stub.sh --list-missing | head -20  # See what's missing
```
