# Stop Work Session

Recipe for gracefully stopping agents and cleaning up. Run these at the end of a work session.

## 1. Signal Graceful Stop

Let agents finish their current work:
```bash
make stop
```

Wait a few minutes for agents to complete current tasks.

## 2. Force Stop (if needed)

If agents don't stop gracefully:
```bash
./scripts/erdos/parallel-enhance.sh --stop
./scripts/research/parallel-research.sh --stop
./scripts/aristotle/launch-agent.sh --stop
./scripts/deploy/launch-agent.sh --stop
```

## 3. Verify All Stopped

```bash
tmux list-sessions
# Should show no agent sessions (or only non-agent sessions)
```

## 4. Clean Up Stale Claims

```bash
./scripts/erdos/claim-stub.sh cleanup
./scripts/research/claim-problem.sh cleanup
```

## 5. Final Deploy (Optional)

Merge any remaining PRs and deploy:
```bash
make deploy
```

Or check what's pending:
```bash
gh pr list --limit 20
```

## 6. Commit Any Local Changes

```bash
git status
# If there are changes worth keeping, commit them on a BRANCH and open a PR —
# direct pushes to main are blocked by branch protection (see CLAUDE.md):
git checkout -b chore/stop-work-sync
git add -A && git commit -m "chore: sync data"
git push -u origin chore/stop-work-sync
gh pr create --fill
```

## 7. Summary Check

```bash
# See final progress
make status

# Research progress
cat .lean/state/candidate-pool.json | jq '[.candidates[] | .status] | group_by(.) | map({status: .[0], count: length})'
```

## Quick Stop (One Command)

For a fast shutdown without cleanup:
```bash
make stop && sleep 5 && tmux kill-server 2>/dev/null; echo "All stopped"
```

**Warning:** This kills ALL tmux sessions, not just agents.

## Notes

- Agents will create PRs for completed work before stopping
- The deployer runs every 30min, so recent PRs may not be merged yet
- Run `make deploy` manually if you want immediate deployment
- Stale claims auto-expire after 60-90 minutes
