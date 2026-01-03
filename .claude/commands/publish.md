# Publish

Publish your research contributions by creating a Pull Request. This packages your work into a branch and opens a PR for review.

> **Note**: This creates a PR rather than pushing directly to main. Your contributions will be reviewed before merging.

## Quick Publish (Recommended)

Run this to create a PR with your accumulated research work:

```bash
cd /Users/rwalters/GitHub/lean-genius

# Ensure we have the latest main
git fetch origin main

# Check for changes
if git diff --quiet && git diff --staged --quiet && [ -z "$(git status --porcelain)" ]; then
  echo "No changes to publish"
  exit 0
fi

# Generate branch name with timestamp
BRANCH_NAME="research/contribution-$(date +%Y%m%d-%H%M%S)"

# Get current branch
CURRENT_BRANCH=$(git branch --show-current)

# If on main, create a new branch
if [ "$CURRENT_BRANCH" = "main" ]; then
  git checkout -b "$BRANCH_NAME"
fi

# Stage and commit all changes
git add -A
git commit -m "$(cat <<'EOF'
Research contribution

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"

# Push the branch
git push -u origin HEAD

# Create the PR
gh pr create --fill --body "$(cat <<'EOF'
## Research Contribution

This PR contains research progress on the lean-genius proof gallery.

### Changes
<!-- The AI will fill this in, or you can describe manually -->

### Checklist
- [ ] Lean proofs build successfully (`lake build`)
- [ ] Knowledge base updated (problem JSON files)
- [ ] No secrets or credentials included

---
🤖 Generated with [Claude Code](https://claude.com/claude-code)
EOF
)"
```

## What This Does

1. **Checks for changes** - Exits early if nothing to publish
2. **Creates a branch** - Named `research/contribution-YYYYMMDD-HHMMSS`
3. **Commits your work** - All modified files including:
   - Lean proof files (`proofs/Proofs/*.lean`)
   - Research knowledge (`src/data/research/problems/*.json`)
   - Candidate pool updates (`research/candidate-pool.json`)
4. **Opens a Pull Request** - For review before merging

## For External Contributors (Fork Workflow)

If you're working on a fork:

```bash
# Make sure your fork is set up correctly
git remote -v
# origin should point to YOUR fork
# upstream should point to rjwalters/lean-genius

# Push to your fork and create PR to upstream
git push -u origin HEAD
gh pr create --repo rjwalters/lean-genius --fill
```

## After Publishing

1. **Check the PR** - Visit the URL shown in the output
2. **Verify CI passes** - Wait for automated checks
3. **Respond to feedback** - Make additional commits if needed
4. **Wait for merge** - Maintainers will review and merge

## Workflow Tips

### Multiple Research Sessions
You can run `/research` multiple times before publishing:
```
/research  # First iteration
/research  # Second iteration
/research  # Third iteration
/publish   # Creates PR with all accumulated work
```

### Descriptive Commits
For better PR descriptions, commit with meaningful messages as you work:
```bash
git add -A
git commit -m "Add infrastructure for ℤ[√-2] Euclidean domain"
# ... more work ...
git add -A
git commit -m "Prove second supplementary law for -2"
# When ready:
/publish
```

## Troubleshooting

| Problem | Solution |
|---------|----------|
| `gh` not authenticated | Run `gh auth login` |
| Branch already exists | Delete with `git branch -D research/...` |
| Merge conflicts | Rebase on main: `git fetch origin && git rebase origin/main` |
| PR to wrong repo | Use `--repo owner/repo` flag with `gh pr create` |
| Want to add more changes | Push additional commits to the same branch |

## Summary Template

After publishing, share this summary:

```markdown
## Research Published

**PR**: [link to PR]
**Branch**: research/contribution-YYYYMMDD-HHMMSS
**Changes**: [brief summary of what was researched]
```
