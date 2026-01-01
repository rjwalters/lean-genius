# Publish

Publish changes to the lean-genius website. Commits, pushes, and deploys to Cloudflare.

> **Note**: `pnpm run deploy` automatically runs `research:sync`, `research:build`, `annotations:build`, TypeScript compilation, and Vite build. No manual sync/build steps needed.

## Quick Publish (Recommended)

If Lean proofs are already built:

```bash
cd /Users/rwalters/GitHub/lean-genius && \
  git add -A && \
  git diff --staged --quiet || git commit -m "Publish updates" && \
  git push origin main && \
  pnpm run deploy
```

## Full Workflow

### Step 1: Verify Lean Proofs (Optional)

Only needed if you changed `.lean` files and haven't built recently:

```bash
cd /Users/rwalters/GitHub/lean-genius/proofs

# Build only changed files (memory-safe)
CHANGED=$(git diff --name-only HEAD~1 -- '*.lean' | grep -v '^proofs/Proofs\.lean$' || true)
for file in $CHANGED; do
  module=$(echo "$file" | sed 's|^proofs/||; s|/|.|g; s|\.lean$||')
  lake build "$module"
done
```

**If build fails**: Fix errors before proceeding.

### Step 2: Commit & Push

```bash
cd /Users/rwalters/GitHub/lean-genius

# Check what changed
git status

# Stage and commit (skip if nothing to commit)
git add -A
git diff --staged --quiet || git commit -m "$(cat <<'EOF'
Publish updates

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"

# Push
git push origin main
```

### Step 3: Deploy

```bash
pnpm run deploy
```

This single command:
1. Syncs `candidate-pool.json` → `registry.json`
2. Builds research data files
3. Resolves proof annotations
4. Compiles TypeScript
5. Bundles with Vite
6. Deploys to Cloudflare Pages

### Step 4: Verify

1. Check deployment URL in terminal output
2. Visit https://lean-genius.pages.dev/research
3. Confirm changes appear correctly

## Summary Template

```markdown
## Publish Complete

**Deployed**: https://lean-genius.pages.dev
**Changes**: [brief summary]
```

## Troubleshooting

| Problem | Solution |
|---------|----------|
| Lean build fails | Fix errors in `.lean` file, re-run `lake build Module` |
| `pnpm run deploy` fails | Check `wrangler whoami`, verify auth |
| Nothing to commit | Normal - proceed to deploy if redeploy needed |
| Sync seems wrong | `candidate-pool.json` is source of truth |
