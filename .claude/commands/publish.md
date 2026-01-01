# Publish

Publish the research section to the lean-genius website. This syncs research data, builds the site, commits changes, pushes to GitHub, and deploys to Cloudflare.

## What This Does

1. **Verify Lean Proofs** — Ensure all proof files build without errors
2. **Sync Research Data** — Syncs `candidate-pool.json` → `registry.json` and creates missing problem directories
3. **Build Research Section** — Generates `research-listings.json` and individual problem JSON files
4. **Commit & Push** — Commits all changes with a descriptive message and pushes to origin
5. **Deploy to Cloudflare** — Builds the full site and deploys to Cloudflare Pages

## Steps

### Step 0: Verify Lean Proofs Build

Before publishing, ensure any new or modified Lean proofs compile:

```bash
cd /Users/rwalters/GitHub/lean-genius/proofs

# Check for modified Lean files
git diff --name-only -- '*.lean'

# Build all proofs (or specific modified ones)
lake build
```

**IMPORTANT**: If the build fails, fix the errors before proceeding. Do NOT commit broken proofs.

If only specific proofs are modified, you can build just those:
```bash
lake build Proofs.SchursTheorem  # Example
```

### Step 1: Sync Research Data

Sync the candidate pool with the registry:

```bash
cd /Users/rwalters/GitHub/lean-genius
pnpm research:sync
```

This will:
- Add new problems from `candidate-pool.json` to `registry.json`
- Create `research/problems/{slug}/` directories for new problems
- Sync status between files (completed → graduated, skipped → blocked)

### Step 2: Build Research Section

Build the research data for the website:

```bash
pnpm research:build
```

This generates:
- `src/data/research/research-listings.json` — Gallery listing data
- `src/data/research/problems/{slug}.json` — Individual problem detail pages

### Step 3: Check for Changes

Check what files have changed:

```bash
git status
git diff --stat
```

**If there are no changes**: Skip to Step 6 (Deploy) or stop if nothing new to publish.

**If there are changes**: Continue to Step 4.

### Step 4: Commit Changes

Stage and commit the research updates:

```bash
# Stage research and data files
git add research/ src/data/research/ proofs/Proofs/

# Check what's staged
git diff --staged --stat

# Commit (skip if nothing staged)
git diff --staged --quiet || git commit -m "$(cat <<'EOF'
Publish research updates

- Synced candidate-pool.json with registry
- Updated research-listings.json
- Generated problem detail pages

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude <noreply@anthropic.com>
EOF
)"
```

### Step 5: Push to GitHub

Push the changes to the remote repository:

```bash
git push origin main
```

### Step 6: Deploy to Cloudflare

Build and deploy the full site:

```bash
pnpm run deploy
```

**Note**: Use `pnpm run deploy`, not `pnpm deploy`.

This runs:
1. `pnpm annotations:build` — Resolve proof annotations
2. `pnpm research:build` — Build research data (idempotent)
3. `tsc -b` — TypeScript compilation
4. `vite build` — Production bundle
5. `wrangler pages deploy dist` — Deploy to Cloudflare Pages

### Step 7: Verify Deployment

After deployment, verify the site is updated:

1. Check the deployment URL printed by wrangler
2. Visit https://lean-genius.pages.dev/research to see the research gallery
3. Confirm new/updated problems appear correctly

## Summary Report

After completing all steps, provide a summary:

```markdown
## Publish Complete

**Lean Build**: ✓ All proofs compile
**Synced**: X new problems added, Y statuses updated
**Built**: Z research problems processed
**Deployed**: https://lean-genius.pages.dev

### Changes Published
- [list of significant changes]

### Verification
- [ ] Site loads correctly
- [ ] Research gallery shows updates
- [ ] Individual problem pages work
```

## Troubleshooting

### Lean Build Errors
If `lake build` fails:
- Check the specific error message and file
- Fix syntax or type errors in the Lean file
- Ensure all imports are correct
- Run `lake clean && lake build` for a fresh build

### Build Errors
If `pnpm research:build` fails:
- Check that `research/registry.json` is valid JSON
- Verify problem directories have required `problem.md` files
- Look for missing fields in problem.md templates

### Deploy Errors
If `pnpm run deploy` fails:
- Check wrangler authentication: `wrangler whoami`
- Verify project name: `wrangler pages project list`
- Check for TypeScript errors in the build output

### Nothing to Commit
If `git status` shows no changes after sync:
- This is normal if nothing has changed since last publish
- Proceed directly to deploy if you want to redeploy

### Sync Issues
If sync seems wrong:
- Manually check `research/candidate-pool.json` for the source of truth
- The pool file is authoritative for problem status
- Registry is derived from pool + enriched with phase/path info

## Quick Reference

One-liner to check everything before publish:
```bash
cd /Users/rwalters/GitHub/lean-genius && \
  (cd proofs && lake build) && \
  pnpm research:build && \
  git status
```

Full publish (after verification):
```bash
git add -A && \
  git commit -m "Publish research updates" && \
  git push origin main && \
  pnpm run deploy
```
