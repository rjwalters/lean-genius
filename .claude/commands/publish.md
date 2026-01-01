# Publish

Publish the research section to the lean-genius website. This syncs research data, builds the site, commits changes, pushes to GitHub, and deploys to Cloudflare.

## What This Does

1. **Sync Research Data** — Syncs `candidate-pool.json` → `registry.json` and creates missing problem directories
2. **Build Research Section** — Generates `research-listings.json` and individual problem JSON files
3. **Commit & Push** — Commits all changes with a descriptive message and pushes to origin
4. **Deploy to Cloudflare** — Builds the full site and deploys to Cloudflare Pages

## Steps

### Step 1: Sync Research Data

First, sync the candidate pool with the registry:

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

### Step 3: Review Changes

Check what files have changed:

```bash
git status
git diff --stat
```

If there are new research problems or updates, proceed to commit.

### Step 4: Commit Changes

Commit the research updates:

```bash
git add research/ src/data/research/
git commit -m "$(cat <<'EOF'
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
pnpm deploy
```

This runs:
1. `pnpm annotations:build` — Resolve proof annotations
2. `pnpm research:build` — Build research data (already done, but idempotent)
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

### Build Errors
If `pnpm research:build` fails:
- Check that `research/registry.json` is valid JSON
- Verify problem directories have required `problem.md` files
- Look for missing fields in problem.md templates

### Deploy Errors
If `pnpm deploy` fails:
- Check wrangler authentication: `wrangler whoami`
- Verify project name: `wrangler pages project list`
- Check for TypeScript errors in the build output

### Sync Issues
If sync seems wrong:
- Manually check `research/candidate-pool.json` for the source of truth
- The pool file is authoritative for problem status
- Registry is derived from pool + enriched with phase/path info
