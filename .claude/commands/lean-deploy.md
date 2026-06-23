# Deploy

Deploy the lean-genius website to Cloudflare Pages. **For maintainers only** - use after merging PRs.

> **Note**: Contributors should use `/publish` to create PRs. This command is for deploying merged changes.

## Quick Deploy

After merging a PR to main:

```bash
cd /Users/rwalters/GitHub/lean-genius

# Pull latest changes
git checkout main
git pull origin main

# Deploy (runs sync, build, and Cloudflare deployment)
pnpm run deploy
```

## What `pnpm run deploy` Does

1. **Syncs research data** - `candidate-pool.json` → `registry.json`
2. **Builds research files** - Generates research listings
3. **Resolves annotations** - Processes proof annotations
4. **Compiles TypeScript** - Type checks the codebase
5. **Bundles with Vite** - Creates production build
6. **Deploys to Cloudflare** - Pushes to Pages

## Full Workflow (with Lean verification)

If the merged PR includes Lean changes:

```bash
cd /Users/rwalters/GitHub/lean-genius

# Pull latest
git checkout main
git pull origin main

# Verify Lean proofs build
cd proofs
lake build
cd ..

# Deploy
pnpm run deploy
```

## Verify Deployment

1. Check deployment URL in terminal output
2. Visit https://lean-genius.pages.dev
3. Verify changes appear correctly
4. Check https://lean-genius.pages.dev/research for research updates

## Summary Template

```markdown
## Deployment Complete

**URL**: https://lean-genius.pages.dev
**Commit**: [commit hash]
**Changes**: [merged PR summary]
```

## Troubleshooting

| Problem | Solution |
|---------|----------|
| `wrangler` auth error | Run `wrangler whoami` and re-auth if needed |
| Build fails | Check TypeScript errors with `pnpm run build` |
| Lean build fails | Fix errors in `.lean` files first |
| Stale data | Run `pnpm run research:sync` manually |
