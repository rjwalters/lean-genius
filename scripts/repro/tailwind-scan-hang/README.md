# Tailwind v4 Oxide Scan-Hang Repro (#21009)

Synthetic pollution fixture for issue #21009 (vite build hangs in dev checkout
because Tailwind v4 oxide scanner walks nested worktree repo copies).

## Layout

- `setup.sh [N]` — Generate `N` (default 50) nested repo-like dirs under
  `tmp-tailwind-repro/` at the repo root. Each fixture dir contains
  `src/index.html`, `src/index.css`, `src/App.tsx`, `data/blob-*.json`,
  `proofs/Proofs/Fixture*.lean`, and a self-referential `proofs/.lake -> .`
  symlink. Environment variables `JSON_PER_DIR` and `LEAN_PER_DIR` tune
  per-fixture file count (defaults 40 and 30).
- `teardown.sh` — Remove `tmp-tailwind-repro/` (requires `.fixture-marker`).

## Usage

```bash
./scripts/repro/tailwind-scan-hang/setup.sh 50
# Comment out `tmp-tailwind-repro/` in .gitignore so oxide scans the fixture.
time pnpm build
./scripts/repro/tailwind-scan-hang/teardown.sh
```

## Builder findings (2026-06-08) — NEGATIVE RESULT

Builder running in `.loom/worktrees/issue-21009/` was **unable to reproduce
the hang** with this fixture at any tested scale:

| Fixture N | Files  | gitignored | Hang? | vite build time |
|-----------|--------|------------|-------|-----------------|
| 50        | 1,251  | yes        | no    | ~46s            |
| 200       | 16,001 | yes        | no    | ~43s            |
| 200       | 16,001 | no         | no    | ~9s             |
| 500       | 40,001 | no         | no    | ~11s            |
| 500       | 40,001 | no + upward symlink to worktree root | no | ~7.7s |

Verification that oxide actually walked the fixture (when not gitignored):
a unique utility class `bg-lime-700 text-rose-300` placed in
`tmp-tailwind-repro/fixture-1/src/MarkerOxide.tsx` DID appear in the
generated `dist/assets/*.css`, confirming oxide scanned the fixture.

Key observation: **oxide v4.1.18 honors `.gitignore`** in builder testing —
files under a gitignored path are skipped (their utility classes do NOT
appear in output CSS). This contradicts #21009's diagnosis that gitignored
`.loom/worktrees/` was being scanned. The real polluted-checkout hang is
likely tied to a topology this synthetic fixture does not replicate:

1. **True git checkouts**: real worktrees are full clones with `.git`
   directories, real `proofs/Proofs/` Lean files (3000+ each), real
   `node_modules/`, etc. — orders of magnitude more file content than the
   synthetic blobs.
2. **Deeper recursion**: real worktrees may contain their own nested
   `.claude/worktrees/` or `.loom/worktrees/` from prior agent activity,
   producing depth-3+ recursion the synthetic fixture does not include.
3. **Specific symlink topology**: real `proofs/.lake` symlinks may have
   pointed to a different target (e.g., out-of-tree absolute path) that
   defeated oxide's cycle detection.
4. **Oxide version drift**: #21009 was filed against an unspecified oxide
   version; v4.1.18 may include a gitignore/cycle-detection improvement
   that masks the original failure mode in synthetic conditions.

## Operator-verification path

Before applying the `@source` scoping fix sketched in the issue body, the
operator should:

1. cd to the polluted primary checkout (`/Users/rwalters/GitHub/lean-genius`).
2. Confirm `pnpm build` still hangs (>120s real, ~0 user CPU during transform).
3. Verify oxide version: `cat node_modules/@tailwindcss/oxide/package.json`.
4. Try a positive-scope fix in `src/index.css`:
   ```css
   /* Disable auto-detection and explicitly scope to src/ */
   @source "./**/*.{ts,tsx,html,css,md}";
   @source not "../tmp-tailwind-repro";
   @source not "../.loom/worktrees";
   @source not "../.claude/worktrees";
   @import "tailwindcss" source(none);
   ```
5. If the fix works, file a follow-up PR with the validated CSS change.

## Why a builder cannot ship the fix today

Per the issue body and this fixture's negative result, no Builder working
in a clean issue worktree (or a clean fixture-augmented worktree) can
empirically validate that a Tailwind `@source` change resolves the hang.
The scoping fix would amount to a CSS change without an executable
regression test, which the workflow guidance forbids.
