# Epic #37508 — Reconcile & Flip RESUME runbook

**Written 2026-07-17 mid-flight (context-limit restart). Branch `reconcile/main-into-37508` is READY
for the final re-sweep + flip. Execute the steps below in order.**

## STATE (what's done)
- `reconcile/main-into-37508` = **`main` merged into `feature/issue-37508`** (HEAD `0216dbf81e`).
  Brings main's ~979 commits (94 new proofs + 349 meta.json + research work) onto the migrated branch.
- **Pins are v4.31 on this branch**: `proofs/lean-toolchain`=`leanprover/lean4:v4.31.0`,
  `proofs/lakefile.toml` mathlib `rev = 9a9483a92959bc92bd6a60176dd1fe597298c1f8`, `lake-manifest.json`
  v4.31, `proofs/scripts/docker-build.sh` `IMAGE="lean4-arm64:v4.31.0"`. **VERIFY `proofs/Dockerfile`
  BOTH elan lines (~26 install, ~27 default) are v4.31.0 before flipping — #38066 flagged bumping only one.**
- Merge had 27 conflicts, all resolved to **main's newest content** (preserve research), then the
  **239 main-contributed at-risk files** were swept: 194 built clean, **45 needed v4.31 drift repair —
  ALL 45 now migrated GREEN and collected** onto reconcile.
- Fixes were all light single-seam drift or reconcile-merge duplicate-declaration dedups. New seams
  (add to rename map): `le_or_lt`→`le_or_gt`; `Nat.pow_le_iff_le_log`→`Nat.le_log_iff_pow_le` (.mp→.mpr);
  `ContDiff.differentiable` arg now `n≠0` not `1≤n`; `CancelCommMonoidWithZero` deprecated →
  `[CommMonoidWithZero][IsCancelMulZero]`; `convert using N` surfaces instance-diamond side-goals
  (`all_goals first|rfl|ring`); `Function.comp_def`/`Pi.inv_def` in `simpa` for `.comp`/`f⁻¹`;
  `simp only [box, Finset.mem_Icc]` no longer fires through `Finset.image` (use `mem_image`);
  AlgEquiv→AlgHom `AlgHom.coe_coe` mismatch (use `show` defeq bridge).

## STEP 1 — FINAL RE-SWEEP (the gate; run FIRST on resume)
Recompute the at-risk set and re-verify EVERY one builds on the current reconcile tip (#38066 gate a):
```bash
cd /Users/rwalters/GitHub/lean-genius && git fetch origin reconcile/main-into-37508 -q
W=/Volumes/Stripe/lean-genius/reconcile
git worktree remove --force "$W" 2>/dev/null; git worktree add -q "$W" -B reconcile/main-into-37508 origin/reconcile/main-into-37508
git -C "$W" diff --name-only origin/feature/issue-37508 origin/reconcile/main-into-37508 -- proofs/Proofs \
  | grep '\.lean$' | sed 's|proofs/Proofs/|Proofs.|;s|\.lean$||' > /tmp/atrisk-modules.txt
wc -l /tmp/atrisk-modules.txt   # expect 239
```
Sweep across 6 workers (cpusets 0-2/3-5/6-8/9-11/12-14/15-17, caches lean-mathlib-cache-v431[/-b/-c/-d/-e/-f],
packages lean-mathlib-packages-v431, image lean4-arm64:v4.31.0, `--memory 7g`, per-file `timeout 600`,
`lake build <module>`), round-robin, log `<mod>\t<PASS|FAIL|TIMEOUT>`.
- **Expect 239/239 PASS.** Any FAIL → migrate it: agent branches `rec/<File>` off
  `origin/reconcile/main-into-37508`, fixes ONLY that .lean, EXIT=0, pushes; collector takes ONLY that file
  (`git checkout origin/rec/<File> -- proofs/Proofs/<File>.lean`), re-verifies clean, commits to reconcile.
  **COLLECT DISCIPLINE: single target file only — never checkout "all changed files" from a rec branch
  (stale copies of since-fixed deps → regression; this bit us once).**

## STEP 2 — THE FLIP (only after 239/239 green; IRREVERSIBLE — confirm go/no-go with operator)
1. **Merge `reconcile/main-into-37508` → `main`.** Check `git log origin/main..origin/reconcile/main-into-37508`
   and reverse. reconcile already contains main, so FF if main hasn't advanced; else merge main again + re-sweep
   newly-touched files.
2. Confirm all 5 pins v4.31 (lean-toolchain, lakefile rev, lake-manifest, **Dockerfile BOTH elan lines**,
   docker-build IMAGE). `grep -rn 'v4.26.0' proofs/` build config = empty.
3. **Production volume refresh**: promote/clone warmed `-v431` caches to production
   `lean-mathlib-packages`/`lean-mathlib-cache` names (disk OK: boot 258Gi, Stripe 3.4Ti free).
4. **CI image retag**: retag/publish `lean4-arm64:v4.31.0` wherever CI references the build image.
5. Post-flip smoke: `./proofs/scripts/docker-build.sh Proofs.<known-green>`; confirm new image is the one used.

## STEP 3 — #38067 metadata sweep (after flip lands on main)
Fresh branch off main: `NEW=4.31.0`; `grep -rl '"mathlib_version"' src/data/proofs --include=meta.json | wc -l`
(~3,513+, grows daily); `... | xargs perl -pi -e 's/("mathlib_version"\s*:\s*)(?:"[^"]*"|null)/$1"'"$NEW"'"/'`;
python uniformity check (single key `{'4.31.0': N}`); diff only mathlib_version lines
(`git diff -U0 -- src/data/proofs | grep '^[+-]' | grep -v '^[+-][+-]' | grep -v mathlib_version | wc -l` → 0).
pnpm build likely absent on main → JSON-parse-all is the fallback. PR, merge.

## STEP 4 — close epic #37508.

## KNOWN RESIDUAL FLOOR (dispositioned; NOT a blocker per #38066 gate-a "moved to cleanup issue")
- #39058 Erdos1162Problem · #39059 Erdos10Incomplete01OQ02+child · #39060 BallotProblemOQ03OQ01OQ02Helpers
  chain (+OQ02/OQ02Aristotle) · #39061 the 28 PRE-EXISTING (never compiled even on v4.26).
- Statement repairs persisted `research/migration/38611-statement-repairs-*.txt` (PR #39055).
- After flip, main's safe-subset build shows these ~6 as the known floor — expected, not a regression.

## INFRA
Image `lean4-arm64:v4.31.0`; per-slot caches `lean-mathlib-cache-v431[/-b/-c/-d/-e/-f/-g/-h]` (~20G warmed);
shared `lean-mathlib-packages-v431`; worktrees `/Volumes/Stripe/lean-genius/doctor-{b..h}` + `.loom/worktrees/issue-38065`;
collector = doctor-h (cpus 21-23, cache -h). Model: Sonnet default, escalate to Fable on genuine capability-fail.
Infra gotcha: re-login/session-limit detaches tracking tasks but LEAVES docker containers running → zombie
100%-CPU builds; kill long-uptime containers + re-verify with hard `timeout`; never trust empty-output "completed".
