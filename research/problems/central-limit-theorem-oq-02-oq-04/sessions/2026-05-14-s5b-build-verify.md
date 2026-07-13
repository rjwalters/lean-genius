# Session 2026-05-14 — S5b build-verify (researcher-9)

## Scope

Doc-only STATE-SYNC retiring the `(build pending)` qualifier on PR #18728
(S5b ACT — `davydov_indicator_bound`, ingredient 3 of the Davydov L^p
covariance-inequality decomposition; merged 2026-05-13T10:17:09Z).

## Why this is doc-only

PR #18728 shipped under `(build pending)` citing the host worktree's
self-referential `proofs/.lake` symlink ("Too many levels of symbolic
links"). That symlink is irrelevant to `./proofs/scripts/docker-build.sh`,
which mounts its own `/lean/.lake` inside the Docker container and ignores
the host directory. This is the canonical false-alarm pattern documented in
researcher memory (`feedback_researcher_build_pending_dot_lake_symlink_false_alarm.md`).

## Build evidence

From a fresh worktree off `origin/main 2afb1b79c0a`:

```
./proofs/scripts/docker-build.sh Proofs.CentralLimitTheoremOQ02OQ04

(cold mathlib clone, 7727 cache files downloaded from Azure)
⚠ [3130/3131] Replayed Proofs.CentralLimitTheoremOQ02
⚠ [3131/3131] Built Proofs.CentralLimitTheoremOQ02OQ04 (3.3s)
Build completed successfully (3131 jobs).
```

Full log: `.loom/logs/researcher-9-clt-s5b-verify-build.log`.

## Sorries surfaced

The expected 2 sorries (matches `meta.json` `sorries: 2`):

* `Proofs/CentralLimitTheoremOQ02OQ04.lean:475:8` — `davydov_covariance_inequality`
  (L^p Davydov inequality, S5c target ~100 LOC: level-set decomposition +
  Hölder + Markov).
* `Proofs/CentralLimitTheoremOQ02OQ04.lean:671:8` — `mixing_clt_ibragimov`
  (S6+ target: Bernstein blocks + Lindeberg-Feller).

Parent file `Proofs/CentralLimitTheoremOQ02.lean` has its own 3 sorries
(lines 480, 519, 538), all reused-by-reference and not in scope for this slug.

## Linter warning (out of scope)

```
Proofs/CentralLimitTheoremOQ02OQ04.lean:419:12: This simp argument is unused:
  Set.indicator_apply
```

The `indicator_pair_covariance_eq` proof (S4 contribution from PR #17939,
**not** part of S5b's contribution) uses
`by_cases hωA <;> by_cases hωB <;> simp [Set.indicator_apply, Set.mem_inter_iff, hωA, hωB]`,
where under Mathlib v4.26.0 the four explicit case splits unfold the
indicator without needing `Set.indicator_apply` in the simp set. Flagged
here for a future cleanup pass; **not bundled** with this build-verify
STATE-SYNC to keep scope minimal (cf. PR #19025 cayley-hamilton-minpoly-oq-03-oq-02
S2 build-verify template).

## State changes

* `research/problems/central-limit-theorem-oq-02-oq-04/state.md`:
  - Top-of-file `Phase` / `Since` / `Iteration` / `Last Updated` fields advanced.
  - S5b section retitled to `(researcher-3, 2026-05-13, PR #18728 — …)` (was `this PR`).
  - Build-status block flipped from `[BUILD PENDING]` to `[BUILD VERIFIED]`
    with the actual `[3131/3131]` build line, and the symlink-deferral
    rationale replaced by the Docker-isolation note.
  - New preamble section above S5b documenting this build-verify session.

* `src/data/research/problems/central-limit-theorem-oq-02-oq-04.json`:
  - Top-level `phase`: `ORIENT` → `ACT` (gallery-listings drift fix —
    `phase` is aggregated by `scripts/research/build.ts` into
    `research-listings.json` consumed by `ResearchPage`; cf. researcher memory
    `feedback_researcher_state_sync_misses_top_level_phase`).
  - Top-level `lastUpdate`: `2026-05-12T14:00:00Z` → `2026-05-14T03:50:00Z`.
  - `currentState.since`: → `2026-05-14T03:50:00Z`.
  - `currentState.iteration`: `5` → `7` (S5a + S5b shipped between sync points).
  - `currentState.focus`: rewritten to reflect S5b shipped + build verified.
  - `currentState.nextAction`: refocused on S5c (was: S5b, now superseded).
  - `knowledge.progressSummary`: prepended with the S5b-shipped + build-verified note.
  - `knowledge.nextSteps[0]`: `S5a ACT (mechanic-pass)` → `S5c ACT (~100 LOC)`
    (S5a/S5b already shipped; next concrete target is the L^p density step).

* No changes to `meta.json` — already reflects post-S5b state
  (`sorries: 2`, `lineCount: 684`, `theoremCount: 12`, `axiomCount: 0`).
* No Lean changes.

## Next iteration (S5c)

S5c ACT (~100 LOC): discharge the L^p density step of
`davydov_covariance_inequality`. All three named order-theory ingredients
are now build-verified, so the path is purely measure-theoretic:

1. **Level-set decomposition**: write `X = ∫₀^∞ (𝟙_{X>t} − 𝟙_{X<−t}) dt`
   (similarly for `Y`).
2. **Bilinear expansion**: expand `Cov(X, Y)` into a double integral
   `∫∫ Cov(𝟙_{X>s}, 𝟙_{Y>t}) ds dt` over the four indicator pairs.
3. **Pointwise application**: apply the now-proven `davydov_indicator_bound`
   inside the integral.
4. **Hölder + Markov**: bound the integral by
   `12 · α^{(p−2)/p} · ‖X‖_p · ‖Y‖_p` via Hölder on the truncated piece and
   Markov's inequality on the tail.

Reference: Doukhan 1994 §1.2.2, Bradley 2007 Vol I Thm 3.7.

Now that the verification pipeline is known good, S5c can ship verified-build
from day one — no `(build pending)` qualifier needed.
