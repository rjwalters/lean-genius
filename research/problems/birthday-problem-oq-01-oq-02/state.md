# Current State

**Phase**: S3 ACT + S4 PREP merged (Path Z scaffold ready, paste-ready against main)
**Since**: 2026-05-15T23:30:27Z (S3 ACT PR #19098 merged; STATE-SYNC researcher-3)
**Iteration**: 6

## S5 update (this PR, 2026-05-16, researcher-3, STATE-SYNC post-S3-ACT-merge)

Post-merge STATE-SYNC catching `state.md` and the website JSON up to the
post-S3-ACT-merge reality:

- PR #19098 (S3 ACT, Markov closed-form `probCollision_le_choose_two_div`,
  build verified 7744 jobs) **MERGED** 2026-05-15T23:30:27Z (merge commit
  `e44038366d8df3c9be9c65858e63c6997b7e1646`). `proofs/Proofs/BirthdayProblemOQ01OQ02.lean`
  is now 143 LOC on main, 2 theorems, 0 sorries, 0 axioms.
- 0 open PRs on the slug or on the file at this STATE-SYNC's commit time;
  no rebase risk for S4 ACT.
- Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` unchanged in the ~5.5h
  since S4c PREP (researcher-9, PR #19315 merged 19:47Z); 9-row bearer
  drift table is byte-stable.

This iteration ships:

- Bearer drift recheck (same 9 bearers as S4c §3, byte-stability argument
  via lake-manifest immutability). **Net: 0 rows drifted.**
- S4 ACT readiness gate refresh — Option A/B stacking choice from S4c §4b
  is **settled by event** (Option B selected; #19098 merged within drain
  wave). The next S4 ACT worker writes a clean 25-LOC delta against
  `origin/main` HEAD `d35a6f0f`; no overlay-stack work owed.
- Paste-anchor pin: PR #19250 §4's 25-LOC scaffold inserts between L142
  (`  exact hbound`, last line of `probCollision_le_choose_two_div`) and
  L143 (`end BirthdayProblemOQ01OQ02`). New failure-mode row F7 (paste
  outside namespace) added to the F1–F6 register.
- OQ01 parent-regression catalogue re-verified: L408 `Nat.choose_three_right (m + 2)`
  unchanged; L508–511 four `native_decide` examples unchanged; no
  mechanic / doctor PR has touched the file since S4c.

See `sessions/2026-05-16-s5-state-sync-post-s3-act-merge.md` for the full
post-merge snapshot, byte-stability methodology note, settled-by-event
stacking analysis, paste-anchor pin, refreshed failure-mode register, and
re-verified OQ01 handoff catalogue.

## S4c update (2026-05-15, researcher-9, STATE-SYNC + drift recheck)

STATE-SYNC catching `state.md` and the website JSON up to the post-18:00-drain
reality:

- PR #19098 (S3 ACT, Markov closed-form `probCollision_le_choose_two_div`,
  build verified 7744 jobs) is OPEN/MERGEABLE on `BirthdayProblemOQ01OQ02.lean`.
- PR #19250 (S4 PREP, Path Z 25-LOC scaffold for the Paley-Zygmund-equivalent
  lower bound `probCollision_ge_paley_zygmund`) MERGED 2026-05-15T18:03:33Z.
- PR #19262 (S4b PREP, bearer-pin re-verification + numerical witness for
  PR #19250) MERGED 2026-05-15T18:02:47Z.

This iteration ships:

- Drift recheck (9 bearer rows: 5 from S3 ACT + 4 from S4 PREP) against lake
  SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`. **Net: 0 rows drifted.**
- S4 ACT readiness gate (entry conditions, stacking-strategy choice A vs B,
  paste sequence, 6-row failure-mode register).
- OQ01 parent-regression handoff catalogue (7 v4.26.0 errors with replacement
  candidates; `Nat.choose_three_right` confirmed absent from Mathlib v4.26.0).

See `sessions/2026-05-15-s4c-prep-state-sync-and-act-readiness-gate.md` for
the full STATE-SYNC + drift recheck + readiness gate.

## S4b update (2026-05-15, researcher-8)

PR #19262 strict-sibling audit of PR #19250 §5 bearer table:

- 4/4 named Path Z bearers re-verified at lake SHA `2df2f015...`:
  `Real.add_one_le_exp` (Exponential.lean:646), `Real.exp_neg` (Exponential.lean:236
  inside `namespace Real` 198-346), `one_div_le_one_div_of_le` (Field/Basic.lean:77).
- Flagged `Complex.exp_neg` co-existence at Exponential.lean:161 (`namespace
  Complex` 88-196) — advised explicit `Real.` qualifier in the Path Z bridge.
- Surveyed for direct 1-line bearers for `x/(1+x) ≤ 1 - exp(-x)` at the pin:
  0 hits, confirming PR #19250's choice to chain three bearers is canonical.

## S4 update (2026-05-15, researcher-8)

PR #19250 doc-only design memo proposing **Path Z** — Paley-Zygmund-equivalent
lower bound via exponential composition (recommended over Path X / Path Y):

| Path | Approach | LOC | Status |
|------|----------|----:|-------|
| X    | OQ01-import named bound (`variancePairs_le_expected`) | ~60 | ❌ blocked by 7-error v4.26.0 regression in `BirthdayProblemOQ01.lean` |
| Y    | full closed-form Paley-Zygmund via E[X²] expansion (gain Δ ≈ 0.0003) | ~120 | ⚠ overlong for the marginal tightening |
| **Z**| chain OQ02.probCollision_ge (already-shipped exponential lower bound) with `1 - exp(-x) ≥ x/(1+x)` via `Real.add_one_le_exp` | ~25 | ✅ recommended |

Ships a paste-ready 25-LOC scaffold materialising `probCollision_ge_paley_zygmund`
as:

```lean
probCollision k d ≥ k(k-1) / (2d + k(k-1))
```

Match: `knowledge.md` §"Paley–Zygmund bound" weak form.

## S3 update (2026-05-14, researcher-?)

PR #19098 shipped the Markov coupling closed-form theorem in
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean`:

```lean
theorem probCollision_le_choose_two_div (k d : ℕ) (hkd : k ≤ d) (hd : 0 < d) :
    probCollision k d ≤ (k : ℝ) * ((k : ℝ) - 1) / (2 * (d : ℝ))
```

- 1 new theorem (`probCollision_le_choose_two_div`) chained on S2's
  `one_sub_prod_le_sum` (line 38) + OQ02's `gauss_sum_div` (OQ02:145).
- 0 sorries, 0 new axioms, 0 changes to OQ01 / OQ02 namespace.
- **Docker build verified**: 7744 jobs, 11s warm cache.
- Closed form `k(k-1)/(2d)` chosen over `expectedPairs` form to avoid
  importing the v4.26.0-regressed parent `Proofs.BirthdayProblemOQ01`
  (7 errors at L410-511 — see S4c session note §5 for catalogue).
- Together with OQ02's `probCollision_ge` (exponential lower bound, OQ02:173),
  brackets `probCollision` between `1 - exp(-k(k-1)/(2d))` and `k(k-1)/(2d)`.

## S2 update (2026-05-13, researcher-10)

Created `proofs/Proofs/BirthdayProblemOQ01OQ02.lean` (~80 LOC) with the
single helper theorem `one_sub_prod_le_sum` per S1 §"Next Action" sketch:

```lean
theorem one_sub_prod_le_sum {n : ℕ} (f : ℕ → ℝ)
    (hnn : ∀ i, i < n → 0 ≤ f i) (hle : ∀ i, i < n → f i ≤ 1) :
    1 - ∏ i ∈ Finset.range n, (1 - f i)
      ≤ ∑ i ∈ Finset.range n, f i
```

- 0 sorries, 0 new axioms.
- Proof by induction on `n`. Successor step uses `Finset.prod_range_succ` +
  `Finset.sum_range_succ`, then closes with `nlinarith` given the
  side-conditions `0 ≤ ∏ ≤ 1` (from `Finset.prod_nonneg` /
  `Finset.prod_le_one`) and the product hint
  `mul_nonneg (sub_nonneg.mpr hP_le_one) hfk_nn`.
- **Build status**: pending Docker verification
  (`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ02`).
  Per the lake-symlink-loop trap precedent, shipping the file as a
  build-pending PR so the Auditor or Doctor can verify from a clean
  worktree.

## Next Action (S4 ACT, paste-ready against main)

**S4 ACT (next Lean-modifying iteration)**: Paste PR #19250 §4's 25-LOC
Path Z scaffold (private `one_sub_exp_neg_ge_div_one_add` bridge lemma +
public `probCollision_ge_paley_zygmund` theorem) into
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean` BETWEEN L142 (`  exact hbound`,
last line of `probCollision_le_choose_two_div`) and L143
(`end BirthdayProblemOQ01OQ02`). Run
`./proofs/scripts/docker-build.sh Proofs.BirthdayProblemOQ01OQ02`.
Expected: 0 sorries, ~7745 jobs, ~11–13s warm cache.

**Stacking choice — settled by event**: PR #19098 (S3 ACT) merged at
2026-05-15T23:30:27Z (merge commit `e44038366d8`), eliminating the Option A
(overlay-stack) vs Option B (wait-for-merge) dilemma from S4c §4b. **Option
B selected by event**: write a clean 25-LOC delta against `origin/main`
HEAD `d35a6f0f` (or current head at paste time; the slug file is stable
with 0 open PRs).

**Pre-flight readiness gate**: all entry conditions GREEN as of 2026-05-16
~01:00 UTC — lake SHA unchanged at `2df2f015...`, all 9 bearers byte-stable
zero drift, **PR #19098 MERGED**, 0 competing open PRs on
`BirthdayProblemOQ01OQ02.lean`, STATE-SYNC complete (this iteration). See
`sessions/2026-05-16-s5-state-sync-post-s3-act-merge.md` §4 for the
post-merge gate (with new failure-mode row F7 for paste-anchor confusion)
and `sessions/2026-05-15-s4c-prep-state-sync-and-act-readiness-gate.md` §4
for the original F1–F6 register (unchanged).

**S5 PREP target** (deferred, distinct from this S5 STATE-SYNC): tighten
Paley-Zygmund denominator from `2d + k(k-1)` to `2d + k(k-1) - 2` (Δ ≈
0.0003 at threshold, gain via exact `E[X²]` instead of `Var ≤ E[X]` bound)
— per PR #19250 §R5. This iteration is **S5 STATE-SYNC**, not S5 PREP;
the Path Y elaboration remains owed to a future iteration.

---

## Original S1 OBSERVE state (preserved for reference)

## Current Focus

S1 (researcher-12): Initial survey of the coupling between
`BirthdayProblemOQ01.expectedPairs` (first-moment quantity, `ℚ`) and
`BirthdayProblemOQ02.probCollision` (probability quantity, `ℝ`).
Establishes:

1. **Markov coupling** `probCollision ≤ ↑expectedPairs` is a direct
   chain of `one_sub_prod_le_sum` (union bound for products) + the
   existing `gauss_sum_div` (`OQ02`). ~40 lines.
2. **Paley-Zygmund coupling** `probCollision ≥ E[X]² / E[X²]` is
   heavier — requires (a) the second-moment formula in OQ02-style and
   (b) a bridge to the OQ01OQ01 finite-sample-space `collisionCount`
   random variable. ~80 lines split over S5/S6.
3. **Bridge** `probAllDistinct n d = descFactorial(d,n) / d^n` unifies
   OQ02's product formulation and OQ01OQ01's counting formulation;
   needed for Paley-Zygmund but stands as its own ~30-line lemma.

## Active Approach

**Two complementary couplings, Markov first.**

The Markov path (S2 → S3) is mechanical: a new helper
`one_sub_prod_le_sum` + the existing `gauss_sum_div` + `two_mul_choose_two`
+ casts. This delivers the upper-bound half of the coupling.

The Paley-Zygmund path (S4 → S6 → S5) is heavier and depends on the
bridge S6 between OQ02 and OQ01OQ01. Deferred to multiple sessions.

The two couplings together place `probCollision` strictly between
`(C(n,2)/d) / (1 + C(n,2)/d)` (P-Z lower) and `C(n,2)/d` (Markov upper).
For `n ≥ 28` (`d = 365`) the lower bound is ≥ 1/2, recovering the
classical birthday threshold without invoking the exponential bound.

## Blockers

None mathematical. Practical: the `proofs/.lake` symlink is broken in
researcher worktrees (~25-45 min cost per Docker build), but S2/S3 are
short enough that one end-of-S3 Docker build is feasible.

## Next Action

**S2 (any researcher)**: Create
`proofs/Proofs/BirthdayProblemOQ01OQ02.lean` and add the helper:

```lean
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Group.Finset
import Proofs.BirthdayProblemOQ01
import Proofs.BirthdayProblemOQ02

namespace BirthdayProblemOQ01OQ02

open BirthdayProblemOQ01 BirthdayProblemOQ02 BigOperators

/-- Union-bound form: for `f` valued in `[0, 1]`,
    `1 - ∏ (1 - f i) ≤ ∑ f i`. -/
theorem one_sub_prod_le_sum {n : ℕ} (f : ℕ → ℝ)
    (hnn : ∀ i, i < n → 0 ≤ f i) (hle : ∀ i, i < n → f i ≤ 1) :
    1 - ∏ i ∈ Finset.range n, (1 - f i)
      ≤ ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ k ih =>
    -- ... use `Finset.prod_range_succ`, `Finset.sum_range_succ`,
    -- and the algebraic identity
    --   1 - (1-a)·P = a + (1-a)·(1-P)
    -- with the bound (1-a)·(1-P) ≤ 1-P from 0 ≤ 1-a ≤ 1.
    sorry

end BirthdayProblemOQ01OQ02
```

Verify with Docker build (`./proofs/scripts/docker-build.sh
Proofs.BirthdayProblemOQ01OQ02`) at the end of S2; ~25-45 min wall-clock
with the broken `.lake` symlink.

**S3 (next session after S2)**: Add the Markov coupling
`probCollision_le_expectedPairs`. Chains `one_sub_prod_le_sum` with
`gauss_sum_div` (OQ02:145) and `two_mul_choose_two` (OQ01:109) plus
`push_cast` for the ℚ → ℝ bridge.

## Attempt Counts

- Total attempts: 1 (S1 survey)
- Current approach attempts: 1
- Approaches tried: 1

## Open files

- `problem.md` — Plain statement, why-it-matters, Mathlib infrastructure
  map, S2-through-S6 decomposition, risk notes.
- `knowledge.md` — S1 session note: Markov 1-line proof, Paley-Zygmund
  formula, worked numerics for `n = 23` and `n = 50`, Mathlib gaps,
  next-action priority table.

## S1 Deliverable

This iteration is **survey-only**:

- 0 new theorems
- 0 new sorries
- 0 axioms touched
- 0 `.lean` files created

Substantive output: `problem.md` (Mathlib API map + suggested S2-S6
decomposition + risk notes) and `knowledge.md` (math content of both
couplings + worked numerics + Mathlib gap inventory). Ready hand-off
for the S2 implementer.
