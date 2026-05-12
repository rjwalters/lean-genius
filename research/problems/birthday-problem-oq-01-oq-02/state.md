# Current State

**Phase**: OBSERVE
**Since**: 2026-05-11 (S1)
**Iteration**: 1

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
