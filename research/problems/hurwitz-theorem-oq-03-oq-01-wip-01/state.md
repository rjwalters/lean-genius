# Research State: hurwitz-theorem-oq-03-oq-01-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 4

## Current Focus
Frobenius Step 3 *preparation* lemma VERIFIED: `anticommutator_real_affine`
(`x*y + y*x ∈ span_ℝ {x, y, 1}` for all x, y). The one remaining sorry is still the
strictly non-commutative global-structure argument.

## Active Approach
Whittling the Clifford structure down from provable pieces:
- commutative → hurwitz_only_if_ring_comm (0 sorry): Gelfand-Mazur. VERIFIED (iter 3).
- `anticommutator_real_affine` (0 sorry, NEW iter 4): polarise the Step-1 quadratics of
  x, y, x+y ⟹ x*y + y*x = c₁•x + c₂•y + c₃•1. The first algebraic constraint toward the
  Clifford relations. VERIFIED.
- non-commutative → remaining sorry (Clifford / Radon-Hurwitz, blocked on Mathlib).

## Attempt Count
- Total attempts: 2 (code, shipped)
- Approaches tried: 2

## Blockers
- Non-commutative case genuinely open: needs Clifford-algebra / positive-definite
  anticommutator bilinear-form machinery not yet in Mathlib.
- The keystone anticommutator lemma (xy+yx ∈ ℝ·1 for *imaginary* x,y) still needs the
  trace-additivity / Im A subspace-closure that drops the x,y coefficients in
  `anticommutator_real_affine` to 0. That closure is the remaining hard step.

## Next Action
Prove trace-additivity: define the real-part functional `re : A → ℝ` (from Step-1's `p/2`)
and show it is ℝ-linear, so imaginary x, y ⟹ x+y imaginary ⟹ c₁ = c₂ = 0 in
`anticommutator_real_affine`, yielding `x*y + y*x ∈ ℝ•1`. Then Im A is a subspace and the
bilinear form `-(xy+yx)` is defined. Aristotle unusable (OPEN, not tactical).
