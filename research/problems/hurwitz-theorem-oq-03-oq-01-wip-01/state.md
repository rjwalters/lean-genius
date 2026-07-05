# Research State: hurwitz-theorem-oq-03-oq-01-wip-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-04
**Iteration**: 5

## Current Focus
Iter 5 (Docker blackout — `docker run` EIO, no kernel-check possible): **gallery-sync
increment**. The gallery `meta.json` for `hurwitz-theorem-oq-03-oq-01` was stale by two
merged/verified commits (#34762 `hurwitz_only_if_ring_comm`, #34770
`anticommutator_real_affine`) — it still reported 231 lines / 7 theorems and omitted both
new theorems from `originalContributions`, `assumptions`, and `sections`. Synced counts
(281 lines / 9 theorems), added the `frobenius-step3-prep` section, and documented both
verified additions. No new Lean written (blackout precludes verification of hard Step-3
math). The one remaining sorry is unchanged: the strictly non-commutative global-structure
argument.

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
(Requires working Docker to kernel-check — do not attempt new hard Lean under blackout.)
Prove trace-additivity: define the real-part functional `re : A → ℝ` (from Step-1's `p/2`)
and show it is ℝ-linear, so imaginary x, y ⟹ x+y imaginary ⟹ c₁ = c₂ = 0 in
`anticommutator_real_affine`, yielding `x*y + y*x ∈ ℝ•1`. Then Im A is a subspace and the
bilinear form `-(xy+yx)` is defined. Aristotle unusable (OPEN, not tactical).

CAUTION on `re` well-definedness: the shift constant `c(a)=p/2` from
`exists_real_shift_sq_scalar` is NOT unique for scalars a=s•1 (every c gives a real
square), so the real-part functional cannot be read off the ad-hoc quadratic. The clean
route is via `minpoly ℝ a` (degree ≤2, genuinely unique): for a ∉ ℝ•1, minpoly = X²−t·X+n
and `re a := t/2`; for a ∈ ℝ•1, `re a := s`. Uniqueness of the ℝ-or-ℂ subalgebra structure
then gives ℝ-linearity. Build this on Mathlib's `minpoly` API rather than `exists_quadratic`.
