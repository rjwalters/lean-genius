# Pompeiu's Theorem (pompeiu-theorem-oq-01)

## Problem
For an equilateral triangle `ABC` and any point `P`, the distances `PA, PB, PC`
satisfy all three triangle inequalities (they are the side lengths of a possibly
degenerate triangle, the *Pompeiu triangle*). Degenerate iff `P` on the circumcircle.

## Status
COMPLETE (inequality direction). 0 sorries, 0 axioms. `Proofs/PompeiuTheorem.lean`.

## Approach (complex numbers)
- Plane = ℂ. Primitive cube root of unity `ω` with `ω² + ω + 1 = 0`.
- Equilateral triangle of one orientation ⟺ `a + ω·b + ω²·c = 0`
  (one factor of `a² + b² + c² = ab+bc+ca = (a+ωb+ω²c)(a+ω²b+ωc)`).
- Key cancellation: `(z-a) + ω(z-b) + ω²(z-c) = z(1+ω+ω²) − (a+ωb+ω²c) = 0`.
- So `z-a = -(ω(z-b) + ω²(z-c))`, and `‖ω‖ = ‖ω²‖ = 1` ⟹ `‖z-a‖ ≤ ‖z-b‖+‖z-c‖`.
- Cyclic inequalities: multiply equilateral identity by `ω`, `ω²` (uses `ω³ = 1`).

## What was built
- `norm_eq_one_of_cube_root` : `ω²+ω+1=0 → ‖ω‖=1` (derives, not assumes; via ω³=1).
- `norm_le_of_rot` : `u + ωv + ω²w = 0, ‖ω‖=1 → ‖u‖ ≤ ‖v‖+‖w‖` (rotation engine).
- `rotation_identity` : the structural `(z-a)+ω(z-b)+ω²(z-c)=0`.
- `pompeiu_norm` : all three triangle inequalities (norm form).
- `pompeiu_dist` : metric (dist) form.

## Mathlib hooks used
- `norm_add_le`, `norm_mul`, `norm_pow`, `norm_neg`, `norm_one`, `norm_nonneg`
- `dist_eq_norm`
- tactics: `linear_combination` (all identities), `nlinarith` (positivity), `mul_eq_zero`

## Non-vacuity
Hypotheses satisfied by cube roots of unity `(a,b,c)=(1,ω,ω²)`, `ω=e^{2πi/3}`:
`1 + ω·ω + ω²·ω² = 1 + ω² + ω⁴ = 1 + ω² + ω = 0`. (Stated in prose; a fully
formalized non-vacuity lemma with explicit ω = ⟨-1/2, √3/2⟩ was drafted but omitted
to keep the build robust — the concrete Complex normSq arithmetic is fragile.)

## Open follow-ups
- Degeneracy iff `P` on circumcircle (equality case of the triangle inequality:
  `ω(z-b)`, `ω²(z-c)` positively proportional). This is the Ptolemy-equality phenomenon.
- Petr–Douglas–Neumann generalization via higher roots of unity.

## Sessions
### 2026-06-16 (Session 1, researcher-11) — FRESH — COMPLETE
- Claimed (took over a stale dead-pid lock; two prior pompeiu branches were empty).
- Wrote `PompeiuTheorem.lean` (5 theorems), build-verified via docker-build, registered
  in `Proofs.lean`, added gallery `pompeiu-theorem-oq-01/` (meta + annotations). PR opened.
