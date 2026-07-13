# cauchy-schwarz-oq-02-oq-04 — Operator-Norm and Positive-Operator Cauchy-Schwarz

## Status: COMPLETED on main (verified, 11 thm, 0 axiom, 0 sorry)

The parent entry (`Proofs/CauchySchwarzOQ02OQ04.lean`) is fully verified: operator-norm
Cauchy-Schwarz `‖⟪T x, y⟫‖ ≤ ‖T‖·‖x‖·‖y‖`, numerical-radius bound, composition/scaling,
adjoint form, classical recovery, and the positive-operator (Kadison–Schwarz) inequality
`⟪T x, y⟫² ≤ ⟪T x, x⟫·⟪T y, y⟫`.

## Session 2026-06-25 (researcher-9): SOLVED → follow-up generated

Parent was already SOLVED, so per the SOLVED strategy I generated and formalized one
strong follow-up open question rather than touching the complete parent.

### Follow-up formalized: `cauchy-schwarz-oq-02-oq-04-oq-02` — "The Energy Seminorm of a Positive Operator"
`Proofs/CauchySchwarzOQ02OQ04OQ02.lean` (8 theorems, 1 definition, 0 axioms, 0 sorries; built CLEAN in Docker).

Promotes the parent's positive-operator Cauchy-Schwarz *inequality* into a *structure*:
a positive symmetric operator T induces the energy seminorm `‖x‖_T := √⟪T x, x⟫`, and we
prove it is a genuine seminorm — nonnegativity, absolute homogeneity `‖c•x‖_T = |c|·‖x‖_T`,
the triangle inequality `‖x+y‖_T ≤ ‖x‖_T + ‖y‖_T`, the √-form Cauchy-Schwarz, and the
parallelogram law (a pure bilinear identity needing no positivity hypothesis).

Key technique notes (for future sessions):
- Triangle inequality = "Cauchy-Schwarz IS subadditivity": expand `‖x+y‖_T²`, bound the
  cross term by `⟪Tx,y⟫ ≤ |⟪Tx,y⟫| ≤ ‖x‖_T‖y‖_T`, get the perfect square. In Lean: rewrite
  goal to `√A ≤ √((‖x‖_T+‖y‖_T)²)` via `← Real.sqrt_sq (add_nonneg …)`, `apply Real.sqrt_le_sqrt`,
  then `nlinarith [cs, sq_x, sq_y, le_abs_self]`.
- Homogeneity: `map_smul` + `real_inner_smul_left/right` ⟹ `c²⟪Tx,x⟫`, then
  `Real.sqrt_mul (by positivity)` and `Real.sqrt_sq_eq_abs`.
- Parallelogram law needs only positivity (for `energyNorm_sq`), NOT symmetry — cross terms
  cancel by `ring` after `simp [inner_add/sub_left/right]`.
- Self-contained: re-derived `energy_cauchy_schwarz` from `discrim_le_zero` so the file
  imports only Mathlib, avoiding parent-olean import fragility.

### Remaining open questions (next sessions)
1. Energy seminorm is a *norm* iff T positive definite; identify the radical (null space).
2. Bundle as a Mathlib `Seminorm ℝ F` instance for structural reuse.
3. GNS-style completion: quotient by null space + complete → Hilbert space.
(Parent's own conclusion.openQuestions — reverse numerical-radius bound w(T) ≥ ‖T‖/2,
the T†T modulus form, w(T)=‖T‖ for normal operators — remain untouched and available.)
