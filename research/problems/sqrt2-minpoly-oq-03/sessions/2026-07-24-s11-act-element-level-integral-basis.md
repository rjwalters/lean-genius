# S11 ACT (2026-07-24, researcher-3): the element-level integral basis of Q(√2)

## Goal

The S10 handoff asked for power-basis trace/norm formulas feeding
`int_pair_of_double_and_norm` to get `𝓞 = ℤ[√2]`. This session delivers that
milestone by a **shorter route**: minimal-polynomial descent.

## Outcome

`isIntegral_elt_iff (a b : ℚ) : IsIntegral ℤ (elt a b) ↔ (a ∈ ℤ) ∧ (b ∈ ℤ)`
where `elt a b = a + b·root` — the complete membership description of the ring
of integers. Host-verified `lake env lean` exit 0 on the pinned v4.31.0
toolchain (mathlib `9a9483a929`); the file's only diagnostic remains the
expected strategic sorry (`Q_sqrt2_discr_eq_eight`, L309). `#print axioms
isIntegral_elt_iff` = `[propext, Classical.choice, Quot.sound]` —
sorry-independent.

## Route (why no trace/norm formulas)

For `b ≠ 0` the minimal polynomial of `x = a + b·root` over ℚ **is**
`X² − 2aX + (a² − 2b²)` — i.e. `X² − (tr x)X + N(x)` — proved directly
(`minpoly_elt`): the quadratic annihilates `x` (`aeval_elt_quadratic`, one
`linear_combination (map b)² * root_sq`), is monic (`monic_X_pow_add`), and
the minpoly dividing it has degree ≥ 2 by irrationality
(`minpoly.two_le_natDegree_iff` + `elt_not_mem_range` ← `root_not_mem_range`
← `rat_int_of_sq_int` + `interval_cases`). Then integrality descends the
minpoly to ℤ (`minpoly.isIntegrallyClosed_eq_field_fractions'`), so both
coefficients are integers — precisely the two inputs `2a ∈ ℤ`, `a² − 2b² ∈ ℤ`
of the S10 crux `int_pair_of_double_and_norm`. Reverse inclusion:
`isIntegral_algebraMap` + `root_isIntegral` + closure under `+`/`*`, with the
tower rewrite `IsScalarTower.algebraMap_apply ℤ ℚ Q_sqrt2` (instance found
automatically).

This kills the planned `leftMulMatrix`/power-basis computation entirely.

## v4.31 gotchas (new)

* `Polynomial.degree_C_mul_le` does NOT exist; `Polynomial.degree_C_mul_X_le`
  does.
* `Polynomial.Monic.natDegree_eq_zero_iff_eq_one` does NOT exist; use
  `Polynomial.eq_C_of_natDegree_eq_zero` + unfold `Monic`/`leadingCoeff` at
  degree 0, then `Polynomial.C_1`.
* Coefficient extraction from `q = (minpoly ℤ x).map (algebraMap ℤ ℚ)`:
  use `congrArg (fun p => p.coeff i)` + `simp only` with the precise
  `coeff_add/coeff_X_pow/coeff_C_mul/coeff_X_one/coeff_C/coeff_map/eq_intCast`
  set. A plain `simpa` rewrites `C (a² − 2b²)` through the `map_sub`/`map_pow`
  simp lemmas first and strands terms like `(C a ^ 2).coeff 1`.
* `↑(-c) : ℚ` is an opaque atom to `linarith` — `rw [Int.cast_neg]` first.
* The ℤ→ℚ→(ℚ-algebra) `IsScalarTower` instance exists and
  `minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint` applies directly to
  `IsIntegral ℤ x` for `x` in any ℚ-algebra field (probe-verified before use).

## Next (S12)

1. Coordinate surjectivity: `∀ x : Q_sqrt2, ∃ a b : ℚ, x = elt a b` (power
   basis `AdjoinRoot.powerBasis`, dim 2 expansion).
2. Package `{1, root}` as `Basis (Fin 2) ℤ (𝓞 Q_sqrt2)` from
   `isIntegral_elt_iff` + (1).
3. `Q_sqrt2_discr_eq_eight` via `NumberField.discr_eq_discr` and the trace
   form `det [[2, 0], [0, 4]] = 8` (trace values now read off `minpoly_elt`:
   `tr(a + b·root) = 2a`).
