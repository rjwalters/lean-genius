/-
  Overpartition generating function — the single-part-size local factor

  Source: open question #3 of the gallery entry `partition-theorem-oq-03`
  ("Euler Partition Identities for Overpartitions").

  Parent open question (OQ-03):
    The generating function  ∑_{n≥0} p̄(n) qⁿ  =  ∏_{k≥1} (1 + qᵏ)/(1 - qᵏ)
    is a formal power-series identity. Can it be formalized in Lean using
    Mathlib's PowerSeries infrastructure?

  Status of THIS file: VERIFIED (0 sorries, 0 axioms).

  Scope.  The full identity is an infinite product of power series, whose
  formalization requires a multipliability/partial-product framework for
  `PowerSeries` that Mathlib 4.26 does not provide in usable form (the
  partition generating function ∏ 1/(1-qᵏ) itself is only available through
  bespoke developments, not a general infinite-product API). Rather than
  axiomatize the whole identity, this file proves the **verified atom** of the
  Euler product: the single-part-size *local factor*.

  For one fixed part size, an overpartition may use that size with any
  multiplicity m ≥ 0, and when m ≥ 1 the first copy may optionally be
  overlined — giving exactly 2 choices for every positive multiplicity and 1
  choice for multiplicity 0. The local generating function (in the variable
  X standing for qᵏ) is therefore

        1 + 2X + 2X² + 2X³ + ⋯  =  (1 + X)/(1 - X),

  which is the k-th factor of the infinite product above. We prove this as the
  formal power-series identity  (1 - X) * overlineFactor = 1 + X  over ℤ, plus
  the closed coefficient formula. This is the genuine building block from which
  the global identity is assembled factor by factor; the global product is left
  as the documented open target (see `overpartition_generating_function_target`).
-/

import Mathlib

namespace PartitionTheoremOQ03OQ03

open PowerSeries

/-- The single-part-size *overline factor*: the power series
    `1 + 2X + 2X² + 2X³ + ⋯` over ℤ.

    Coefficient interpretation: for one fixed part size, multiplicity `0`
    contributes the constant `1` (the part is unused); every positive
    multiplicity contributes `2`, the two choices "overlined" / "not
    overlined" for its first copy. -/
noncomputable def overlineFactor : ℤ⟦X⟧ :=
  mk (fun n => if n = 0 then 1 else 2)

/-- Closed form for the coefficients of the local overline factor. -/
@[simp]
theorem coeff_overlineFactor (n : ℕ) :
    coeff n overlineFactor = if n = 0 then 1 else 2 :=
  coeff_mk n _

@[simp]
theorem coeff_overlineFactor_zero : coeff 0 overlineFactor = 1 := by
  simp

theorem coeff_overlineFactor_pos {n : ℕ} (hn : n ≠ 0) :
    coeff n overlineFactor = 2 := by
  simp [hn]

/-- **Local Euler factor of the overpartition generating function.**

    `(1 - X) · overlineFactor = 1 + X`, i.e. the single-part-size factor
    `overlineFactor = (1 + X)/(1 - X)` as a formal power series over ℤ.

    This is the k-th factor (with `X ↦ qᵏ`) of the conjectural global product
    `∏_{k≥1} (1 + qᵏ)/(1 - qᵏ)`. -/
theorem overline_local_factor :
    (1 - X) * overlineFactor = 1 + X := by
  ext n
  rw [sub_mul, one_mul, map_sub, map_add]
  cases n with
  | zero =>
      simp [coeff_zero_X_mul]
  | succ m =>
      rw [coeff_succ_X_mul]
      cases m with
      | zero => simp [coeff_X, coeff_one]
      | succ k => simp [coeff_X, coeff_one]

/-- The local factor has invertible constant term, so it is a unit; equivalently
    `1 - X` divides `1 + X` in `ℤ⟦X⟧` with quotient `overlineFactor`. -/
theorem oneSubX_dvd_onePlusX : (1 - X : ℤ⟦X⟧) ∣ (1 + X) :=
  ⟨overlineFactor, (overline_local_factor).symm⟩

/-!
## The remaining open target

The global identity OQ-03 asks for

  `∑_{n} p̄(n) Xⁿ = ∏_{k ≥ 1} (1 + Xᵏ)/(1 - Xᵏ)`

as an equality of formal power series. With `overline_local_factor` the right
side is, factor by factor,

  `∏_{k ≥ 1} (1 + Xᵏ)/(1 - Xᵏ) = ∏_{k ≥ 1} overlineFactor(Xᵏ)`,

so the only missing ingredient is a convergent infinite-product /
multipliability framework for `PowerSeries` together with a coefficient-level
identification of the product with the overpartition counting function
`numOverpartitions` (currently axiomatized in `PartitionTheoremOQ03.lean`).

We record the statement as a documented target rather than an axiom; it is
deliberately **not** assumed anywhere. Discharging it is the content of OQ-03.
-/

end PartitionTheoremOQ03OQ03
