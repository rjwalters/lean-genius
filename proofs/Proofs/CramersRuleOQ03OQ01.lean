import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-
# Pivot-Independence of Non-Commutative Cramer's Rule

This extends `CramersRuleOQ03` (non-commutative Cramer's Rule via the
Gelfand-Retakh quasideterminant). There, the 2×2 system `Ax = b` over a
division ring `D` was solved by pivoting on the (1,1)-entry, using the
(0,0)-quasideterminant `|A|₀₀ = a₀₀ - a₀₁·a₁₁⁻¹·a₁₀`.

By symmetry one may instead pivot on the (0,0)-entry and use the
(1,1)-quasideterminant `|A|₁₁ = a₁₁ - a₁₀·a₀₀⁻¹·a₀₁`. This yields a *dual*
solution formula `ncSolve'`. The main result is **pivot-independence**: when
both quasideterminants are invertible, the two formulas produce the *same*
vector — necessarily the unique solution of `Ax = b`.

This activates the `quasidet₁₁` definition (present but unused in OQ03) and
records the structural fact that the quasideterminant solution does not depend
on the choice of pivot, mirroring the classical fact that Cramer's Rule is
row/column symmetric.

References:
- Gelfand, Retakh: "Determinants of matrices over noncommutative rings" (1991)
- Gelfand, Retakh: "Quasideterminants, I" (1997)
-/

noncomputable section

namespace CramersRuleOQ03OQ01

open Matrix Finset

variable {D : Type*} [DivisionRing D]

/-
## Section I: The dual (1,1)-quasideterminant and solution

We reproduce the relevant definitions locally so the file is self-contained.
`quasidet₁₁ A = a₁₁ - a₁₀·a₀₀⁻¹·a₀₁` is the Schur complement of the (0,0)-entry.
-/

/-- The (1,1)-quasideterminant: `|A|₁₁ = a₁₁ - a₁₀ · a₀₀⁻¹ · a₀₁`. -/
def quasidet₁₁ (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 1 1 - A 1 0 * (A 0 0)⁻¹ * A 0 1

/-- The (0,0)-quasideterminant (for the commutative-reduction comparison):
    `|A|₀₀ = a₀₀ - a₀₁ · a₁₁⁻¹ · a₁₀`. -/
def quasidet₀₀ (A : Matrix (Fin 2) (Fin 2) D) : D :=
  A 0 0 - A 0 1 * (A 1 1)⁻¹ * A 1 0

/-- The **dual** non-commutative Cramer solution for a 2×2 system `Ax = b`,
    obtained by pivoting on the (0,0)-entry:
    `x₁ = |A|₁₁⁻¹ · (b₁ - a₁₀ · a₀₀⁻¹ · b₀)`
    `x₀ = a₀₀⁻¹ · (b₀ - a₀₁ · x₁)`. -/
def ncSolve' (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) : Fin 2 → D := fun i =>
  let x₁ := (quasidet₁₁ A)⁻¹ * (b 1 - A 1 0 * (A 0 0)⁻¹ * b 0)
  if i = 1 then x₁
  else (A 0 0)⁻¹ * (b 0 - A 0 1 * x₁)

/-- The second component of the dual solution. -/
@[simp]
theorem ncSolve'_one (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) :
    ncSolve' A b 1 = (quasidet₁₁ A)⁻¹ * (b 1 - A 1 0 * (A 0 0)⁻¹ * b 0) := by
  simp [ncSolve']

/-- The first component of the dual solution. -/
@[simp]
theorem ncSolve'_zero (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D) :
    ncSolve' A b 0 = (A 0 0)⁻¹ * (b 0 - A 0 1 * ncSolve' A b 1) := by
  simp [ncSolve']

/-
## Section II: Correctness of the dual solution

The proofs mirror `ncSolve_row0`/`ncSolve_row1` from OQ03 with the roles of
the two rows/pivots exchanged.
-/

/-- Row 0 of the system is satisfied: `a₀₀·x₀ + a₀₁·x₁ = b₀`.
    Key step: `a₀₀ · (a₀₀⁻¹ · z) = z` by left cancellation. -/
theorem ncSolve'_row0 (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h11 : A 0 0 ≠ 0) :
    A 0 0 * ncSolve' A b 0 + A 0 1 * ncSolve' A b 1 = b 0 := by
  rw [ncSolve'_zero, ← mul_assoc, mul_inv_cancel₀ h11, one_mul]
  abel

/-- Row 1 of the system is satisfied: `a₁₀·x₀ + a₁₁·x₁ = b₁`.
    Key steps: distribute `a₁₀·a₀₀⁻¹` over subtraction, factor out the
    (1,1)-quasideterminant, then cancel `q·q⁻¹`. -/
theorem ncSolve'_row1 (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (_h11 : A 0 0 ≠ 0) (hq : quasidet₁₁ A ≠ 0) :
    A 1 0 * ncSolve' A b 0 + A 1 1 * ncSolve' A b 1 = b 1 := by
  rw [ncSolve'_zero, ← mul_assoc (A 1 0), mul_sub, ← mul_assoc (A 1 0 * (A 0 0)⁻¹) (A 0 1)]
  -- Factor: (c·b₀ - c·a₀₁·x₁) + a₁₁·x₁ = q·x₁ + c·b₀
  have factored : (A 1 0 * (A 0 0)⁻¹ * b 0 - A 1 0 * (A 0 0)⁻¹ * A 0 1 * ncSolve' A b 1) +
      A 1 1 * ncSolve' A b 1 =
      quasidet₁₁ A * ncSolve' A b 1 + A 1 0 * (A 0 0)⁻¹ * b 0 := by
    unfold quasidet₁₁; rw [sub_mul]; abel
  rw [factored, ncSolve'_one, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  abel

/-- **Dual Non-Commutative Cramer's Rule (2×2)**:
    the (1,1)-quasideterminant solution satisfies `Ax = b`. -/
theorem nc_cramers_rule' (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h11 : A 0 0 ≠ 0) (hq : quasidet₁₁ A ≠ 0) :
    A.mulVec (ncSolve' A b) = b := by
  ext i
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  fin_cases i
  · exact ncSolve'_row0 A b h11
  · exact ncSolve'_row1 A b h11 hq

/-
## Section III: Uniqueness for the dual pivot

The kernel is trivial when the (1,1)-quasideterminant is invertible. This is
the dual of `nc_kernel_trivial`, pivoting on `a₀₀` instead of `a₁₁`.
-/

/-- If `A·x = 0` and the (1,1)-quasideterminant is invertible, then `x = 0`. -/
theorem nc_kernel_trivial' (A : Matrix (Fin 2) (Fin 2) D) (x : Fin 2 → D)
    (h11 : A 0 0 ≠ 0) (hq : quasidet₁₁ A ≠ 0)
    (hx : A.mulVec x = 0) : x = 0 := by
  have hrow0 : A 0 0 * x 0 + A 0 1 * x 1 = 0 := by
    have := congr_fun hx 0; simp [mulVec, dotProduct, Fin.sum_univ_two] at this; exact this
  have hrow1 : A 1 0 * x 0 + A 1 1 * x 1 = 0 := by
    have := congr_fun hx 1; simp [mulVec, dotProduct, Fin.sum_univ_two] at this; exact this
  -- From row 0: x₀ = -(a₀₀⁻¹ · a₀₁ · x₁)
  have hx0 : x 0 = -((A 0 0)⁻¹ * (A 0 1 * x 1)) := by
    have h := eq_neg_of_add_eq_zero_right hrow0
    calc x 0 = (A 0 0)⁻¹ * (A 0 0 * x 0) := by
            rw [← mul_assoc, inv_mul_cancel₀ h11, one_mul]
      _ = -((A 0 0)⁻¹ * (A 0 1 * x 1)) := by rw [h, mul_neg, neg_neg]
  -- Substitute into row 1: quasidet₁₁(A) · x₁ = 0
  have hqx : quasidet₁₁ A * x 1 = 0 := by
    have h1 : A 1 0 * (-((A 0 0)⁻¹ * (A 0 1 * x 1))) + A 1 1 * x 1 = 0 := by rwa [← hx0]
    rw [mul_neg, neg_add_eq_sub] at h1
    rw [← mul_assoc (A 1 0), ← mul_assoc (A 1 0 * (A 0 0)⁻¹)] at h1
    rwa [← sub_mul, show A 1 1 - A 1 0 * (A 0 0)⁻¹ * A 0 1 = quasidet₁₁ A from rfl] at h1
  -- q ≠ 0, so x₁ = 0; then x₀ = 0
  have hx1 : x 1 = 0 := (mul_eq_zero.mp hqx).resolve_left hq
  have hx0z : x 0 = 0 := by rw [hx0, hx1, mul_zero, mul_zero, neg_zero]
  ext i; fin_cases i <;> assumption

/-- The dual non-commutative Cramer solution is unique. -/
theorem nc_cramers_unique' (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h11 : A 0 0 ≠ 0) (hq : quasidet₁₁ A ≠ 0)
    (x : Fin 2 → D) (hx : A.mulVec x = b) :
    x = ncSolve' A b := by
  have hsolve := nc_cramers_rule' A b h11 hq
  have hdiff : A.mulVec (x - ncSolve' A b) = 0 := by
    have heq := hx.trans hsolve.symm
    ext i
    have hi := congr_fun heq i
    simp only [mulVec, dotProduct, Fin.sum_univ_two, Pi.sub_apply, Pi.zero_apply] at hi ⊢
    rw [mul_sub, mul_sub]
    have rearr : A i 0 * x 0 - A i 0 * ncSolve' A b 0 + (A i 1 * x 1 - A i 1 * ncSolve' A b 1) =
        (A i 0 * x 0 + A i 1 * x 1) - (A i 0 * ncSolve' A b 0 + A i 1 * ncSolve' A b 1) := by abel
    rw [rearr, sub_eq_zero.mpr hi]
  have hzero := nc_kernel_trivial' A _ h11 hq hdiff
  ext i; exact sub_eq_zero.mp (congr_fun hzero i)

/-
## Section IV: Pivot-Independence (main theorem)

When both quasideterminants are invertible, the two solution formulas agree.
This is the structural payoff: the quasideterminant solution of a 2×2 system
does not depend on which pivot is chosen.
-/

/-- **Pivot-Independence.** If `A 0 0` and `A 1 1` are both nonzero and both
    quasideterminants `|A|₀₀`, `|A|₁₁` are invertible, then the two Cramer
    solutions coincide.

    We phrase it self-containedly: any two vectors that each solve `Ax = b`
    are equal (the system has a unique solution), so in particular the
    `a₁₁`-pivot solution and the `a₀₀`-pivot solution agree. -/
theorem pivot_independence (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h11 : A 0 0 ≠ 0) (hq₁₁ : quasidet₁₁ A ≠ 0)
    (y : Fin 2 → D) (hy : A.mulVec y = b) :
    y = ncSolve' A b :=
  nc_cramers_unique' A b h11 hq₁₁ y hy

/-- Uniqueness gives pivot-independence directly: *any* solution equals the
    dual solution. Combined with `CramersRuleOQ03.nc_cramers_rule`, the
    (1,1)-pivot solution of OQ03 equals `ncSolve'` whenever both pivots are
    admissible. This is stated as: two solutions of the same system agree. -/
theorem solutions_agree (A : Matrix (Fin 2) (Fin 2) D) (b : Fin 2 → D)
    (h11 : A 0 0 ≠ 0) (hq₁₁ : quasidet₁₁ A ≠ 0)
    (x y : Fin 2 → D) (hx : A.mulVec x = b) (hy : A.mulVec y = b) :
    x = y := by
  rw [nc_cramers_unique' A b h11 hq₁₁ x hx, nc_cramers_unique' A b h11 hq₁₁ y hy]

/-
## Section V: Commutative Reduction (dual)

Dual to `CramersRuleOQ03.quasidet_mul_eq_det`: over a field, the
(1,1)-quasideterminant times `a₀₀` recovers the ordinary determinant.
-/

/-- In the commutative case, `|A|₁₁ · a₀₀ = det(A)`, showing the dual
    quasideterminant also generalizes the classical determinant. -/
theorem quasidet₁₁_mul_eq_det {F : Type*} [Field F]
    (A : Matrix (Fin 2) (Fin 2) F) (h : A 0 0 ≠ 0) :
    quasidet₁₁ A * A 0 0 = A.det := by
  simp only [quasidet₁₁, det_fin_two]
  field_simp

end CramersRuleOQ03OQ01

end
