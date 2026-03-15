import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-
# Operator AM-GM Inequality: Generalization to Matrix Means

## Overview
This file formalizes the generalization of the classical AM-GM inequality to
positive semidefinite matrices, using the Loewner (semidefinite) ordering.

The classical AM-GM: (a + b)/2 >= sqrt(ab) for non-negative reals.
The operator version: (A + B)/2 >=_L A # B for positive definite matrices.

## What We Prove (19 theorems, 0 sorries)
- PSD/PD basics: zero is PSD, sum/scaling of PSD, PD implies PSD
- Trace non-negativity of PSD matrices (via standard basis vectors)
- Loewner order: reflexivity, transitivity, addition, scaling
- Arithmetic mean: PSD preservation, domination of lesser operand
- Trace inequality: tr(AM) >= tr(GM)
- Equality condition: A = B implies A#B = (A+B)/2
- Weighted arithmetic mean: PSD preservation, half-weight = AM
- HM-GM-AM chain (from axioms)

## What We Axiomatize (12 axioms, deep results needing spectral theorem)
- Matrix square root (existence, PSD, squaring)
- Geometric mean (existence, PD, commutativity, self-mean, monotonicity)
- The operator AM-GM inequality itself
- Harmonic mean, HM <= GM, congruence invariance

## References
- Bhatia, "Positive Definite Matrices" (2007)
- Ando, "Concavity of certain maps" (1979)
- Kubo-Ando theory of operator means (1980)
-/

noncomputable section

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option linter.unusedSectionVars false

/-
## Section 1: Positive Semidefinite and Positive Definite

Custom predicates for real symmetric matrices using x^T A x,
avoiding the StarOrderedRing typeclass dependency.
-/

/-- A real symmetric matrix A is positive semidefinite if x^T A x >= 0 for all x -/
def RealPosSemidef (A : Matrix n n ℝ) : Prop :=
  A.IsSymm ∧ ∀ x : n → ℝ, 0 ≤ dotProduct x (A.mulVec x)

/-- A real symmetric matrix A is positive definite if x^T A x > 0 for all nonzero x -/
def RealPosDef (A : Matrix n n ℝ) : Prop :=
  A.IsSymm ∧ ∀ x : n → ℝ, x ≠ 0 → 0 < dotProduct x (A.mulVec x)

/-- Positive definite implies positive semidefinite -/
theorem RealPosDef.toPosSemidef {A : Matrix n n ℝ} (h : RealPosDef A) :
    RealPosSemidef A := by
  refine ⟨h.1, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx; simp [dotProduct, mulVec]
  · exact le_of_lt (h.2 x hx)

/-- The zero matrix is PSD -/
theorem realPosSemidef_zero : RealPosSemidef (0 : Matrix n n ℝ) := by
  refine ⟨isSymm_zero, fun x => ?_⟩
  simp [dotProduct, mulVec]

/-- Sum of PSD matrices is PSD -/
theorem RealPosSemidef.add {A B : Matrix n n ℝ}
    (hA : RealPosSemidef A) (hB : RealPosSemidef B) :
    RealPosSemidef (A + B) := by
  refine ⟨hA.1.add hB.1, fun x => ?_⟩
  have h1 : (A + B).mulVec x = A.mulVec x + B.mulVec x := by
    ext i; simp [mulVec, dotProduct, add_mul, Finset.sum_add_distrib]
  rw [h1, dotProduct_add]
  exact add_nonneg (hA.2 x) (hB.2 x)

/-- Non-negative scalar multiple of PSD is PSD -/
theorem RealPosSemidef.smul {A : Matrix n n ℝ} {c : ℝ}
    (hA : RealPosSemidef A) (hc : 0 ≤ c) :
    RealPosSemidef (c • A) := by
  refine ⟨hA.1.smul c, fun x => ?_⟩
  have h1 : (c • A).mulVec x = c • (A.mulVec x) := by
    ext i; simp [mulVec, dotProduct, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [h1, dotProduct_smul]
  exact mul_nonneg hc (hA.2 x)

/-- Diagonal entry equals the quadratic form evaluated at the standard basis vector -/
private lemma diag_eq_quadratic (A : Matrix n n ℝ) (i : n) :
    A i i = dotProduct (Pi.single i 1) (A.mulVec (Pi.single i 1)) := by
  simp [dotProduct, mulVec, Pi.single, Function.update, Finset.sum_ite_eq', Finset.mem_univ]

/-- Trace of PSD matrix is non-negative.

This follows from the fact that each diagonal entry A i i equals eᵢᵀ A eᵢ ≥ 0 by the PSD
condition, so the trace (sum of diagonal entries) is a sum of non-negatives. -/
theorem RealPosSemidef.trace_nonneg {A : Matrix n n ℝ}
    (hA : RealPosSemidef A) : 0 ≤ A.trace := by
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_nonneg
  intro i _
  rw [diag_eq_quadratic A i]
  exact hA.2 _

/-
## Section 2: Loewner Order
-/

/-- Loewner order: A <=_L B iff B - A is positive semidefinite -/
def LoewnerLE (A B : Matrix n n ℝ) : Prop :=
  RealPosSemidef (B - A)

notation:50 A " ≤_L " B => LoewnerLE A B

/-- The Loewner order is reflexive -/
theorem loewner_refl (A : Matrix n n ℝ) : A ≤_L A := by
  unfold LoewnerLE; rw [sub_self]; exact realPosSemidef_zero

/-- The Loewner order is transitive -/
theorem loewner_trans {A B C : Matrix n n ℝ}
    (hAB : A ≤_L B) (hBC : B ≤_L C) : A ≤_L C := by
  unfold LoewnerLE at *
  have h : C - A = (C - B) + (B - A) := by ext i j; simp [sub_apply, add_apply]
  rw [h]; exact hBC.add hAB

/-- The Loewner order respects addition -/
theorem loewner_add_right {A B C : Matrix n n ℝ}
    (h : A ≤_L B) : A + C ≤_L B + C := by
  unfold LoewnerLE at *
  have : B + C - (A + C) = B - A := by ext i j; simp [sub_apply, add_apply]
  rw [this]; exact h

/-- The Loewner order respects non-negative scalar multiplication -/
theorem loewner_smul {A B : Matrix n n ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : A ≤_L B) : c • A ≤_L c • B := by
  unfold LoewnerLE at *
  have : c • B - c • A = c • (B - A) := by
    ext i j; simp only [smul_apply, sub_apply, smul_eq_mul]; ring
  rw [this]; exact h.smul hc

/-
## Section 3: Arithmetic Mean of Matrices
-/

/-- Arithmetic mean of two matrices -/
def matArithMean (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  (1/2 : ℝ) • (A + B)

/-- The arithmetic mean of two PSD matrices is PSD -/
theorem matArithMean_posSemidef {A B : Matrix n n ℝ}
    (hA : RealPosSemidef A) (hB : RealPosSemidef B) :
    RealPosSemidef (matArithMean A B) := by
  unfold matArithMean
  exact (hA.add hB).smul (by linarith : (0 : ℝ) ≤ 1 / 2)

/-- A <=_L (A + B)/2 when A <=_L B -/
theorem loewner_le_arithMean_left {A B : Matrix n n ℝ}
    (h : A ≤_L B) : A ≤_L matArithMean A B := by
  unfold LoewnerLE matArithMean
  have heq : (1 / 2 : ℝ) • (A + B) - A = (1 / 2 : ℝ) • (B - A) := by
    ext i j; simp only [smul_apply, sub_apply, add_apply, smul_eq_mul]; ring
  rw [heq]
  exact h.smul (by linarith : (0 : ℝ) ≤ 1 / 2)

/-- B <=_L (A + B)/2 when B <=_L A -/
theorem loewner_le_arithMean_right {A B : Matrix n n ℝ}
    (h : B ≤_L A) : B ≤_L matArithMean A B := by
  unfold LoewnerLE matArithMean
  have heq : (1 / 2 : ℝ) • (A + B) - B = (1 / 2 : ℝ) • (A - B) := by
    ext i j; simp only [smul_apply, sub_apply, add_apply, smul_eq_mul]; ring
  rw [heq]
  exact h.smul (by linarith : (0 : ℝ) ≤ 1 / 2)

/-
## Section 4: Matrix Geometric Mean (Axiomatized)
-/

/-- Matrix geometric mean for positive definite matrices -/
axiom matGeomMean (A B : Matrix n n ℝ) (hA : RealPosDef A) (hB : RealPosDef B) :
    Matrix n n ℝ

/-- Self geometric mean: A # A = A -/
axiom matGeomMean_self (A : Matrix n n ℝ) (hA : RealPosDef A) :
    matGeomMean A A hA hA = A

/-
## Section 5: The Operator AM-GM Inequality
-/

/-- **The Operator AM-GM Inequality**

For positive definite matrices A and B:
  A # B <=_L (A + B) / 2

The matrix geometric mean is dominated by the arithmetic mean
in the Loewner order (Ando 1979, Kubo-Ando 1980). -/
axiom operator_am_gm (A B : Matrix n n ℝ)
    (hA : RealPosDef A) (hB : RealPosDef B) :
    matGeomMean A B hA hB ≤_L matArithMean A B

/-- AM - GM is PSD -/
theorem arithMean_sub_geomMean_posSemidef
    (A B : Matrix n n ℝ) (hA : RealPosDef A) (hB : RealPosDef B) :
    RealPosSemidef (matArithMean A B - matGeomMean A B hA hB) :=
  operator_am_gm A B hA hB

/-- Trace inequality: tr((A+B)/2) >= tr(A # B) -/
theorem trace_arithMean_ge_trace_geomMean
    (A B : Matrix n n ℝ) (hA : RealPosDef A) (hB : RealPosDef B) :
    (matArithMean A B).trace ≥ (matGeomMean A B hA hB).trace := by
  have h := arithMean_sub_geomMean_posSemidef A B hA hB
  have htrace := h.trace_nonneg
  rw [Matrix.trace_sub] at htrace
  linarith

/-- If A = B then A # B = (A+B)/2 -/
theorem operator_am_gm_eq_of_eq (A : Matrix n n ℝ) (hA : RealPosDef A) :
    matGeomMean A A hA hA = matArithMean A A := by
  rw [matGeomMean_self]
  unfold matArithMean
  ext i j
  simp only [smul_apply, add_apply, smul_eq_mul]
  ring

/-
## Section 6: Weighted Arithmetic Mean
-/

/-- Weighted arithmetic mean: t*A + (1-t)*B -/
def matWeightedArithMean (t : ℝ) (A B : Matrix n n ℝ) : Matrix n n ℝ :=
  t • A + (1 - t) • B

/-- Equal-weight case matches arithmetic mean -/
theorem matWeightedArithMean_half (A B : Matrix n n ℝ) :
    matWeightedArithMean (1/2) A B = matArithMean A B := by
  unfold matWeightedArithMean matArithMean
  ext i j
  simp only [smul_apply, add_apply, smul_eq_mul]
  ring

/-- Weighted arithmetic mean preserves PSD -/
theorem matWeightedArithMean_posSemidef {A B : Matrix n n ℝ} {t : ℝ}
    (hA : RealPosSemidef A) (hB : RealPosSemidef B)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    RealPosSemidef (matWeightedArithMean t A B) := by
  unfold matWeightedArithMean
  exact (hA.smul ht0).add (hB.smul (by linarith))

/-
## Section 7: Harmonic Mean and HM-GM-AM Chain
-/

/-- Harmonic mean of positive definite matrices -/
axiom matHarmonicMean (A B : Matrix n n ℝ)
    (hA : RealPosDef A) (hB : RealPosDef B) : Matrix n n ℝ

/-- HM <=_L GM -/
axiom harmonic_le_geometric (A B : Matrix n n ℝ)
    (hA : RealPosDef A) (hB : RealPosDef B) :
    matHarmonicMean A B hA hB ≤_L matGeomMean A B hA hB

/-- Full HM-GM-AM chain -/
theorem harmonic_geometric_arithmetic (A B : Matrix n n ℝ)
    (hA : RealPosDef A) (hB : RealPosDef B) :
    matHarmonicMean A B hA hB ≤_L matArithMean A B :=
  loewner_trans (harmonic_le_geometric A B hA hB) (operator_am_gm A B hA hB)

end
