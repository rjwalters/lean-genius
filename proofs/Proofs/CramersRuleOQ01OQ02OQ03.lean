import Proofs.CramersRuleOQ01OQ02
import Mathlib.Tactic

/-
# Complete Schur Complement Inverse: All Four Block-Matrix Entries (OQ-01-OQ-02-OQ-03)

## Research Question
The parent file `CramersRuleOQ01OQ02.lean` defines the Schur-complement inverse
`schurInv A` of a 2x2 matrix over a division ring and verifies *two* of the four
entries of the product `A * schurInv A` (the (0,0) and (1,0) entries). Can we
complete the verification for **all four** entries — and, dually, for the four
entries of `schurInv A * A` — so that `schurInv A` is established as a genuine
two-sided inverse of `A`?

## Answer: YES

For `A = [[a,b],[c,d]]` over a division ring `D` with `q := qdet00 A = a - b d⁻¹ c`
and `d ≠ 0`, the matrix

  schurInv A = [[ q⁻¹,          -(q⁻¹ b d⁻¹) ],
                [ -(d⁻¹ c q⁻¹),  d⁻¹ + d⁻¹ c q⁻¹ b d⁻¹ ]]

is the unique two-sided inverse of `A`. This file:

1. Completes the right-multiplication identities: the (0,1) and (1,1) entries of
   `A * schurInv A` (the parent supplied (0,0) and (1,0)).
2. Assembles the full matrix equation `A * schurInv A = 1`.
3. Proves all four entries of the dual product `schurInv A * A` and assembles
   `schurInv A * A = 1`.
4. Packages the result as an `Invertible A` instance: `schurInv A` is THE inverse.

## Key Insight
Each off-diagonal cancellation is a *single* application of `q⁻¹ q = 1`
(resp. `d⁻¹ d = 1`); every remaining manipulation is a pure (non-commutative)
ring identity, isolated via `noncomm_ring`. The two scalar inverse cancellations
are exactly the two genuine hypotheses `qdet00 A ≠ 0` and `A 1 1 ≠ 0`.

## Extends
- `CramersRuleOQ01OQ02.lean`: quasideterminant theory + `schurInv`, `mul_schurInv_00`,
  `mul_schurInv_10`.
-/

noncomputable section

namespace CramersRuleOQ01OQ02OQ03

open Matrix CramersRuleOQ01OQ02

variable {D : Type*} [DivisionRing D]

-- ============================================================
-- PART I: Completing the Right-Inverse Entries
-- ============================================================

/-- The (0,1) entry of `A * schurInv A` is `0`.
    Proof: `-(a q⁻¹ b d⁻¹) + b d⁻¹ + (b d⁻¹ c) q⁻¹ b d⁻¹`
    `= (b d⁻¹ c - a)(q⁻¹ b d⁻¹) + b d⁻¹ = -q (q⁻¹ b d⁻¹) + b d⁻¹ = 0`. -/
theorem mul_schurInv_01 (A : Matrix (Fin 2) (Fin 2) D) (hq : qdet00 A ≠ 0) :
    A 0 0 * schurInv A 0 1 + A 0 1 * schurInv A 1 1 = 0 := by
  simp only [schurInv_01, schurInv_11]
  have key : A 0 0 * -((qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹)
      + A 0 1 * ((A 1 1)⁻¹ + (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹)
      = (A 0 1 * (A 1 1)⁻¹ * A 1 0 - A 0 0) * ((qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹)
        + A 0 1 * (A 1 1)⁻¹ := by
    noncomm_ring
  rw [key, show A 0 1 * (A 1 1)⁻¹ * A 1 0 - A 0 0 = -qdet00 A from by
        simp only [qdet00]; abel, neg_mul,
      show qdet00 A * ((qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹)
          = qdet00 A * (qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹ from by rw [← mul_assoc, ← mul_assoc],
      mul_inv_cancel₀ hq, one_mul]
  exact neg_add_cancel _

/-- The (1,1) entry of `A * schurInv A` is `1`.
    Proof: `-(c q⁻¹ b d⁻¹) + d d⁻¹ + (d d⁻¹) c q⁻¹ b d⁻¹ = 1` after `d d⁻¹ = 1`. -/
theorem mul_schurInv_11 (A : Matrix (Fin 2) (Fin 2) D) (hd : A 1 1 ≠ 0) :
    A 1 0 * schurInv A 0 1 + A 1 1 * schurInv A 1 1 = 1 := by
  simp only [schurInv_01, schurInv_11]
  have key : A 1 0 * -((qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹)
      + A 1 1 * ((A 1 1)⁻¹ + (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹)
      = A 1 1 * (A 1 1)⁻¹
        + (A 1 1 * (A 1 1)⁻¹ - 1) * (A 1 0 * (qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹) := by
    noncomm_ring
  rw [key, mul_inv_cancel₀ hd, sub_self, zero_mul, add_zero]

-- ============================================================
-- PART II: The Full Right-Inverse Matrix Identity
-- ============================================================

/-- **All four entries together:** `A * schurInv A = 1`.
    Right-inverse half of the two-sided Schur-complement inversion. -/
theorem mul_schurInv_eq_one (A : Matrix (Fin 2) (Fin 2) D)
    (hq : qdet00 A ≠ 0) (hd : A 1 1 ≠ 0) :
    A * schurInv A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]
      using mul_schurInv_00 A hq
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.one_apply_ne (by decide)]
    exact mul_schurInv_01 A hq
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.one_apply_ne (by decide)]
    exact mul_schurInv_10 A hd
  · simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]
      using mul_schurInv_11 A hd

-- ============================================================
-- PART III: The Dual Left-Inverse Entries
-- ============================================================

/-- The (0,0) entry of `schurInv A * A` is `1`.
    Proof: `q⁻¹ a - q⁻¹ b d⁻¹ c = q⁻¹ (a - b d⁻¹ c) = q⁻¹ q = 1`. -/
theorem schurInv_mul_00 (A : Matrix (Fin 2) (Fin 2) D) (hq : qdet00 A ≠ 0) :
    schurInv A 0 0 * A 0 0 + schurInv A 0 1 * A 1 0 = 1 := by
  simp only [schurInv_00, schurInv_01]
  have key : (qdet00 A)⁻¹ * A 0 0 + -((qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹) * A 1 0
      = (qdet00 A)⁻¹ * (A 0 0 - A 0 1 * (A 1 1)⁻¹ * A 1 0) := by
    noncomm_ring
  rw [key, show A 0 0 - A 0 1 * (A 1 1)⁻¹ * A 1 0 = qdet00 A from rfl, inv_mul_cancel₀ hq]

/-- The (0,1) entry of `schurInv A * A` is `0`.
    Proof: `q⁻¹ b - q⁻¹ b d⁻¹ d = q⁻¹ b (1 - d⁻¹ d) = 0`. -/
theorem schurInv_mul_01 (A : Matrix (Fin 2) (Fin 2) D) (hd : A 1 1 ≠ 0) :
    schurInv A 0 0 * A 0 1 + schurInv A 0 1 * A 1 1 = 0 := by
  simp only [schurInv_00, schurInv_01]
  have key : (qdet00 A)⁻¹ * A 0 1 + -((qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹) * A 1 1
      = (qdet00 A)⁻¹ * A 0 1 * (1 - (A 1 1)⁻¹ * A 1 1) := by
    noncomm_ring
  rw [key, inv_mul_cancel₀ hd, sub_self, mul_zero]

/-- The (1,0) entry of `schurInv A * A` is `0`.
    Proof: `d⁻¹ c q⁻¹ (b d⁻¹ c - a) + d⁻¹ c = d⁻¹ c q⁻¹ (-q) + d⁻¹ c = 0`. -/
theorem schurInv_mul_10 (A : Matrix (Fin 2) (Fin 2) D) (hq : qdet00 A ≠ 0) :
    schurInv A 1 0 * A 0 0 + schurInv A 1 1 * A 1 0 = 0 := by
  simp only [schurInv_10, schurInv_11]
  have key : -((A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹) * A 0 0
      + ((A 1 1)⁻¹ + (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹) * A 1 0
      = (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ * (A 0 1 * (A 1 1)⁻¹ * A 1 0 - A 0 0)
        + (A 1 1)⁻¹ * A 1 0 := by
    noncomm_ring
  rw [key, show A 0 1 * (A 1 1)⁻¹ * A 1 0 - A 0 0 = -qdet00 A from by
        simp only [qdet00]; abel, mul_neg,
      mul_assoc ((A 1 1)⁻¹ * A 1 0) ((qdet00 A)⁻¹) (qdet00 A),
      inv_mul_cancel₀ hq, mul_one, neg_add_cancel]

/-- The (1,1) entry of `schurInv A * A` is `1`.
    Proof: `d⁻¹ d + d⁻¹ c q⁻¹ b (d⁻¹ d - 1) = 1 + 0 = 1` after `d⁻¹ d = 1`. -/
theorem schurInv_mul_11 (A : Matrix (Fin 2) (Fin 2) D) (hd : A 1 1 ≠ 0) :
    schurInv A 1 0 * A 0 1 + schurInv A 1 1 * A 1 1 = 1 := by
  simp only [schurInv_10, schurInv_11]
  have key : -((A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹) * A 0 1
      + ((A 1 1)⁻¹ + (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ * A 0 1 * (A 1 1)⁻¹) * A 1 1
      = (A 1 1)⁻¹ * A 1 1
        + (A 1 1)⁻¹ * A 1 0 * (qdet00 A)⁻¹ * A 0 1 * ((A 1 1)⁻¹ * A 1 1 - 1) := by
    noncomm_ring
  rw [key, inv_mul_cancel₀ hd, sub_self, mul_zero, add_zero]

-- ============================================================
-- PART IV: The Full Left-Inverse Identity and Invertibility
-- ============================================================

/-- **All four entries together:** `schurInv A * A = 1`.
    Left-inverse half of the two-sided Schur-complement inversion. -/
theorem schurInv_mul_eq_one (A : Matrix (Fin 2) (Fin 2) D)
    (hq : qdet00 A ≠ 0) (hd : A 1 1 ≠ 0) :
    schurInv A * A = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]
      using schurInv_mul_00 A hq
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.one_apply_ne (by decide)]
    exact schurInv_mul_01 A hd
  · simp only [Matrix.mul_apply, Fin.sum_univ_two]
    rw [Matrix.one_apply_ne (by decide)]
    exact schurInv_mul_10 A hq
  · simpa only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq]
      using schurInv_mul_11 A hd

/-- The complete two-sided statement: under the Schur conditions
    `qdet00 A ≠ 0` and `A 1 1 ≠ 0`, `schurInv A` is a two-sided inverse of `A`. -/
theorem schurInv_two_sided (A : Matrix (Fin 2) (Fin 2) D)
    (hq : qdet00 A ≠ 0) (hd : A 1 1 ≠ 0) :
    A * schurInv A = 1 ∧ schurInv A * A = 1 :=
  ⟨mul_schurInv_eq_one A hq hd, schurInv_mul_eq_one A hq hd⟩

/-- Under the Schur conditions, `A` is invertible with `⅟A = schurInv A`.
    This certifies that `schurInv A` is *the* (unique) inverse, not merely a
    one-sided pseudo-inverse. -/
def invertibleOfSchur (A : Matrix (Fin 2) (Fin 2) D)
    (hq : qdet00 A ≠ 0) (hd : A 1 1 ≠ 0) : Invertible A where
  invOf := schurInv A
  invOf_mul_self := schurInv_mul_eq_one A hq hd
  mul_invOf_self := mul_schurInv_eq_one A hq hd

/-- Consequently `schurInv A` agrees with Mathlib's general matrix inverse
    `A⁻¹` over a (commutative) field, whenever the Schur conditions hold. -/
theorem schurInv_eq_inv {F : Type*} [Field F] (A : Matrix (Fin 2) (Fin 2) F)
    (hq : qdet00 A ≠ 0) (hd : A 1 1 ≠ 0) :
    schurInv A = A⁻¹ :=
  (Matrix.inv_eq_left_inv (schurInv_mul_eq_one A hq hd)).symm

end CramersRuleOQ01OQ02OQ03

end
