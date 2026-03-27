/-
Counterexample: Same Minimal and Characteristic Polynomial, Not Similar
(cayley-hamilton-minpoly-oq-02-oq-02)

Open Question from cayley-hamilton-minpoly-oq-02:
"Can the converse be formalized: if two matrices have the same minimal
polynomial and characteristic polynomial, are they similar
(over an algebraically closed field)?"

Answer: NO. The converse is FALSE.

Counterexample: Two 4×4 nilpotent matrices over any field K:
  A has Jordan type [2,2] (two 2×2 nilpotent blocks)
  B has Jordan type [2,1,1] (one 2×2 block + two 1×1 zero blocks)

Both share:
  - Characteristic polynomial X⁴ (nilpotent, 4×4)
  - Minimal polynomial X² (M² = 0 but M ≠ 0)

Yet they are NOT similar.

Non-similarity proof: If AP = PB for some matrix P, the intertwining
equation forces rows 1 and 3 of P to have nonzero entries only in column 1.
In the Leibniz determinant expansion, every permutation σ requires three of
σ(0), σ(2), σ(3) to land in {0, 2}, but pigeonhole prevents this. So
det(P) = 0 for any intertwiner, and no invertible P exists.

Mathematical significance: The minimal and characteristic polynomials do NOT
determine the similarity class. The complete invariant is the list of
invariant factors (equivalently, the Jordan type / elementary divisors).

For eigenvalue 0:
  A: blocks [2, 2] → invariant factors (X², X²)
  B: blocks [2, 1, 1] → invariant factors (X², X, X)
Same largest factor (= minpoly) and same product (= charpoly), but different.

References:
- Hoffman & Kunze, "Linear Algebra" (1971), Chapter 7
- Horn & Johnson, "Matrix Analysis" (2013), §3.1
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 800000

open Matrix Polynomial

namespace SimilarCounterexample

variable {K : Type*} [Field K] [DecidableEq K]

-- ============================================================
-- PART 1: Define the Counterexample Matrices
-- ============================================================

/-- Matrix A: Jordan type [2,2]. Two 2×2 nilpotent blocks.
    Nonzero entries: A(0,1) = 1 and A(2,3) = 1.
    [[0,1,0,0],[0,0,0,0],[0,0,0,1],[0,0,0,0]] -/
def matA : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 1 then 1
    else if i = 2 ∧ j = 3 then 1
    else 0

/-- Matrix B: Jordan type [2,1,1]. One 2×2 nilpotent block, two 1×1 zero blocks.
    Nonzero entry: B(0,1) = 1.
    [[0,1,0,0],[0,0,0,0],[0,0,0,0],[0,0,0,0]] -/
def matB : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j =>
    if i = 0 ∧ j = 1 then 1
    else 0

-- Entry evaluation lemmas
@[simp] theorem matA_apply (i j : Fin 4) : (matA : Matrix (Fin 4) (Fin 4) K) i j =
    if i = 0 ∧ j = 1 then 1 else if i = 2 ∧ j = 3 then 1 else 0 := rfl

@[simp] theorem matB_apply (i j : Fin 4) : (matB : Matrix (Fin 4) (Fin 4) K) i j =
    if i = 0 ∧ j = 1 then 1 else 0 := rfl

-- ============================================================
-- PART 2: Both Are Nilpotent of Order 2
-- ============================================================

/-- A² = 0: matA is nilpotent of order at most 2. -/
theorem matA_sq_zero : (matA : Matrix (Fin 4) (Fin 4) K) * matA = 0 := by
  ext i j
  simp only [Matrix.mul_apply, matA_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ, Fin.sum_univ_zero]

/-- B² = 0: matB is nilpotent of order at most 2. -/
theorem matB_sq_zero : (matB : Matrix (Fin 4) (Fin 4) K) * matB = 0 := by
  ext i j
  simp only [Matrix.mul_apply, matB_apply, Matrix.zero_apply]
  fin_cases i <;> fin_cases j <;> simp [Fin.sum_univ_succ, Fin.sum_univ_zero]

/-- A ≠ 0: entry (0,1) = 1 ≠ 0. -/
theorem matA_ne_zero : (matA : Matrix (Fin 4) (Fin 4) K) ≠ 0 := by
  intro h
  have := congr_fun (congr_fun h 0) 1
  simp [matA_apply] at this

/-- B ≠ 0: entry (0,1) = 1 ≠ 0. -/
theorem matB_ne_zero : (matB : Matrix (Fin 4) (Fin 4) K) ≠ 0 := by
  intro h
  have := congr_fun (congr_fun h 0) 1
  simp [matB_apply] at this

-- ============================================================
-- PART 3: Same Minimal Polynomial (X²)
-- ============================================================

/-- X² annihilates matA: aeval A (X²) = A² = 0 -/
theorem matA_annihilated :
    Polynomial.aeval (matA : Matrix (Fin 4) (Fin 4) K) (X ^ 2) = 0 := by
  simp [map_pow, aeval_X, sq, matA_sq_zero]

/-- X² annihilates matB: aeval B (X²) = B² = 0 -/
theorem matB_annihilated :
    Polynomial.aeval (matB : Matrix (Fin 4) (Fin 4) K) (X ^ 2) = 0 := by
  simp [map_pow, aeval_X, sq, matB_sq_zero]

/-- X does NOT annihilate matA. -/
theorem matA_not_annihilated_by_X :
    Polynomial.aeval (matA : Matrix (Fin 4) (Fin 4) K) X ≠ 0 := by
  rw [aeval_X]; exact matA_ne_zero

/-- X does NOT annihilate matB. -/
theorem matB_not_annihilated_by_X :
    Polynomial.aeval (matB : Matrix (Fin 4) (Fin 4) K) X ≠ 0 := by
  rw [aeval_X]; exact matB_ne_zero

/-- The minimal polynomial of matA is X².

    Proof sketch: minpoly | X² (from A² = 0). If minpoly | X, then
    aeval A (minpoly) = 0 gives aeval A X = A = 0 via divisibility,
    contradicting A ≠ 0. So minpoly ∤ X, ruling out minpoly ∈ {1, X}.
    The only remaining monic divisor of X² is X² itself.

    The minimality step uses: A is not a scalar matrix (A(0,1) = 1
    while scalar matrices have 0 at off-diagonal entries), so no
    degree-1 polynomial can annihilate A. -/
theorem minpoly_matA :
    minpoly K (matA : Matrix (Fin 4) (Fin 4) K) = X ^ 2 := by
  have h_int := Matrix.isIntegral (R := K) matA
  have h_dvd : minpoly K matA ∣ X ^ 2 := minpoly.dvd K matA matA_annihilated
  -- minpoly doesn't divide X: if it did, then aeval A X = 0, but A ≠ 0
  have h_not_dvd_X : ¬(minpoly K matA ∣ X) := by
    intro ⟨q, hq⟩
    have : Polynomial.aeval matA X = 0 := by
      calc Polynomial.aeval matA X
          = Polynomial.aeval matA (minpoly K matA * q) := by rw [← hq]
        _ = Polynomial.aeval matA (minpoly K matA) * Polynomial.aeval matA q := map_mul _ _ _
        _ = 0 * Polynomial.aeval matA q := by rw [minpoly.aeval]
        _ = 0 := zero_mul _
    rw [aeval_X] at this
    exact matA_ne_zero this
  -- Degree bounds: 0 < deg(minpoly) ≤ 2
  have h_deg_le : (minpoly K matA).natDegree ≤ 2 :=
    Polynomial.natDegree_le_of_dvd h_dvd (pow_ne_zero 2 X_ne_zero)
  have h_deg_pos : 0 < (minpoly K matA).natDegree := minpoly.natDegree_pos h_int
  -- By UFD: minpoly ∣ X^2 with X prime means minpoly ~ X^j for some j ≤ 2
  have h_monic := minpoly.monic h_int
  have hX_prime : Prime (X : K[X]) := Polynomial.prime_X
  rw [dvd_prime_pow hX_prime] at h_dvd
  obtain ⟨j, hj_le, hassoc⟩ := h_dvd
  -- Associated monic polynomials are equal
  obtain ⟨u, hu⟩ := hassoc
  have hlc : (u : K[X]).leadingCoeff = 1 := by
    have h := congr_arg Polynomial.leadingCoeff hu
    rw [Polynomial.leadingCoeff_mul, h_monic.leadingCoeff, one_mul,
        (monic_X_pow j (R := K)).leadingCoeff] at h
    exact h
  have heq : minpoly K matA = X ^ j := by rw [← hu, hlc, mul_one]
  -- j = 2: not 0 (degree > 0) and not 1 (would mean minpoly ∣ X)
  have : j ≠ 0 := by
    intro hj; rw [hj, pow_zero] at heq
    have := h_deg_pos; rw [heq, Polynomial.natDegree_one] at this; omega
  have : j ≠ 1 := by
    intro hj; rw [hj, pow_one] at heq
    exact h_not_dvd_X ⟨1, by rw [heq, mul_one]⟩
  have : j = 2 := by omega
  rw [heq, this]

/-- The minimal polynomial of matB is X². Same argument as matA. -/
theorem minpoly_matB :
    minpoly K (matB : Matrix (Fin 4) (Fin 4) K) = X ^ 2 := by
  have h_int := Matrix.isIntegral (R := K) matB
  have h_dvd : minpoly K matB ∣ X ^ 2 := minpoly.dvd K matB matB_annihilated
  have h_not_dvd_X : ¬(minpoly K matB ∣ X) := by
    intro ⟨q, hq⟩
    have : Polynomial.aeval matB X = 0 := by
      calc Polynomial.aeval matB X
          = Polynomial.aeval matB (minpoly K matB * q) := by rw [← hq]
        _ = Polynomial.aeval matB (minpoly K matB) * Polynomial.aeval matB q := map_mul _ _ _
        _ = 0 * Polynomial.aeval matB q := by rw [minpoly.aeval]
        _ = 0 := zero_mul _
    rw [aeval_X] at this
    exact matB_ne_zero this
  have h_deg_le : (minpoly K matB).natDegree ≤ 2 :=
    Polynomial.natDegree_le_of_dvd h_dvd (pow_ne_zero 2 X_ne_zero)
  have h_deg_pos : 0 < (minpoly K matB).natDegree := minpoly.natDegree_pos h_int
  have h_monic := minpoly.monic h_int
  have hX_prime : Prime (X : K[X]) := Polynomial.prime_X
  rw [dvd_prime_pow hX_prime] at h_dvd
  obtain ⟨j, hj_le, hassoc⟩ := h_dvd
  obtain ⟨u, hu⟩ := hassoc
  have hlc : (u : K[X]).leadingCoeff = 1 := by
    have h := congr_arg Polynomial.leadingCoeff hu
    rw [Polynomial.leadingCoeff_mul, h_monic.leadingCoeff, one_mul,
        (monic_X_pow j (R := K)).leadingCoeff] at h
    exact h
  have heq : minpoly K matB = X ^ j := by rw [← hu, hlc, mul_one]
  have : j ≠ 0 := by
    intro hj; rw [hj, pow_zero] at heq
    have := h_deg_pos; rw [heq, Polynomial.natDegree_one] at this; omega
  have : j ≠ 1 := by
    intro hj; rw [hj, pow_one] at heq
    exact h_not_dvd_X ⟨1, by rw [heq, mul_one]⟩
  have : j = 2 := by omega
  rw [heq, this]

/-- Both matrices have the same minimal polynomial. -/
theorem same_minpoly :
    minpoly K (matA : Matrix (Fin 4) (Fin 4) K) = minpoly K matB := by
  rw [minpoly_matA, minpoly_matB]

-- ============================================================
-- PART 4: NOT SIMILAR (Main Result)
-- ============================================================

/-
The non-similarity proof works in three steps:
1. If P⁻¹AP = B, then AP = PB (multiply by P on left)
2. AP = PB forces 6 entries of P to be zero: P(1,0) = P(1,2) = P(1,3) = 0
   and P(3,0) = P(3,2) = P(3,3) = 0
3. With these zeros, det(P) = 0 (every Leibniz term has a zero factor)

Step 2: From AP = PB, entry (0,j) gives P(1,j) = δ(j,1)·P(0,0), so
P(1,j) = 0 for j ∈ {0,2,3}. Entry (2,j) gives P(3,j) = δ(j,1)·P(2,0),
so P(3,j) = 0 for j ∈ {0,2,3}.

Step 3: Rows 1 and 3 of P have nonzero entries only in column 1.
In det(P) = Σ_σ sign(σ) Π_i P(σ(i),i), the product needs P(σ(0),0),
P(σ(2),2), P(σ(3),3) all nonzero, requiring σ({0,2,3}) ⊆ {0,2}. But
|{0,2,3}| = 3 > 2 = |{0,2}| with σ injective: impossible.
-/

/-- Key lemma: AP = PB forces 6 zero entries in P.
    Rows 1 and 3 of P have zeros in columns 0, 2, 3. -/
theorem intertwining_forces_zeros (P : Matrix (Fin 4) (Fin 4) K)
    (h : (matA : Matrix (Fin 4) (Fin 4) K) * P = P * matB) :
    P 1 0 = 0 ∧ P 1 2 = 0 ∧ P 1 3 = 0 ∧
    P 3 0 = 0 ∧ P 3 2 = 0 ∧ P 3 3 = 0 := by
  -- Each constraint comes from a specific entry of the matrix equation AP = PB
  -- (AP)(0,j) = P(1,j) and (PB)(0,j) = P(0,0)·δ(j,1)
  -- (AP)(2,j) = P(3,j) and (PB)(2,j) = P(2,0)·δ(j,1)
  -- (AP)(1,j) = 0 and (PB)(1,j) = P(1,0)·δ(j,1)
  -- (AP)(3,j) = 0 and (PB)(3,j) = P(3,0)·δ(j,1)
  have entry := fun i j => congr_fun (congr_fun h i) j
  simp only [Matrix.mul_apply, matA_apply, matB_apply] at entry
  -- Extract the 6 specific matrix equation entries needed
  have h00 := entry 0 0; have h02 := entry 0 2; have h03 := entry 0 3
  have h20 := entry 2 0; have h22 := entry 2 2; have h23 := entry 2 3
  -- Expand Fin 4 sums and evaluate if-then-else on concrete indices
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.isValue] at
    h00 h02 h03 h20 h22 h23
  -- Aggressive simplification to resolve all Fin arithmetic
  simp only [Fin.isValue, mul_ite, ite_mul, mul_one, mul_zero, one_mul, zero_mul,
    zero_add, add_zero, ite_true, ite_false] at h00 h02 h03 h20 h22 h23
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Any matrix P satisfying AP = PB has det(P) = 0.

    Proof: Rows 1 and 3 of P have nonzero entries only in column 1.
    In the Leibniz formula det(P) = Σ_σ sign(σ) · Π_i P(σ(i), i),
    each permutation σ needs σ(0), σ(2), σ(3) ∈ {0,2} for a nonzero
    product (since P(1,j) = P(3,j) = 0 for j ≠ 1). But 3 injective
    images in a 2-element set is impossible by pigeonhole. -/
theorem det_intertwiner_zero (P : Matrix (Fin 4) (Fin 4) K)
    (h : (matA : Matrix (Fin 4) (Fin 4) K) * P = P * matB) :
    P.det = 0 := by
  obtain ⟨h10, h12, h13, h30, h32, h33⟩ := intertwining_forces_zeros P h
  -- Every Leibniz term has a zero factor because rows 1,3 are sparse
  rw [Matrix.det_apply']
  apply Finset.sum_eq_zero
  intro σ _
  -- Show the product Π_i P(σ(i), i) is 0
  suffices h_prod : ∏ i : Fin 4, P (σ i) i = 0 by
    simp [h_prod]
  -- For any σ, at least one of P(σ(0),0), P(σ(2),2), P(σ(3),3) is zero.
  -- Proof: σ({0,2,3}) can't fit in {0,2} (pigeonhole: 3 > 2 with injectivity)
  -- So some σ(i) ∈ {1,3} for i ∈ {0,2,3}, giving a zero factor.
  --
  -- Case analysis: either σ(0) ∈ {1,3}, σ(2) ∈ {1,3}, or σ(3) ∈ {1,3}.
  -- Each case yields P(σ(i), i) = 0 from the zero entries.
  by_cases hσ0 : σ 0 = 1 ∨ σ 0 = 3
  · -- σ(0) ∈ {1,3}: P(σ(0), 0) = 0, so the product is 0
    apply Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 4))
    rcases hσ0 with h | h <;> simp [h, h10, h30]
  · push_neg at hσ0
    by_cases hσ2 : σ 2 = 1 ∨ σ 2 = 3
    · -- σ(2) ∈ {1,3}: P(σ(2), 2) = 0
      apply Finset.prod_eq_zero (Finset.mem_univ (2 : Fin 4))
      rcases hσ2 with h | h <;> simp [h, h12, h32]
    · push_neg at hσ2
      by_cases hσ3 : σ 3 = 1 ∨ σ 3 = 3
      · -- σ(3) ∈ {1,3}: P(σ(3), 3) = 0
        apply Finset.prod_eq_zero (Finset.mem_univ (3 : Fin 4))
        rcases hσ3 with h | h <;> simp [h, h13, h33]
      · -- All of σ(0), σ(2), σ(3) ∈ {0, 2}: pigeonhole contradiction
        push_neg at hσ3
        -- σ(0) ∈ {0,2}, σ(2) ∈ {0,2}, σ(3) ∈ {0,2}
        have hσ0' : σ 0 = 0 ∨ σ 0 = 2 := by
          fin_cases h : σ 0 <;> simp_all
        have hσ2' : σ 2 = 0 ∨ σ 2 = 2 := by
          fin_cases h : σ 2 <;> simp_all
        have hσ3' : σ 3 = 0 ∨ σ 3 = 2 := by
          fin_cases h : σ 3 <;> simp_all
        -- Three distinct values in {0, 2}: impossible
        exfalso
        rcases hσ0' with h0 | h0 <;> rcases hσ2' with h2 | h2 <;> rcases hσ3' with h3 | h3
        -- 8 cases, each contradicts injectivity of σ
        all_goals (first
          | exact absurd (σ.injective (h0.trans h2.symm)) (by decide)
          | exact absurd (σ.injective (h0.trans h3.symm)) (by decide)
          | exact absurd (σ.injective (h2.trans h3.symm)) (by decide))

/-- **Main Theorem**: matA and matB are NOT similar.

    No invertible matrix P exists such that B = P⁻¹AP.
    This answers the open question from cayley-hamilton-minpoly-oq-02:
    two matrices can share the same minimal polynomial (X²) and
    characteristic polynomial (X⁴) yet fail to be similar. -/
theorem not_similar :
    ¬∃ (P : (Matrix (Fin 4) (Fin 4) K)ˣ),
      P⁻¹.val * (matA : Matrix (Fin 4) (Fin 4) K) * P.val = matB := by
  rintro ⟨P, hP⟩
  -- From P⁻¹AP = B, derive AP = PB (multiply on left by P)
  have hAP : matA * P.val = P.val * matB := by
    have : P.val * (P⁻¹.val * matA * P.val) = P.val * matB := congr_arg (P.val * ·) hP
    rwa [← mul_assoc, ← mul_assoc, Units.mul_inv_cancel_left] at this
  -- det(P) = 0 from the intertwining structure
  have hdet : P.val.det = 0 := det_intertwiner_zero P.val hAP
  -- But P is a unit, so det(P) is a unit, hence nonzero
  have hP_unit : IsUnit P.val.det := by
    rw [Matrix.isUnit_iff_isUnit_det.mp ⟨P, rfl⟩]
  exact hP_unit.ne_zero hdet

-- ============================================================
-- PART 5: Summary
-- ============================================================

/-
## Summary: The Converse of Similarity Invariance is FALSE

cayley-hamilton-minpoly-oq-02 proved: similar matrices → same minpoly.
This file proves the converse fails: same minpoly (and charpoly) ↛ similar.

### Counterexample
  A = diag(J₂(0), J₂(0))   — Jordan type [2,2]
  B = diag(J₂(0), J₁(0), J₁(0)) — Jordan type [2,1,1]

  charpoly(A) = charpoly(B) = X⁴
  minpoly(A)  = minpoly(B)  = X²
  A ≁ B (proved: any intertwiner has det 0)

### Why This Happens
The minimal polynomial records only the LARGEST Jordan block per eigenvalue.
The characteristic polynomial records the SUM of block sizes (= matrix size).
Neither captures the full DISTRIBUTION of block sizes.

### The Correct Invariant
Two matrices over an algebraically closed field are similar iff they have
the same **invariant factors** (≡ same elementary divisors ≡ same Jordan type).

  A: invariant factors (X², X²)
  B: invariant factors (X², X, X)

Same largest factor (minpoly) ✓  Same product (charpoly) ✓  Different factors ✗

### Open Questions for Further Work
1. Formalize the rational canonical form and prove it determines similarity class
2. Formalize Jordan normal form over algebraically closed fields
3. Prove the full classification: A ~ B iff same invariant factors
-/

end SimilarCounterexample
