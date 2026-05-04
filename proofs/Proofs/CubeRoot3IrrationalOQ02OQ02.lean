/-
# Linear Independence of {1, ∛3, (∛3)²} over ℚ

**Open Question OQ-02** from `cube-root-3-irrational-oq-02`:
Is {1, ∛3, (∛3)²} linearly independent over ℚ?

## Mathematical Strategy

Let α = (3 : ℝ)^(1/3). The minimal polynomial of α over ℚ is X³ - 3
(proved in CubeRoot2IrrationalOQ03 via Eisenstein at p = 3). It has degree 3.

**Linear Independence proof (by contrapositive):**
Suppose Σ_{i < 3} cᵢ · αⁱ = 0 for c : Fin 3 → ℚ.
Define p = C(c₀) + C(c₁)X + C(c₂)X² ∈ ℚ[X].
Then aeval α p = 0, so by minpoly.dvd, the degree-3 polynomial minpoly ℚ α divides p.
If p ≠ 0, then natDegree(minpoly ℚ α) ≤ natDegree(p) ≤ 2 < 3, contradiction.
Hence p = 0, so coeff(p, i) = 0 for all i, giving cᵢ = 0.

## Relationship to Gallery

- **CubeRoot3IrrationalOQ02.lean**: proves ∛3 irrational via Eisenstein
- **CubeRoot3IrrationalOQ02OQ01.lean**: proves [ℚ(∛3):ℚ] = 3
- **This file**: proves {1, ∛3, (∛3)²} is a ℚ-linearly independent set

The linear independence follows from the degree-3 extension but is proved
here directly via the minpoly divisibility argument, without using the
full power basis machinery.

## Status: 0 sorries, 0 axioms
-/

import Proofs.CubeRoot2IrrationalOQ03

open Polynomial CubeRoot2IrrationalOQ03

set_option maxHeartbeats 800000

namespace CubeRoot3IrrationalOQ02OQ02

private noncomputable abbrev α : ℝ := (3 : ℝ) ^ ((1 : ℝ) / 3)

/-- The minimal polynomial of α = ∛3 over ℚ has natDegree 3.

This is the key ingredient: since deg(minpoly ℚ α) = 3, no nonzero polynomial
of degree ≤ 2 can be divisible by minpoly ℚ α. -/
private lemma α_minpoly_deg : (minpoly ℚ α).natDegree = 3 :=
  minpoly_nthRoot_natDegree 3 3 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- The powers {1, ∛3, (∛3)²} = {α^0, α^1, α^2} are linearly independent over ℚ.

**Proof**: Suppose Σ_{i < 3} cᵢ • αⁱ = 0 for c : Fin 3 → ℚ.
The polynomial p = C(c₀) + C(c₁)X + C(c₂)X² ∈ ℚ[X] satisfies aeval α p = 0.
By minpoly.dvd, minpoly ℚ α (degree 3) divides p. Since natDegree(p) ≤ 2 < 3,
if p ≠ 0 this contradicts natDegree_le_of_dvd. So p = 0 and all cᵢ = 0. -/
theorem cbrt3_powers_linearIndependent :
    LinearIndependent ℚ (fun i : Fin 3 => α ^ (i : ℕ)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  -- Build the polynomial whose evaluation at α encodes the linear combination
  set p : ℚ[X] := C (c 0) + C (c 1) * X + C (c 2) * X ^ 2 with hp_def
  -- Show aeval α p = Σ cᵢ • αⁱ = 0
  have haeval : Polynomial.aeval α p = 0 := by
    have heq : Polynomial.aeval α p = ∑ i : Fin 3, c i • α ^ (i : ℕ) := by
      simp only [hp_def, map_add, map_mul, map_pow, aeval_C, aeval_X,
                 Fin.sum_univ_three, Algebra.smul_def, pow_zero, pow_one]
      ring
    rw [heq, hc]
  -- minpoly ℚ α divides p (the key divisibility step)
  have hdvd : minpoly ℚ α ∣ p := minpoly.dvd ℚ α haeval
  -- Degree argument: p must be the zero polynomial
  have hp0 : p = 0 := by
    by_contra hne
    -- natDegree p ≤ 2 since p has terms at degrees 0, 1, 2 only
    have hdeg_p : p.natDegree ≤ 2 := by
      simp only [hp_def]
      apply (Polynomial.natDegree_add_le _ _).trans
      apply max_le
      · apply (Polynomial.natDegree_add_le _ _).trans
        apply max_le
        · simp [Polynomial.natDegree_C]
        · exact Polynomial.natDegree_mul_le.trans
            (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X])
      · exact Polynomial.natDegree_mul_le.trans
          (by simp [Polynomial.natDegree_C, Polynomial.natDegree_X_pow])
    -- natDegree(minpoly ℚ α) = 3 ≤ natDegree(p) ≤ 2: contradiction
    have hdeg_mp : (minpoly ℚ α).natDegree ≤ p.natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hne
    rw [α_minpoly_deg] at hdeg_mp; omega
  -- Extract cᵢ = 0 from p = 0 by reading off coefficients
  intro i
  have hci : c i = p.coeff (i : ℕ) := by
    fin_cases i <;> simp [hp_def]
  have h0 : p.coeff (i : ℕ) = 0 := by rw [hp0]; simp
  exact hci.trans h0

/-- Explicit form: 1, ∛3, and (∛3)² are ℚ-linearly independent. -/
theorem one_cbrt3_cbrt3_sq_linearIndependent :
    LinearIndependent ℚ (![1, α, α ^ 2] : Fin 3 → ℝ) := by
  convert cbrt3_powers_linearIndependent using 1
  ext i
  fin_cases i <;> simp [pow_succ]

end CubeRoot3IrrationalOQ02OQ02
