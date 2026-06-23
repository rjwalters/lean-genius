/-
  Aristotle targets for Erdős Problem #1151 OQ-04 (Lebesgue Function / Chebyshev Divergence)
  Routine supporting lemmas for automated proof search.
  See Erdos1151OQ04.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main hard results (chebyshev_lebesgue_growth, divergence_from_lebesgue_growth)
  - NOT lagrange_basis_chebyshev_formula (Chebyshev product formula absent from Mathlib v4.26.0)
  - Routine lemmas about Chebyshev nodes derivable from Mathlib trig API:
    * cos_odd_half_pi: cos((2k+1)π/2) = 0 via cos_add + trig identities
    * chebyshevNode_is_root: T_n(cos((2k+1)π/(2n))) = 0 via T_real_cos
    * chebyshevNode_injective: cos injective on (0,π) ⊂ [0,π]
  - No axioms, no definition sorries, no open conjectures

  Excluded:
  - chebyshev_lebesgue_growth: deep trig sum lower bound
  - divergence_from_lebesgue_growth: lacunary series construction
  - chebyshev_lebesgue_eq: depends on lagrange_basis_chebyshev_formula (unresolved)
-/
import Mathlib
import Proofs.Erdos1151OQ04

open Real Polynomial.Chebyshev

namespace Erdos1151OQ04Aristotle

open Erdos1151OQ04

/-
## Section 1: Arithmetic Helpers

Simple algebraic facts about Chebyshev angles φₖ = (2k+1)π/(2n).
All proofs are complete (no sorry).
-/

/-- n * ((2k+1)π/(2n)) = (2k+1)π/2. -/
theorem n_mul_chebyshevAngle (n : ℕ) (hn : 0 < n) (k : Fin n) :
    (n : ℝ) * ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) =
    (2 * k.val + 1 : ℝ) * Real.pi / 2 := by
  have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp
  ring

/-- The Chebyshev node angles are positive. -/
theorem chebyshevAngle_pos (n : ℕ) (k : Fin n) :
    0 < (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) :=
  div_pos (mul_pos (by positivity) Real.pi_pos) (by positivity)

/-- The Chebyshev node angles are less than π, using k.val < n. -/
theorem chebyshevAngle_lt_pi (n : ℕ) (hn : 0 < n) (k : Fin n) :
    (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) < Real.pi := by
  rw [div_lt_iff (by positivity : (0 : ℝ) < 2 * n)]
  have : k.val + 1 ≤ n := k.isLt
  have hcast : (2 * k.val + 1 : ℝ) < 2 * n := by exact_mod_cast by omega
  linarith [Real.pi_pos]

/-- The Chebyshev node angles lie in the open interval (0, π). -/
theorem chebyshevAngle_mem_Ioo (n : ℕ) (hn : 0 < n) (k : Fin n) :
    (2 * k.val + 1 : ℝ) * Real.pi / (2 * n) ∈ Set.Ioo (0 : ℝ) Real.pi :=
  ⟨chebyshevAngle_pos n k, chebyshevAngle_lt_pi n hn k⟩

/-- Distinct k give distinct Chebyshev angles. -/
theorem chebyshevAngle_ne_of_ne (n : ℕ) (hn : 0 < n) (i j : Fin n) (hij : i ≠ j) :
    (2 * i.val + 1 : ℝ) * Real.pi / (2 * n) ≠
    (2 * j.val + 1 : ℝ) * Real.pi / (2 * n) := by
  intro h
  apply hij
  apply Fin.ext
  have hpos : (0 : ℝ) < 2 * n := by positivity
  have hpi : Real.pi > 0 := Real.pi_pos
  have h2 : (2 * (i.val : ℝ) + 1) * Real.pi = (2 * j.val + 1) * Real.pi := by
    field_simp [hpos.ne'] at h; linarith
  have h3 : (2 * (i.val : ℝ) + 1) = 2 * j.val + 1 :=
    mul_right_cancel₀ hpi.ne' h2
  exact_mod_cast by linarith

/-
## Section 2: Aristotle Targets

Three sorries that Aristotle should be able to prove using Mathlib's trig API.
-/

/-- cos((2k+1)π/2) = 0 for any natural k.

    Strategy:
      (2k+1)π/2 = k·π + π/2
      cos(k·π + π/2) = cos(k·π)·cos(π/2) - sin(k·π)·sin(π/2)
                     = cos(k·π)·0 - 0·1 = 0
    Key lemmas: Real.cos_add, Real.cos_pi_div_two (= 0),
                Real.sin_nat_mul_pi (= 0), Real.sin_pi_div_two (= 1). -/
theorem cos_odd_half_pi (k : ℕ) :
    Real.cos ((2 * k + 1 : ℝ) * Real.pi / 2) = 0 := by
  have h : (2 * (k : ℝ) + 1) * Real.pi / 2 = k * Real.pi + Real.pi / 2 := by ring
  rw [h, Real.cos_add, Real.cos_pi_div_two, mul_zero, Real.sin_nat_mul_pi, zero_mul, sub_zero]

/-- The k-th Chebyshev node is a root of T_n (n-th Chebyshev polynomial).

    Strategy:
    1. chebyshevNode n k = cos(φₖ) where φₖ = (2k+1)π/(2n).
    2. T_real_cos: T_n(cos θ) = cos(n·θ).
    3. n·φₖ = (2k+1)π/2                     [n_mul_chebyshevAngle].
    4. cos((2k+1)π/2) = 0                    [cos_odd_half_pi]. -/
theorem chebyshevNode_is_root (n : ℕ) (hn : 0 < n) (k : Fin n) :
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).eval (chebyshevNode n k) = 0 := by
  simp only [chebyshevNode, chebyshev_T_at_cos]
  have hmul : (n : ℤ) * ((2 * ↑k.val + 1 : ℝ) * Real.pi / (2 * ↑n)) =
      (2 * k.val + 1 : ℝ) * Real.pi / 2 := by
    push_cast
    have : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
    ring
  rw [hmul]
  exact cos_odd_half_pi k.val

/-- The Chebyshev nodes are pairwise distinct.

    Strategy:
    1. The k-th node is cos((2k+1)π/(2n)).
    2. These angles are in (0, π)             [chebyshevAngle_mem_Ioo].
    3. cos is strictly monotone on [0, π]     [Real.strictAntiOn_cos].
    4. Distinct k give distinct angles        [chebyshevAngle_ne_of_ne].
    5. Therefore distinct k give distinct cosines. -/
theorem chebyshevNode_injective (n : ℕ) (hn : 0 < n) :
    Function.Injective (chebyshevNode n) := by
  intro i j heq
  simp only [chebyshevNode] at heq
  have hi := chebyshevAngle_mem_Ioo n hn i
  have hj := chebyshevAngle_mem_Ioo n hn j
  have hangle_eq := Real.strictAntiOn_cos.injOn
    (Set.Ioo_subset_Icc_self hi) (Set.Ioo_subset_Icc_self hj) heq
  apply Fin.ext
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have heq2 : (2 * (i.val : ℝ) + 1) = 2 * j.val + 1 := by
    have := hangle_eq
    field_simp [hn', hpi] at this
    linarith
  exact_mod_cast (show (i.val : ℝ) = j.val by linarith)

end Erdos1151OQ04Aristotle
