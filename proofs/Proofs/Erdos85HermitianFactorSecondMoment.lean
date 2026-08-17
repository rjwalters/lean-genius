import Proofs.Erdos85HermitianCharpolyPowerSums

/-! # Second-moment positivity for Hermitian characteristic factors -/

open Polynomial

namespace Erdos85

noncomputable section

/-- A complementary factor of a Hermitian characteristic polynomial has
only real roots, so its second root-power sum is nonnegative. -/
theorem complexRootPowerSum_two_re_nonnegative_of_charpoly_factor
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {f q : ℂ[X]} (hf : f ≠ 0) (hq : q ≠ 0)
    (hfactor : A.charpoly = f * q) :
    0 ≤ (complexRootPowerSum q 2).re := by
  rw [complexRootPowerSum]
  have hre_sum : ∀ s : Multiset ℂ,
      s.sum.re = (s.map Complex.re).sum := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons z s ih => simp [ih]
  rw [hre_sum, Multiset.map_map]
  apply Multiset.sum_nonneg
  intro _ hz'
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.mp hz'
  have hzchar : z ∈ A.charpoly.roots := by
    rw [hfactor, roots_mul (mul_ne_zero hf hq), Multiset.mem_add]
    exact Or.inr hz
  rw [hA.roots_charpoly_eq_eigenvalues] at hzchar
  obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
  simpa [Function.comp_apply, pow_two] using
    (mul_self_nonneg (hA.eigenvalues i))

/-- Consequently, the real part of a characteristic factor's second
root-power sum is bounded by the matrix square trace. -/
theorem complexRootPowerSum_factor_two_re_le_trace_sq
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {f q : ℂ[X]} (hf : f ≠ 0) (hq : q ≠ 0)
    (hfactor : A.charpoly = f * q) :
    (complexRootPowerSum f 2).re ≤ (Matrix.trace (A ^ 2)).re := by
  have hsum := complexRootPowerSum_mul hf hq 2
  have htrace := complexRootPowerSum_charpoly_eq_trace_pow A hA 2
  have hnonneg :=
    complexRootPowerSum_two_re_nonnegative_of_charpoly_factor
      A hA hf hq hfactor
  rw [← htrace, hfactor, hsum]
  rw [Complex.add_re]
  linarith

end

end Erdos85
