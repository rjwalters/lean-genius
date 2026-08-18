import Proofs.Erdos85HermitianCharpolyPowerSums

/-! # Second-moment bound for a nonprincipal Hermitian factor -/

open Polynomial

namespace Erdos85

noncomputable section

private theorem complementary_secondMoment_nonnegative
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {g r : ℂ[X]} (hg : g ≠ 0) (hr : r ≠ 0)
    (hfactor : A.charpoly = g * r) :
    0 ≤ (complexRootPowerSum r 2).re := by
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
    rw [hfactor, roots_mul (mul_ne_zero hg hr), Multiset.mem_add]
    exact Or.inr hz
  rw [hA.roots_charpoly_eq_eigenvalues] at hzchar
  obtain ⟨i, _hi, rfl⟩ := Multiset.mem_map.mp hzchar
  simpa [Function.comp_apply, pow_two] using
    (mul_self_nonneg (hA.eigenvalues i))

/-- If a Hermitian characteristic polynomial factors as
`f * (X - 7) * r`, then the roots of `f` consume at most the total second
moment minus the principal contribution `7² = 49`. -/
theorem complexRootPowerSum_two_re_le_trace_sq_sub_principal_seven
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian)
    {f r : ℂ[X]} (hf : f ≠ 0) (hr : r ≠ 0)
    (hfactor : A.charpoly = f * (X - C 7) * r) :
    (complexRootPowerSum f 2).re + 49 ≤
      (Matrix.trace (A ^ 2)).re := by
  have hlin : (X - C (7 : ℂ)) ≠ 0 := by
    intro h
    have hdegree := congrArg Polynomial.degree h
    norm_num at hdegree
  have hflin : f * (X - C (7 : ℂ)) ≠ 0 := mul_ne_zero hf hlin
  have hnonneg := complementary_secondMoment_nonnegative
    A hA hflin hr hfactor
  have hsumOuter := complexRootPowerSum_mul hflin hr 2
  have hsumInner := complexRootPowerSum_mul hf hlin 2
  have htrace := complexRootPowerSum_charpoly_eq_trace_pow A hA 2
  have hlinMoment : complexRootPowerSum (X - C (7 : ℂ)) 2 = 49 := by
    rw [complexRootPowerSum, Polynomial.roots_X_sub_C]
    norm_num
  rw [← htrace, hfactor, hsumOuter, hsumInner, hlinMoment]
  norm_num at hnonneg ⊢
  linarith

end

end Erdos85
