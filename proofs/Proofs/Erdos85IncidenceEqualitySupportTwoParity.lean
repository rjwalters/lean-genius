import Proofs.Erdos85IntegerZeroSumSupportBounds

/-!
# Parity exclusion of the two-support equality regime

A zero-sum integer vector supported at two coordinates has values `a,-a`.
If its square energy is divisible by four, then `a` is even.  Hence such a
vector cannot have an odd coordinate, as incidence-bottleneck diagonals do.
-/

open Finset BigOperators

namespace Erdos85

noncomputable section

private theorem sum_eq_sum_support_int
    {V : Type*} [Fintype V] [DecidableEq V] (y : V → ℤ) :
    ∑ v : V, y v = ∑ v ∈ finiteVectorSupport y, y v := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _hv hvnot
  exact not_ne_iff.mp ((mem_finiteVectorSupport y v).not.mp hvnot)

private theorem sum_sq_eq_sum_support_int
    {V : Type*} [Fintype V] [DecidableEq V] (y : V → ℤ) :
    ∑ v : V, y v ^ 2 = ∑ v ∈ finiteVectorSupport y, y v ^ 2 := by
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _hv hvnot
  have hy0 := not_ne_iff.mp ((mem_finiteVectorSupport y v).not.mp hvnot)
  simp [hy0]

/-- Two-support, zero-sum integer vectors with four-divisible square energy
are coordinatewise even. -/
theorem even_apply_of_support_card_two_of_sum_zero_of_four_dvd_sq_sum
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) {delta : ℕ}
    (hsupport : (finiteVectorSupport y).card = 2)
    (hsum : ∑ v, y v = 0)
    (henergy : ∑ v, y v ^ 2 = (delta : ℤ))
    (hfour : 4 ∣ delta) :
    ∀ v, Even (y v) := by
  obtain ⟨a, b, hab, hsupp⟩ := Finset.card_eq_two.mp hsupport
  have hasum : y a + y b = 0 := by
    have h := sum_eq_sum_support_int y
    rw [hsupp] at h
    simp [hab] at h
    omega
  have haenergy : y a ^ 2 + y b ^ 2 = (delta : ℤ) := by
    have h := sum_sq_eq_sum_support_int y
    rw [hsupp] at h
    simp [hab] at h
    omega
  obtain ⟨c, hc⟩ := hfour
  have hdelta : (delta : ℤ) = 4 * (c : ℤ) := by exact_mod_cast hc
  have hasq : y a ^ 2 = 2 * (c : ℤ) := by
    have hba : y b = -y a := by omega
    rw [hba] at haenergy
    rw [hdelta] at haenergy
    nlinarith
  have haEvenSq : Even (y a ^ 2) := ⟨c, by omega⟩
  have haEven : Even (y a) := (Int.even_pow.mp haEvenSq).1
  have hbEven : Even (y b) := by
    have hba : y b = -y a := by omega
    obtain ⟨d, hd⟩ := haEven
    use -d
    omega
  intro v
  by_cases hv : v ∈ finiteVectorSupport y
  · rw [hsupp] at hv
    rcases Finset.mem_insert.mp hv with rfl | hvb
    · exact haEven
    · have : v = b := Finset.mem_singleton.mp hvb
      simpa [this] using hbEven
  · have hyv : y v = 0 :=
      not_ne_iff.mp ((mem_finiteVectorSupport y v).not.mp hv)
    simp [hyv]

/-- In particular, an odd marked coordinate excludes the two-support
regime. -/
theorem support_card_ne_two_of_sum_zero_of_four_dvd_sq_sum_of_odd_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (y : V → ℤ) {delta : ℕ}
    (hsum : ∑ v, y v = 0)
    (henergy : ∑ v, y v ^ 2 = (delta : ℤ))
    (hfour : 4 ∣ delta) (x : V) (hodd : Odd (y x)) :
    (finiteVectorSupport y).card ≠ 2 := by
  intro htwo
  have heven :=
    even_apply_of_support_card_two_of_sum_zero_of_four_dvd_sq_sum
      y htwo hsum henergy hfour x
  exact (Int.not_odd_iff_even.mpr heven) hodd

end

end Erdos85

#print axioms
  Erdos85.even_apply_of_support_card_two_of_sum_zero_of_four_dvd_sq_sum
#print axioms
  Erdos85.support_card_ne_two_of_sum_zero_of_four_dvd_sq_sum_of_odd_apply
