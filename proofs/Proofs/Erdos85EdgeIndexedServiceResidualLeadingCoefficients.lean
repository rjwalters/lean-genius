import Proofs.Erdos85EdgeIndexedServiceExactResidualFactor
import Proofs.Erdos85PolynomialSecondNewtonIdentity
import Proofs.Erdos85CyclePrimaryQuadraticTerminals
import Mathlib.RingTheory.Polynomial.Vieta

/-! # Leading coefficients of the h305 service residual -/

open Polynomial

namespace Erdos85

noncomputable section

private theorem esymm_zero_succ' {R : Type*} [CommRing R] (n : ℕ) :
    (0 : Multiset R).esymm (n + 1) = 0 := by
  simp [Multiset.esymm]

private theorem esymm_cons_succ'
    {R : Type*} [CommRing R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_add,
    Multiset.prod_cons, Multiset.sum_map_mul_left]

private theorem esymm_one_eq_sum'
    {R : Type*} [CommRing R] (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

private theorem multiset_powerSum_two'
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x ↦ x ^ 2).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ']
  | @cons a s ih =>
      simp [esymm_cons_succ', esymm_one_eq_sum', ih]
      ring

private theorem multiset_powerSum_three'
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x ↦ x ^ 3).sum =
      s.esymm 1 * (s.map fun x ↦ x ^ 2).sum -
        s.esymm 2 * s.sum + 3 * s.esymm 3 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ']
  | @cons a s ih =>
      have htwo := multiset_powerSum_two' s
      simp [esymm_cons_succ', esymm_one_eq_sum', ih, htwo]
      ring

private theorem multiset_powerSum_four'
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x ↦ x ^ 4).sum =
      s.esymm 1 * (s.map fun x ↦ x ^ 3).sum -
        s.esymm 2 * (s.map fun x ↦ x ^ 2).sum +
        s.esymm 3 * s.sum - 4 * s.esymm 4 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ']
  | @cons a s ih =>
      have htwo := multiset_powerSum_two' s
      have hthree := multiset_powerSum_three' s
      simp [esymm_cons_succ', esymm_one_eq_sum', ih, htwo, hthree]
      ring

/-- The first four residual power sums determine its top four non-leading
coefficients.  The cubic and quartic conclusions are denominator-free. -/
theorem h305_residual_leading_coefficients_of_powerSums
    (p : ℂ[X]) (hp : p.Monic) (hdeg : 4 ≤ p.natDegree)
    (h1 : complexRootPowerSum p 1 = -8)
    (h2 : complexRootPowerSum p 2 = 224)
    (tau : ℂ)
    (h3 : complexRootPowerSum p 3 = tau - 224)
    (h4 : complexRootPowerSum p 4 = 1792) :
    p.coeff (p.natDegree - 1) = 8 ∧
      p.coeff (p.natDegree - 2) = -80 ∧
      3 * p.coeff (p.natDegree - 3) = -tau - 2208 ∧
      3 * p.coeff (p.natDegree - 4) = 9024 - 8 * tau := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hc1 : p.coeff (p.natDegree - 1) = -p.roots.esymm 1 := by
    rw [p.coeff_eq_esymm_roots_of_splits hsplit (Nat.sub_le _ _),
      hp.leadingCoeff, Nat.sub_sub_self (by omega : 1 ≤ p.natDegree)]
    norm_num
  have hc2 : p.coeff (p.natDegree - 2) = p.roots.esymm 2 := by
    rw [p.coeff_eq_esymm_roots_of_splits hsplit (Nat.sub_le _ _),
      hp.leadingCoeff, Nat.sub_sub_self (by omega : 2 ≤ p.natDegree)]
    norm_num
  have hc3 : p.coeff (p.natDegree - 3) = -p.roots.esymm 3 := by
    rw [p.coeff_eq_esymm_roots_of_splits hsplit (Nat.sub_le _ _),
      hp.leadingCoeff, Nat.sub_sub_self (by omega : 3 ≤ p.natDegree)]
    norm_num
  have hc4 : p.coeff (p.natDegree - 4) = p.roots.esymm 4 := by
    rw [p.coeff_eq_esymm_roots_of_splits hsplit (Nat.sub_le _ _),
      hp.leadingCoeff, Nat.sub_sub_self hdeg]
    norm_num
  have hp1 : p.roots.sum = -8 := by
    rw [complexRootPowerSum] at h1
    simpa using h1
  have hp2 := multiset_powerSum_two' p.roots
  have hp3 := multiset_powerSum_three' p.roots
  have hp4 := multiset_powerSum_four' p.roots
  change complexRootPowerSum p 2 = _ at hp2
  change complexRootPowerSum p 3 =
    p.roots.esymm 1 * complexRootPowerSum p 2 -
      p.roots.esymm 2 * p.roots.sum + 3 * p.roots.esymm 3 at hp3
  change complexRootPowerSum p 4 =
    p.roots.esymm 1 * complexRootPowerSum p 3 -
      p.roots.esymm 2 * complexRootPowerSum p 2 +
      p.roots.esymm 3 * p.roots.sum - 4 * p.roots.esymm 4 at hp4
  rw [hp1, h2] at hp2
  rw [esymm_one_eq_sum', hp1, h2] at hp3
  rw [esymm_one_eq_sum', hp1, h2, h3] at hp4
  have he2 : p.roots.esymm 2 = -80 := by
    linear_combination (1 / 2) * hp2
  rw [he2] at hp3 hp4
  rw [h3] at hp3
  rw [h4] at hp4
  have he3 : 3 * p.roots.esymm 3 = tau + 2208 := by
    linear_combination -hp3
  constructor
  · rw [hc1, esymm_one_eq_sum', hp1]
    norm_num
  constructor
  · rw [hc2]
    exact he2
  constructor
  · rw [hc3]
    calc
      3 * -p.roots.esymm 3 = -(3 * p.roots.esymm 3) := by ring
      _ = -tau - 2208 := by rw [he3]; ring
  · rw [hc4]
    linear_combination (3 / 4) * hp4 - 2 * he3

/-- Degree-32 numerical indexing of the residual coefficient ledger. -/
theorem h305_degreeThirtyTwo_residual_leading_coefficients
    (p : ℂ[X]) (hp : p.Monic) (hpdeg : p.natDegree = 32)
    (h1 : complexRootPowerSum p 1 = -8)
    (h2 : complexRootPowerSum p 2 = 224)
    (tau : ℂ)
    (h3 : complexRootPowerSum p 3 = tau - 224)
    (h4 : complexRootPowerSum p 4 = 1792) :
    p.coeff 31 = 8 ∧ p.coeff 30 = -80 ∧
      3 * p.coeff 29 = -tau - 2208 ∧
      3 * p.coeff 28 = 9024 - 8 * tau := by
  have h := h305_residual_leading_coefficients_of_powerSums
    p hp (by omega) h1 h2 tau h3 h4
  simpa [hpdeg] using h

end

end Erdos85

#print axioms Erdos85.h305_residual_leading_coefficients_of_powerSums
#print axioms Erdos85.h305_degreeThirtyTwo_residual_leading_coefficients
