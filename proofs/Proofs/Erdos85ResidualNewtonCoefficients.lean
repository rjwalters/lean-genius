import Proofs.Erdos85QuadraticFactorRootMoments
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Newton identities for residual characteristic factors

This file turns second and fourth root power sums into the corresponding
coefficients of a monic split polynomial whose root sum is zero.
-/

open Polynomial

namespace Erdos85

noncomputable section

private theorem esymm_zero_succ {R : Type*} [CommRing R] (n : ℕ) :
    (0 : Multiset R).esymm (n + 1) = 0 := by
  simp [Multiset.esymm]

private theorem esymm_cons_succ
    {R : Type*} [CommRing R] (a : R) (s : Multiset R) (n : ℕ) :
    (a ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + a * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_add,
    Multiset.prod_cons, Multiset.sum_map_mul_left]

private theorem esymm_one_eq_sum
    {R : Type*} [CommRing R] (s : Multiset R) : s.esymm 1 = s.sum := by
  simp [Multiset.esymm, Multiset.powersetCard_one]

private theorem multiset_powerSum_two
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x => x ^ 2).sum = s.sum ^ 2 - 2 * s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ]
  | @cons a s ih =>
      simp [esymm_cons_succ, esymm_one_eq_sum, ih]
      ring

private theorem multiset_powerSum_three
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x => x ^ 3).sum =
      s.esymm 1 * (s.map fun x => x ^ 2).sum -
        s.esymm 2 * s.sum + 3 * s.esymm 3 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ]
  | @cons a s ih =>
      have htwo := multiset_powerSum_two s
      simp [esymm_cons_succ, esymm_one_eq_sum, ih, htwo]
      ring

private theorem multiset_powerSum_four
    {R : Type*} [CommRing R] (s : Multiset R) :
    (s.map fun x => x ^ 4).sum =
      s.esymm 1 * (s.map fun x => x ^ 3).sum -
        s.esymm 2 * (s.map fun x => x ^ 2).sum +
        s.esymm 3 * s.sum - 4 * s.esymm 4 := by
  induction s using Multiset.induction_on with
  | empty => simp [esymm_zero_succ]
  | @cons a s ih =>
      have htwo := multiset_powerSum_two s
      have hthree := multiset_powerSum_three s
      simp [esymm_cons_succ, esymm_one_eq_sum, ih, htwo, hthree]
      ring

/-- For a monic complex polynomial with at least four roots and zero next
coefficient, the second and fourth Newton identities directly identify its
second and fourth coefficients with its root power sums. -/
theorem monic_coeff_even_newton_of_nextCoeff_zero
    (p : ℂ[X]) (hp : p.Monic) (hdegree : 4 ≤ p.natDegree)
    (hnext : p.nextCoeff = 0) :
    2 * p.coeff (p.natDegree - 2) = -complexRootPowerSum p 2 ∧
    4 * p.coeff (p.natDegree - 4) =
      -(p.coeff (p.natDegree - 2) * complexRootPowerSum p 2 +
        complexRootPowerSum p 4) := by
  have hsplit : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree :=
    (splits_iff_card_roots.mp hsplit)
  have hsum : p.roots.sum = 0 := by
    have h := hsplit.nextCoeff_eq_neg_sum_roots_of_monic hp
    rw [hnext] at h
    simpa using neg_eq_zero.mp h.symm
  have hc2 : p.coeff (p.natDegree - 2) = p.roots.esymm 2 := by
    rw [p.coeff_eq_esymm_roots_of_splits hsplit (Nat.sub_le _ _), hp.leadingCoeff]
    rw [Nat.sub_sub_self (by omega : 2 ≤ p.natDegree)]
    norm_num
  have hc4 : p.coeff (p.natDegree - 4) = p.roots.esymm 4 := by
    rw [p.coeff_eq_esymm_roots_of_splits hsplit (Nat.sub_le _ _), hp.leadingCoeff]
    rw [Nat.sub_sub_self hdegree]
    norm_num
  have htwo := multiset_powerSum_two p.roots
  have hfour := multiset_powerSum_four p.roots
  rw [hsum, zero_pow (by norm_num : 2 ≠ 0), zero_sub] at htwo
  rw [esymm_one_eq_sum, hsum] at hfour
  simp at hfour
  change complexRootPowerSum p 2 = _ at htwo
  change complexRootPowerSum p 4 = _ at hfour
  change complexRootPowerSum p 4 =
    -(p.roots.esymm 2 * complexRootPowerSum p 2) -
      4 * p.roots.esymm 4 at hfour
  constructor
  · rw [hc2]
    linear_combination htwo
  · rw [hc2, hc4]
    linear_combination hfour

end

end Erdos85
