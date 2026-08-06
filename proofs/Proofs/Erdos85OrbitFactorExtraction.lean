import Proofs.Erdos85OrbitParity
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
# Extracting an asymmetric irreducible orbit

This file converts failure of sign stability into failure of reflection
stability of the normalized irreducible-factor multiset.  Multiplicities are
retained: the witness may be a reflected pair occurring unequally often.
-/

namespace Erdos85

open Polynomial
open scoped Polynomial

/-- The monic normalization of the reflection `p(X) ↦ p(-X)`. -/
noncomputable def Polynomial.signedReflection {K : Type*} [Ring K]
    (p : Polynomial K) : Polynomial K :=
  (-1 : K) ^ p.natDegree • p.comp (-(Polynomial.X : Polynomial K))

theorem Polynomial.signedReflection_monic
    {K : Type*} [Field K] {p : Polynomial K} (hp : p.Monic) :
    (signedReflection p).Monic := by
  have ha : (-1 : K) ^ p.natDegree * (-1 : K) ^ p.natDegree = 1 := by
    rw [← mul_pow]
    simp
  have hreg : IsSMulRegular K ((-1 : K) ^ p.natDegree) :=
    IsSMulRegular.of_mul_eq_one (M := K) ha
  rw [Polynomial.Monic, signedReflection,
    Polynomial.leadingCoeff_smul_of_smul_regular _ hreg]
  simp [hp, ← pow_add]

theorem Polynomial.natDegree_signedReflection
    {K : Type*} [Field K] {p : Polynomial K} (hp : p.Monic) :
    (signedReflection p).natDegree = p.natDegree := by
  have ha : (-1 : K) ^ p.natDegree * (-1 : K) ^ p.natDegree = 1 := by
    rw [← mul_pow]
    simp
  have hreg : IsSMulRegular K ((-1 : K) ^ p.natDegree) :=
    IsSMulRegular.of_mul_eq_one (M := K) ha
  rw [signedReflection,
    Polynomial.natDegree_smul_of_smul_regular _ hreg,
    Polynomial.natDegree_comp_eq_of_mul_ne_zero]
  · simp
  · simp [hp.ne_zero]

theorem Polynomial.signedReflection_involutive
    {K : Type*} [Field K] {p : Polynomial K} (hp : p.Monic) :
    signedReflection (signedReflection p) = p := by
  have ha : (-1 : K) ^ p.natDegree * (-1 : K) ^ p.natDegree = 1 := by
    rw [← mul_pow]
    simp
  unfold signedReflection
  rw [show ((-1 : K) ^ p.natDegree •
      p.comp (-(Polynomial.X : Polynomial K))).natDegree = p.natDegree from
        natDegree_signedReflection hp]
  simp only [Polynomial.smul_comp, Polynomial.comp_neg_X_comp_neg_X, ← mul_smul, ha,
    one_smul]

theorem Polynomial.signedReflection_mul
    {K : Type*} [Field K] (p q : Polynomial K) (hp : p ≠ 0) (hq : q ≠ 0) :
    signedReflection (p * q) = signedReflection p * signedReflection q := by
  unfold signedReflection
  rw [Polynomial.natDegree_mul hp hq, pow_add, Polynomial.mul_comp, mul_smul]
  simp only [smul_mul_assoc, mul_smul_comm]
  rw [smul_comm]

theorem Polynomial.signedReflection_multiset_prod
    {K : Type*} [Field K] (s : Multiset (Polynomial K))
    (hs : ∀ p ∈ s, p ≠ 0) :
    signedReflection s.prod = (s.map signedReflection).prod := by
  induction s using Multiset.induction_on with
  | empty => simp [signedReflection]
  | @cons p s ih =>
      have hp : p ≠ 0 := hs p (by simp)
      have hsTail : ∀ q ∈ s, q ≠ 0 := fun q hq => hs q (by simp [hq])
      have hs0 : s.prod ≠ 0 := by
        rw [ne_eq, Multiset.prod_eq_zero_iff]
        exact fun hzero => hsTail 0 hzero rfl
      rw [Multiset.prod_cons, signedReflection_mul p s.prod hp hs0, Multiset.map_cons,
        Multiset.prod_cons, ih]
      exact hsTail

theorem Polynomial.signedReflection_eq_self_iff
    {K : Type*} [Field K] (p : Polynomial K) :
    signedReflection p = p ↔
      p.comp (-(Polynomial.X : Polynomial K)) = (-1 : K) ^ p.natDegree • p := by
  let a : K := (-1 : K) ^ p.natDegree
  have ha : a * a = 1 := by simp [a, ← pow_add]
  constructor
  · intro h
    have hh := congrArg (fun q : Polynomial K => a • q) h
    simpa only [signedReflection, a, ← mul_smul, ha, one_smul] using hh
  · intro h
    unfold signedReflection
    rw [h, ← mul_smul, ha, one_smul]

theorem Polynomial.normalizedFactors_not_reflectionStable_of_not_signStable
    {K : Type*} [Field K] [DecidableEq K] (q : Polynomial K) (hq : q.Monic)
    (hnot : q.comp (-(Polynomial.X : Polynomial K)) ≠
      (-1 : K) ^ q.natDegree • q) :
    (UniqueFactorizationMonoid.normalizedFactors q).map signedReflection ≠
      UniqueFactorizationMonoid.normalizedFactors q := by
  intro hmap
  have hq0 : q ≠ 0 := hq.ne_zero
  let s := UniqueFactorizationMonoid.normalizedFactors q
  have hs0 : ∀ p ∈ s, p ≠ 0 := by
    intro p hp
    exact (UniqueFactorizationMonoid.irreducible_of_normalized_factor p hp).ne_zero
  have hprod := signedReflection_multiset_prod s hs0
  have hprodq : s.prod = q := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hq0, hq.normalize_eq_self]
  have hfix : signedReflection q = q := by rw [← hprodq, hprod, hmap]
  exact hnot ((signedReflection_eq_self_iff q).mp hfix)

theorem Polynomial.exists_count_ne_of_not_signStable
    {K : Type*} [Field K] [DecidableEq K] (q : Polynomial K) (hq : q.Monic)
    (hnot : q.comp (-(Polynomial.X : Polynomial K)) ≠
      (-1 : K) ^ q.natDegree • q) :
    ∃ f : Polynomial K,
      ((UniqueFactorizationMonoid.normalizedFactors q).map signedReflection).count f ≠
        (UniqueFactorizationMonoid.normalizedFactors q).count f := by
  have hne := normalizedFactors_not_reflectionStable_of_not_signStable q hq hnot
  contrapose! hne
  exact Multiset.ext.mpr hne

/-- The discrepancy can be oriented onto an actual normalized irreducible
factor of `q`: that factor and its signed reflection occur with unequal
multiplicities. -/
theorem Polynomial.exists_normalizedFactor_reflection_count_ne_of_not_signStable
    {K : Type*} [Field K] [DecidableEq K] (q : Polynomial K) (hq : q.Monic)
    (hnot : q.comp (-(Polynomial.X : Polynomial K)) ≠
      (-1 : K) ^ q.natDegree • q) :
    ∃ f ∈ UniqueFactorizationMonoid.normalizedFactors q,
      (UniqueFactorizationMonoid.normalizedFactors q).count (signedReflection f) ≠
        (UniqueFactorizationMonoid.normalizedFactors q).count f := by
  let s := UniqueFactorizationMonoid.normalizedFactors q
  have hchange : s.map signedReflection ≠ s := by
    exact normalizedFactors_not_reflectionStable_of_not_signStable q hq hnot
  have hmonic : ∀ f ∈ s, f.Monic := by
    intro f hf
    have hnorm := UniqueFactorizationMonoid.normalize_normalized_factor f hf
    exact (Polynomial.normalize_eq_self_iff_monic
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor f hf).ne_zero).mp hnorm
  have hinj : Set.InjOn signedReflection {f : Polynomial K | f ∈ s} := by
    intro a ha b hb hab
    calc
      a = signedReflection (signedReflection a) := (signedReflection_involutive (hmonic a ha)).symm
      _ = signedReflection (signedReflection b) := congrArg signedReflection hab
      _ = b := signedReflection_involutive (hmonic b hb)
  by_contra hex
  push_neg at hex
  apply hchange
  apply Multiset.ext.mpr
  intro x
  by_cases hxmap : x ∈ s.map signedReflection
  · obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp hxmap
    rw [Multiset.count_map_eq_count signedReflection s hinj f hf]
    exact (hex f hf).symm
  · have hleft : (s.map signedReflection).count x = 0 :=
      Multiset.count_eq_zero.mpr hxmap
    rw [hleft]
    apply (Multiset.count_eq_zero.mpr ?_).symm
    intro hx
    have hrx : signedReflection x ∈ s := by
      have hpos : 0 < s.count x := Multiset.count_pos.mpr hx
      have := hex x hx
      exact Multiset.count_pos.mp (this.symm ▸ hpos)
    apply hxmap
    refine Multiset.mem_map.mpr ⟨signedReflection x, hrx, ?_⟩
    exact signedReflection_involutive (hmonic x hx)

end Erdos85
