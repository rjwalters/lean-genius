/-
  Angle Trisection - Galois Group of cos(40°) Minimal Polynomial (OQ-03)

  Proves: |Gal(8X³-6X+1/ℚ)| = 3

  The polynomial 8X³-6X+1 is the minimal polynomial of cos(40°) = cos(2π/9).
  Its three roots are cos(40°), cos(80°), cos(160°).

  Strategy (mirrors AngleTrisectionCos20Gal.lean for the cos(20°) case):
  - If α is a root, then β = 2α²-1 and γ = -2α²-α+1 are also roots
  - β = cos(80°) = 2cos²(40°)-1 (double-angle formula)
  - γ = -2α²-α+1 = -(α+β) (since α+β+γ = 0 by Vieta)
  - All roots ∈ ℚ(α) → SplittingField = ℚ(α) → [SF:ℚ] = 3 → |Gal| = 3

  Algebraic identities:
    cos(80°) = 2cos²(40°)-1 → β = 2α²-1
    γ = -(α+β) = -α-(2α²-1) = -2α²-α+1

  Irreducibility: 8X³-6X+1 = r(2X-2) where r = Y³+6Y²+9Y+3 is Eisenstein at 3.
  (Contrast with cos(20°): r = Y³-6Y²+9Y-3, substitution Y=2X+2.)

  0 sorries, 0 axioms.
-/

import Mathlib

open Polynomial IntermediateField FiniteDimensional

namespace AngleTrisectionCos20GalOQ03

/-
## Part I: Key Algebraic Identities
-/

/-- If 8a³-6a+1=0 in any commutative ring, then 2a²-1 is also a root.

    Algebraic identity: 8(2a²-1)³-6(2a²-1)+1 = (8a³-6a-1)(8a³-6a+1). -/
theorem root_image_beta {R : Type*} [CommRing R] (a : R)
    (ha : 8 * a ^ 3 - 6 * a + 1 = 0) :
    8 * (2 * a ^ 2 - 1) ^ 3 - 6 * (2 * a ^ 2 - 1) + 1 = 0 := by
  have key : 8 * (2 * a ^ 2 - 1) ^ 3 - 6 * (2 * a ^ 2 - 1) + 1 =
    (8 * a ^ 3 - 6 * a - 1) * (8 * a ^ 3 - 6 * a + 1) := by ring
  rw [key, ha, mul_zero]

/-- If 8a³-6a+1=0 in any commutative ring, then -2a²-a+1 is also a root.

    This is γ = -(α+β) = -(a + (2a²-1)) = -2a²-a+1.
    Algebraic identity: 8(-2a²-a+1)³-6(-2a²-a+1)+1 = (-8a³-12a²+3)(8a³-6a+1). -/
theorem root_image_gamma {R : Type*} [CommRing R] (a : R)
    (ha : 8 * a ^ 3 - 6 * a + 1 = 0) :
    8 * (-2 * a ^ 2 - a + 1) ^ 3 - 6 * (-2 * a ^ 2 - a + 1) + 1 = 0 := by
  have key : 8 * (-2 * a ^ 2 - a + 1) ^ 3 - 6 * (-2 * a ^ 2 - a + 1) + 1 =
    (-8 * a ^ 3 - 12 * a ^ 2 + 3) * (8 * a ^ 3 - 6 * a + 1) := by ring
  rw [key, ha, mul_zero]

/-
## Part II: Polynomial Properties
-/

/-- Shorthand for the polynomial 8X³-6X+1. -/
private noncomputable abbrev p : ℚ[X] := 8 * X ^ 3 - 6 * X + C 1

private theorem p_ne_zero : (p : ℚ[X]) ≠ 0 := by
  intro h
  have : Polynomial.eval 0 (p : ℚ[X]) = 1 := by simp [p]
  rw [h, Polynomial.eval_zero] at this
  norm_num at this

private theorem p_natDegree : (p : ℚ[X]).natDegree = 3 := by
  show (8 * X ^ 3 - 6 * X + C (1 : ℚ)).natDegree = 3
  compute_degree!

private theorem p_degree_ne_zero : (p : ℚ[X]).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree p_ne_zero, p_natDegree]
  exact (by norm_num : (3 : WithBot ℕ) ≠ 0)

/-
## Part II-B: Irreducibility of p via Eisenstein Criterion

Strategy: The polynomial q = Y³+6Y²+9Y+3 is Eisenstein at p=3, hence irreducible
over ℤ and ℚ. The linear substitution Y = 2X-2 gives q(2X-2) = 8X³-6X+1 = p.
Since irreducibility is preserved under invertible linear substitutions, p is irreducible.

Verification: (2X-2)³+6(2X-2)²+9(2X-2)+3
  = 8X³-24X²+24X-8+6(4X²-8X+4)+18X-18+3
  = 8X³-24X²+24X-8+24X²-48X+24+18X-18+3 = 8X³-6X+1 ✓
-/

/-- The Eisenstein polynomial: q = Y³+6Y²+9Y+3 over ℤ. -/
private noncomputable def q_eis_int : ℤ[X] := X ^ 3 + C 6 * X ^ 2 + C 9 * X + C 3

private theorem q_eis_int_natDegree : q_eis_int.natDegree = 3 := by
  unfold q_eis_int; compute_degree!

private theorem q_eis_int_degree : q_eis_int.degree = 3 := by
  unfold q_eis_int; compute_degree!

private theorem q_eis_int_monic : q_eis_int.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, q_eis_int_natDegree]
  unfold q_eis_int
  simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- q is irreducible over ℤ by Eisenstein's criterion at p = 3. -/
private theorem q_eis_int_irreducible : Irreducible q_eis_int := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(3 : ℤ)})
  · -- (3) is a prime ideal in ℤ
    rw [Ideal.span_singleton_prime (show (3 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · -- leadingCoeff ∉ (3)
    rw [show q_eis_int.leadingCoeff = 1 from q_eis_int_monic, Ideal.mem_span_singleton]
    norm_num
  · -- ∀ k < degree, coeff k ∈ (3)
    intro k hk
    rw [q_eis_int_degree] at hk
    have hkn : k < 3 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    unfold q_eis_int
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · -- 0 < degree
    rw [q_eis_int_degree]; exact_mod_cast Nat.zero_lt_succ 2
  · -- coeff 0 ∉ (3)²
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold q_eis_int
    simp only [coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · -- isPrimitive (monic → primitive)
    exact q_eis_int_monic.isPrimitive

/-- The same polynomial over ℚ. -/
private noncomputable def q_eis_rat : ℚ[X] := X ^ 3 + C 6 * X ^ 2 + C 9 * X + C 3

/-- q is irreducible over ℚ (Gauss's lemma: monic + ℤ-irreducible → ℚ-irreducible). -/
private theorem q_eis_rat_irreducible : Irreducible q_eis_rat := by
  have hprim := q_eis_int_monic.isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp q_eis_int_irreducible
  have heq : q_eis_rat = Polynomial.map (Int.castRingHom ℚ) q_eis_int := by
    unfold q_eis_rat q_eis_int
    simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.map_X, Polynomial.map_pow]
    norm_num
  rwa [heq]

/-- Key identity: q(2X-2) = p, i.e., substituting Y = 2X-2 transforms q into p.
    Verified by expanding: (2X-2)³+6(2X-2)²+9(2X-2)+3 = 8X³-6X+1. -/
private theorem q_comp_eq_p :
    q_eis_rat.comp (C 2 * X - C 2) = p := by
  apply Polynomial.funext; intro x
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  unfold q_eis_rat p
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  ring

/-- 8X³-6X+1 is irreducible over ℚ.

    Proof: The shifted polynomial q = Y³+6Y²+9Y+3 is Eisenstein at p=3,
    so q is irreducible over ℚ by Gauss's lemma. Since p = q(2X-2)
    and the substitution X ↦ 2X-2 is invertible (inverse: X ↦ X/2+1),
    irreducibility transfers from q to p. -/
private theorem p_irreducible : Irreducible (p : ℚ[X]) := by
  rw [← q_comp_eq_p]
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · -- q.comp ℓ is not a unit (has degree 3)
    intro h
    have hd := Polynomial.natDegree_eq_zero_of_isUnit h
    have : (q_eis_rat.comp (C 2 * X - C 2)).natDegree = 3 := by
      rw [q_comp_eq_p]; exact p_natDegree
    omega
  · -- if q.comp ℓ = a * b, then one is a unit
    intro a b hab
    set ℓ := (C (2 : ℚ) * X - C 2 : ℚ[X])
    set ℓ_inv := (C (2⁻¹ : ℚ) * X + C 1 : ℚ[X])
    have hq_factor : q_eis_rat = (a.comp ℓ_inv) * (b.comp ℓ_inv) := by
      have h1 : ℓ.comp ℓ_inv = X := by
        ext n
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X, coeff_C]
        rcases n with _ | _ | _ <;> simp <;> ring
      calc q_eis_rat
          = q_eis_rat.comp X := q_eis_rat.comp_X.symm
        _ = q_eis_rat.comp (ℓ.comp ℓ_inv) := by rw [h1]
        _ = (q_eis_rat.comp ℓ).comp ℓ_inv := (q_eis_rat.comp_assoc ℓ ℓ_inv).symm
        _ = (a * b).comp ℓ_inv := by rw [hab]
        _ = (a.comp ℓ_inv) * (b.comp ℓ_inv) := Polynomial.mul_comp a b ℓ_inv
    rcases q_eis_rat_irreducible.isUnit_or_isUnit hq_factor with ha | hb
    · left
      rw [Polynomial.isUnit_iff] at ha
      obtain ⟨c, hc_ne, hc_eq⟩ := ha
      have h_inv : ℓ_inv.comp ℓ = X := by
        ext n
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X, coeff_C]
        rcases n with _ | _ | _ <;> simp <;> ring
      have ha_eq : a = (a.comp ℓ_inv).comp ℓ := by
        conv_lhs => rw [← a.comp_X, ← h_inv]
        exact (a.comp_assoc ℓ_inv ℓ).symm
      rw [Polynomial.isUnit_iff]
      exact ⟨c, hc_ne, by rw [ha_eq, ← hc_eq, Polynomial.C_comp]⟩
    · right
      rw [Polynomial.isUnit_iff] at hb
      obtain ⟨c, hc_ne, hc_eq⟩ := hb
      have h_inv : ℓ_inv.comp ℓ = X := by
        ext n
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp, Polynomial.add_comp,
          Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X, coeff_C]
        rcases n with _ | _ | _ <;> simp <;> ring
      have hb_eq : b = (b.comp ℓ_inv).comp ℓ := by
        conv_lhs => rw [← b.comp_X, ← h_inv]
        exact (b.comp_assoc ℓ_inv ℓ).symm
      rw [Polynomial.isUnit_iff]
      exact ⟨c, hc_ne, by rw [hb_eq, ← hc_eq, Polynomial.C_comp]⟩

private theorem p_separable : (p : ℚ[X]).Separable :=
  p_irreducible.separable

/-
## Part III: Splitting Field Analysis
-/

/-- Evaluation of p at an element equals 8a³-6a+1. -/
private theorem p_eval_eq {R : Type*} [CommRing R] [Algebra ℚ R] (a : R) :
    Polynomial.aeval a p = 8 * a ^ 3 - 6 * a + 1 := by
  simp [p, map_add, map_sub, map_mul, map_pow, map_ofNat, Polynomial.aeval_X]

private theorem p_map_degree_ne :
    (p.map (algebraMap ℚ p.SplittingField)).degree ≠ 0 := by
  rw [degree_map_eq_of_injective (RingHom.injective (algebraMap ℚ p.SplittingField))]
  exact p_degree_ne_zero

/-- In the splitting field, get a root via rootOfSplits. -/
private noncomputable def root_in_sf : p.SplittingField :=
  rootOfSplits (SplittingField.splits p) p_map_degree_ne

/-- The root satisfies p(α) = 0. -/
private theorem root_is_root :
    Polynomial.aeval root_in_sf p = 0 := by
  unfold root_in_sf
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  exact eval_rootOfSplits _ p_map_degree_ne

/-- The root satisfies 8α³-6α+1 = 0. -/
private theorem root_eq_zero :
    8 * root_in_sf ^ 3 - 6 * root_in_sf + 1 = 0 := by
  have := root_is_root
  rwa [p_eval_eq] at this

/-- β = 2α²-1 is a root of p in the splitting field. -/
private theorem beta_is_root :
    Polynomial.aeval (2 * root_in_sf ^ 2 - 1) p = 0 := by
  rw [p_eval_eq]
  exact root_image_beta root_in_sf root_eq_zero

/-- γ = -2α²-α+1 is a root of p in the splitting field. -/
private theorem gamma_is_root :
    Polynomial.aeval (-2 * root_in_sf ^ 2 - root_in_sf + 1) p = 0 := by
  rw [p_eval_eq]
  exact root_image_gamma root_in_sf root_eq_zero

/-
## Part IV: Lower and Upper Bounds on |Gal|
-/

/-- 3 divides |Gal(p)|. -/
private theorem three_dvd_gal_card :
    3 ∣ Fintype.card p.Gal := by
  have h := Polynomial.Gal.prime_degree_dvd_card p_irreducible
    (show Nat.Prime p.natDegree by rw [p_natDegree]; decide)
  rw [Nat.card_eq_fintype_card, p_natDegree] at h
  exact h

/-- |Gal(p)| divides 6 (= 3!). -/
private theorem gal_card_dvd_six :
    Fintype.card p.Gal ∣ 6 := by
  classical
  haveI : Fact (map (algebraMap ℚ p.SplittingField) p).Splits :=
    ⟨SplittingField.splits p⟩
  have hinj := Polynomial.Gal.galActionHom_injective p p.SplittingField
  have hdvd : Nat.card p.Gal ∣ Nat.card (Equiv.Perm (p.rootSet p.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm] at hdvd
  have hcard : Fintype.card (p.rootSet p.SplittingField) = 3 :=
    (Polynomial.card_rootSet_eq_natDegree p_separable
      (SplittingField.splits p)).trans p_natDegree
  rw [hcard] at hdvd
  simpa using hdvd

/-
## Part V: The Splitting Field Has Degree 3
-/

/-- The root α is integral over ℚ. -/
private theorem root_integral : IsIntegral ℚ root_in_sf :=
  .of_finite ℚ root_in_sf

/-- The minpoly of α has natDegree 3. -/
private theorem minpoly_natDegree :
    (minpoly ℚ root_in_sf).natDegree = 3 := by
  have hdvd : minpoly ℚ root_in_sf ∣ p :=
    minpoly.dvd ℚ root_in_sf (by rw [p_eval_eq]; exact root_eq_zero)
  have hirr_min := minpoly.irreducible root_integral
  have hassoc := hirr_min.dvd_symm p_irreducible hdvd
  apply le_antisymm
  · calc (minpoly ℚ root_in_sf).natDegree ≤ p.natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd p_ne_zero
      _ = 3 := p_natDegree
  · calc 3 = p.natDegree := p_natDegree.symm
      _ ≤ (minpoly ℚ root_in_sf).natDegree :=
          Polynomial.natDegree_le_of_dvd hassoc (minpoly.ne_zero root_integral)

/-- [ℚ(α):ℚ] = 3. -/
private theorem adjoin_finrank :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      ({root_in_sf} : Set p.SplittingField)) = 3 := by
  rw [IntermediateField.adjoin.finrank root_integral, minpoly_natDegree]

/-- β = 2α²-1 is in ℚ(α). -/
private theorem beta_in_adjoin :
    (2 * root_in_sf ^ 2 - 1 : p.SplittingField) ∈
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  have hα : root_in_sf ∈ S := IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  have hαα : root_in_sf * root_in_sf ∈ S := S.mul_mem hα hα
  have h2αα : (2 : p.SplittingField) * (root_in_sf * root_in_sf) ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hαα
  show 2 * root_in_sf ^ 2 - 1 ∈ S
  have heq : 2 * root_in_sf ^ 2 - 1 = (2 : p.SplittingField) * (root_in_sf * root_in_sf) - 1 := by ring
  rw [heq]
  exact S.sub_mem h2αα S.one_mem

/-- γ = -2α²-α+1 is in ℚ(α). -/
private theorem gamma_in_adjoin :
    (-2 * root_in_sf ^ 2 - root_in_sf + 1 : p.SplittingField) ∈
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  have hα : root_in_sf ∈ S := IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  have hαα : root_in_sf * root_in_sf ∈ S := S.mul_mem hα hα
  have h2αα : (2 : p.SplittingField) * (root_in_sf * root_in_sf) ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hαα
  show -2 * root_in_sf ^ 2 - root_in_sf + 1 ∈ S
  have heq : -2 * root_in_sf ^ 2 - root_in_sf + 1 =
    1 - (2 : p.SplittingField) * (root_in_sf * root_in_sf) - root_in_sf := by ring
  rw [heq]
  exact S.sub_mem (S.sub_mem S.one_mem h2αα) hα

/-- Factored form: 8a³-6a+1 = 8(a-α)(a-β)(a-γ) when 8α³-6α+1 = 0.

    Ring identity: 8a³-6a+1 - 8(a-α)(a-(2α²-1))(a-(-2α²-α+1))
    = ((4α+2)·a + (-4α²-2α+1))·(8α³-6α+1). -/
private theorem factored_eval_eq {R : Type*} [CommRing R] (α a : R)
    (hα : 8 * α ^ 3 - 6 * α + 1 = 0) :
    8 * a ^ 3 - 6 * a + 1 =
    8 * (a - α) * (a - (2 * α ^ 2 - 1)) * (a - (-2 * α ^ 2 - α + 1)) := by
  have h : 8 * a ^ 3 - 6 * a + 1 -
    8 * (a - α) * (a - (2 * α ^ 2 - 1)) * (a - (-2 * α ^ 2 - α + 1)) = 0 := by
    have key : 8 * a ^ 3 - 6 * a + 1 -
      8 * (a - α) * (a - (2 * α ^ 2 - 1)) * (a - (-2 * α ^ 2 - α + 1)) =
      ((4 * α + 2) * a + (-4 * α ^ 2 - 2 * α + 1)) * (8 * α ^ 3 - 6 * α + 1) := by ring
    rw [key, hα, mul_zero]
  exact sub_eq_zero.mp h

/-- Every root of p in the splitting field lies in ℚ(α). -/
private theorem rootSet_subset_adjoin :
    (p.rootSet p.SplittingField : Set p.SplittingField) ⊆
    (IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) :
      Set p.SplittingField) := by
  intro r hr
  have hr_aeval : Polynomial.aeval r p = 0 := (Polynomial.mem_rootSet.mp hr).2
  have hr_root : 8 * r ^ 3 - 6 * r + 1 = 0 := by rwa [p_eval_eq] at hr_aeval
  have hfact := factored_eval_eq root_in_sf r root_eq_zero
  rw [hr_root] at hfact
  have h8 : (8 : p.SplittingField) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp hfact.symm with h12 | h3
  · rcases mul_eq_zero.mp h12 with h8a | h2
    · rw [sub_eq_zero.mp ((mul_eq_zero.mp h8a).resolve_left h8)]
      exact IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
    · rw [sub_eq_zero.mp h2]
      exact beta_in_adjoin
  · rw [sub_eq_zero.mp h3]
    exact gamma_in_adjoin

/-- The splitting field is generated by α alone. -/
private theorem adjoin_root_eq_top :
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) = ⊤ := by
  have hgen : Algebra.adjoin ℚ (p.rootSet p.SplittingField : Set p.SplittingField) = ⊤ :=
    Polynomial.SplittingField.adjoin_rootSet (K := ℚ) (f := p)
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  have hsub := rootSet_subset_adjoin
  have halg : Algebra.adjoin ℚ (p.rootSet p.SplittingField : Set p.SplittingField) ≤
    S.toSubalgebra := Algebra.adjoin_le (fun x hx => hsub hx)
  rw [eq_top_iff]
  intro x _
  exact halg (hgen ▸ Algebra.mem_top)

/-- Module.finrank ℚ p.SplittingField = 3. -/
theorem splitting_finrank :
    Module.finrank ℚ p.SplittingField = 3 := by
  have htop := adjoin_root_eq_top
  have h_top_eq : Module.finrank ℚ
    (↥(IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField))) =
    Module.finrank ℚ p.SplittingField := by
    rw [htop]
    exact LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
  rw [← h_top_eq, adjoin_finrank]

/-
## Part VI: Main Theorem
-/

/-- |Gal(8X³-6X+1/ℚ)| = 3.

    This is the Galois group of the minimal polynomial of cos(40°) = cos(2π/9).
    The three roots are cos(40°), cos(80°), cos(160°).
    All three lie in ℚ(cos(40°)), making the splitting field degree 3 over ℚ. -/
theorem cos40_gal_card :
    Fintype.card (8 * X ^ 3 - 6 * X + C 1 : ℚ[X]).Gal = 3 := by
  have hcard := Polynomial.Gal.card_of_separable p_separable
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard, splitting_finrank]

/-- The polynomial 8X³-6X+1 is irreducible over ℚ (public interface).
    Proved via Eisenstein's criterion on the shifted polynomial Y³+6Y²+9Y+3. -/
theorem cos40_poly_irreducible :
    Irreducible (8 * X ^ 3 - 6 * X + C 1 : ℚ[X]) :=
  p_irreducible

end AngleTrisectionCos20GalOQ03
