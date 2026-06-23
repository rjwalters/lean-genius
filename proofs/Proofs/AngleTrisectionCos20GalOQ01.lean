/-
  Angle Trisection - Galois Group of cos(π/7) Minimal Polynomial

  Proves: |Gal(8X³-4X²-4X+1/ℚ)| = 3

  The polynomial 8X³-4X²-4X+1 is the minimal polynomial of cos(π/7).
  Its three roots are cos(π/7), cos(3π/7), cos(5π/7).

  Strategy (mirrors AngleTrisectionCos20Gal.lean for the cos(20°) case):
  - If α is a root, then γ = 1-2α² and β = 2α²-α-1/2 are also roots
  - These correspond to cos(5π/7) and cos(3π/7) respectively
  - All roots ∈ ℚ(α) → SplittingField = ℚ(α) → [SF:ℚ] = 3 → |Gal| = 3

  Algebraic identities:
    cos(5π/7) = -cos(2π/7) = -(2cos²(π/7)-1) = 1-2α²
    cos(3π/7) = 4cos³(π/7)-3cos(π/7) = 4α³-3α ≡ 2α²-α-1/2 (mod 8α³-4α²-4α+1)

  Irreducibility: 8X³-4X²-4X+1 = r(2X+2) where r = Y³-7Y²+14Y-7 is Eisenstein at 7.
  (Contrast with cos(20°): r = Y³-6Y²+9Y-3 Eisenstein at 3.)

  0 sorries, 0 axioms.
-/

import Mathlib

open Polynomial IntermediateField FiniteDimensional

namespace AngleTrisectionCos20GalOQ01

/-
## Part I: Key Algebraic Identities
-/

/-- If 8a³-4a²-4a+1=0 in any commutative ring, then 1-2a² is also a root. -/
theorem root_image_gamma {R : Type*} [CommRing R] (a : R)
    (ha : 8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1 = 0) :
    8 * (1 - 2 * a ^ 2) ^ 3 - 4 * (1 - 2 * a ^ 2) ^ 2 - 4 * (1 - 2 * a ^ 2) + 1 = 0 := by
  have key : 8 * (1 - 2 * a ^ 2) ^ 3 - 4 * (1 - 2 * a ^ 2) ^ 2 - 4 * (1 - 2 * a ^ 2) + 1 =
    (-8 * a ^ 3 - 4 * a ^ 2 + 4 * a + 1) * (8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1) := by ring
  rw [key, ha, mul_zero]

/-- If 8a³-4a²-4a+1=0 in a characteristic-zero field, then 2a²-a-1/2 is also a root.
    Note: 2a²-a-1/2 = cos(3π/7) when a = cos(π/7). Requires char ≠ 2 (satisfied by ℚ-algebras). -/
theorem root_image_beta {F : Type*} [Field F] [CharZero F] (a : F)
    (ha : 8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1 = 0) :
    8 * (2 * a ^ 2 - a - 1 / 2) ^ 3 - 4 * (2 * a ^ 2 - a - 1 / 2) ^ 2 -
    4 * (2 * a ^ 2 - a - 1 / 2) + 1 = 0 := by
  have key : 8 * (2 * a ^ 2 - a - 1 / 2) ^ 3 - 4 * (2 * a ^ 2 - a - 1 / 2) ^ 2 -
    4 * (2 * a ^ 2 - a - 1 / 2) + 1 =
    (8 * a ^ 3 - 8 * a ^ 2 - 2 * a + 1) * (8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1) := by
    field_simp; ring
  rw [key, ha, mul_zero]

/-
## Part II: Polynomial Properties
-/

/-- Shorthand for the polynomial 8X³-4X²-4X+1. -/
private noncomputable abbrev pCos7 : ℚ[X] := 8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1

private theorem pCos7_ne_zero : (pCos7 : ℚ[X]) ≠ 0 := by
  intro h
  have : Polynomial.eval 0 (pCos7 : ℚ[X]) = 1 := by simp [pCos7]
  rw [h, Polynomial.eval_zero] at this
  norm_num at this

private theorem pCos7_natDegree : (pCos7 : ℚ[X]).natDegree = 3 := by
  show (8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C (1 : ℚ)).natDegree = 3
  norm_num [natDegree_sub_eq_left_of_natDegree_lt, natDegree_add_eq_left_of_natDegree_lt,
    natDegree_mul, natDegree_pow, natDegree_X, natDegree_C, natDegree_one]

private theorem pCos7_degree_ne_zero : (pCos7 : ℚ[X]).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree pCos7_ne_zero, pCos7_natDegree]
  exact (by norm_num : (3 : WithBot ℕ) ≠ 0)

/-
## Part II-B: Irreducibility via Eisenstein Criterion

Strategy: r = Y³-7Y²+14Y-7 is Eisenstein at p=7, hence irreducible over ℤ and ℚ.
The linear substitution Y = 2X+2 gives r(2X+2) = 8X³-4X²-4X+1.
Irreducibility is preserved under invertible linear substitutions.
-/

/-- The Eisenstein polynomial: r = Y³ - 7Y² + 14Y - 7 over ℤ. -/
private noncomputable def r_eis_int : ℤ[X] := X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7

private theorem r_eis_int_natDegree : r_eis_int.natDegree = 3 := by
  unfold r_eis_int; compute_degree!

private theorem r_eis_int_degree : r_eis_int.degree = 3 := by
  unfold r_eis_int; compute_degree!

private theorem r_eis_int_monic : r_eis_int.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, r_eis_int_natDegree]
  unfold r_eis_int
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- r = Y³-7Y²+14Y-7 is irreducible over ℤ by Eisenstein's criterion at p = 7. -/
private theorem r_eis_int_irreducible : Irreducible r_eis_int := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(7 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (7 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [show r_eis_int.leadingCoeff = 1 from r_eis_int_monic, Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [r_eis_int_degree] at hk
    have hkn : k < 3 := WithBot.coe_lt_coe.mp hk
    simp only [Ideal.mem_span_singleton]
    unfold r_eis_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [r_eis_int_degree]; exact_mod_cast Nat.zero_lt_succ 2
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold r_eis_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · exact r_eis_int_monic.isPrimitive

/-- The same polynomial over ℚ. -/
private noncomputable def r_eis_rat : ℚ[X] := X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7

/-- r is irreducible over ℚ (Gauss's lemma). -/
private theorem r_eis_rat_irreducible : Irreducible r_eis_rat := by
  have hprim := r_eis_int_monic.isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp r_eis_int_irreducible
  have heq : r_eis_rat = Polynomial.map (Int.castRingHom ℚ) r_eis_int := by
    unfold r_eis_rat r_eis_int
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow]
    norm_num
  rwa [heq]

/-- Key identity: r(2X+2) = pCos7, i.e., the substitution Y=2X+2 transforms r into pCos7. -/
private theorem r_comp_eq_pCos7 :
    r_eis_rat.comp (C 2 * X + C 2) = pCos7 := by
  apply Polynomial.funext; intro x
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, r_eis_rat]
  simp only [pCos7, Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  ring

/-- 8X³-4X²-4X+1 is irreducible over ℚ. -/
private theorem pCos7_irreducible : Irreducible (pCos7 : ℚ[X]) := by
  rw [← r_comp_eq_pCos7]
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro h
    have hd := Polynomial.natDegree_eq_zero_of_isUnit h
    have : (r_eis_rat.comp (C 2 * X + C 2)).natDegree = 3 := by
      rw [r_comp_eq_pCos7]; exact pCos7_natDegree
    omega
  · intro a b hab
    set ℓ := (C (2 : ℚ) * X + C 2 : ℚ[X])
    set ℓ_inv := (C (2⁻¹ : ℚ) * X - C 1 : ℚ[X])
    have hq_factor : r_eis_rat = (a.comp ℓ_inv) * (b.comp ℓ_inv) := by
      have h1 : ℓ.comp ℓ_inv = X := by
        ext n
        simp only [ℓ, ℓ_inv, Polynomial.add_comp,
          Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X, coeff_C]
        rcases n with _ | _ | _ <;> simp <;> ring
      calc r_eis_rat
          = r_eis_rat.comp X := r_eis_rat.comp_X.symm
        _ = r_eis_rat.comp (ℓ.comp ℓ_inv) := by rw [h1]
        _ = (r_eis_rat.comp ℓ).comp ℓ_inv := (r_eis_rat.comp_assoc ℓ ℓ_inv).symm
        _ = (a * b).comp ℓ_inv := by rw [hab]
        _ = (a.comp ℓ_inv) * (b.comp ℓ_inv) := Polynomial.mul_comp a b ℓ_inv
    rcases r_eis_rat_irreducible.isUnit_or_isUnit hq_factor with ha | hb
    · left
      rw [Polynomial.isUnit_iff] at ha
      obtain ⟨c, hc_ne, hc_eq⟩ := ha
      have h_inv : ℓ_inv.comp ℓ = X := by
        ext n
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp,
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
        simp only [ℓ, ℓ_inv, Polynomial.sub_comp,
          Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X, coeff_C]
        rcases n with _ | _ | _ <;> simp <;> ring
      have hb_eq : b = (b.comp ℓ_inv).comp ℓ := by
        conv_lhs => rw [← b.comp_X, ← h_inv]
        exact (b.comp_assoc ℓ_inv ℓ).symm
      rw [Polynomial.isUnit_iff]
      exact ⟨c, hc_ne, by rw [hb_eq, ← hc_eq, Polynomial.C_comp]⟩

private theorem pCos7_separable : (pCos7 : ℚ[X]).Separable :=
  pCos7_irreducible.separable

/-
## Part III: Splitting Field Analysis
-/

/-- Evaluation of pCos7 at an element equals 8a³-4a²-4a+1. -/
private theorem pCos7_eval_eq {R : Type*} [CommRing R] [Algebra ℚ R] (a : R) :
    Polynomial.aeval a pCos7 = 8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1 := by
  simp [pCos7, map_sub, map_add, map_mul, map_pow, map_ofNat, Polynomial.aeval_X]

private theorem pCos7_map_degree_ne :
    (pCos7.map (algebraMap ℚ pCos7.SplittingField)).degree ≠ 0 := by
  rw [degree_map_eq_of_injective (RingHom.injective (algebraMap ℚ pCos7.SplittingField))]
  exact pCos7_degree_ne_zero

/-- In the splitting field, get a root via rootOfSplits. -/
private noncomputable def root_in_sf : pCos7.SplittingField :=
  rootOfSplits (SplittingField.splits pCos7) pCos7_map_degree_ne

private theorem root_is_root :
    Polynomial.aeval root_in_sf pCos7 = 0 := by
  unfold root_in_sf
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  exact eval_rootOfSplits _ pCos7_map_degree_ne

private theorem root_eq_zero :
    8 * root_in_sf ^ 3 - 4 * root_in_sf ^ 2 - 4 * root_in_sf + 1 = 0 := by
  have := root_is_root
  rwa [pCos7_eval_eq] at this

/-- β = 2α²-α-1/2 is a root of pCos7 in the splitting field. -/
private theorem beta_is_root :
    Polynomial.aeval (2 * root_in_sf ^ 2 - root_in_sf - 1 / 2) pCos7 = 0 := by
  rw [pCos7_eval_eq]
  exact root_image_beta root_in_sf root_eq_zero

/-- γ = 1-2α² is a root of pCos7 in the splitting field. -/
private theorem gamma_is_root :
    Polynomial.aeval (1 - 2 * root_in_sf ^ 2) pCos7 = 0 := by
  rw [pCos7_eval_eq]
  exact root_image_gamma root_in_sf root_eq_zero

/-
## Part IV: Divisibility Bounds on |Gal|
-/

private theorem three_dvd_gal_card :
    3 ∣ Fintype.card pCos7.Gal := by
  have h := Polynomial.Gal.prime_degree_dvd_card pCos7_irreducible
    (show Nat.Prime pCos7.natDegree by rw [pCos7_natDegree]; decide)
  rw [Nat.card_eq_fintype_card, pCos7_natDegree] at h
  exact h

private theorem gal_card_dvd_six :
    Fintype.card pCos7.Gal ∣ 6 := by
  classical
  haveI : Fact (map (algebraMap ℚ pCos7.SplittingField) pCos7).Splits :=
    ⟨SplittingField.splits pCos7⟩
  have hinj := Polynomial.Gal.galActionHom_injective pCos7 pCos7.SplittingField
  have hdvd : Nat.card pCos7.Gal ∣ Nat.card (Equiv.Perm (pCos7.rootSet pCos7.SplittingField)) :=
    Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_perm] at hdvd
  have hcard : Fintype.card (pCos7.rootSet pCos7.SplittingField) = 3 :=
    (Polynomial.card_rootSet_eq_natDegree pCos7_separable
      (SplittingField.splits pCos7)).trans pCos7_natDegree
  rw [hcard] at hdvd
  simpa using hdvd

/-
## Part V: Splitting Field Has Degree 3

All roots of pCos7 lie in ℚ(α), so SplittingField = ℚ(α) and [SF:ℚ] = 3.
-/

private theorem root_integral : IsIntegral ℚ root_in_sf :=
  .of_finite ℚ root_in_sf

private theorem minpoly_natDegree :
    (minpoly ℚ root_in_sf).natDegree = 3 := by
  have hdvd : minpoly ℚ root_in_sf ∣ pCos7 :=
    minpoly.dvd ℚ root_in_sf (by rw [pCos7_eval_eq]; exact root_eq_zero)
  have hirr_min := minpoly.irreducible root_integral
  have hassoc := hirr_min.dvd_symm pCos7_irreducible hdvd
  apply le_antisymm
  · calc (minpoly ℚ root_in_sf).natDegree ≤ pCos7.natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd pCos7_ne_zero
      _ = 3 := pCos7_natDegree
  · calc 3 = pCos7.natDegree := pCos7_natDegree.symm
      _ ≤ (minpoly ℚ root_in_sf).natDegree :=
          Polynomial.natDegree_le_of_dvd hassoc (minpoly.ne_zero root_integral)

private theorem adjoin_finrank :
    Module.finrank ℚ (IntermediateField.adjoin ℚ
      ({root_in_sf} : Set pCos7.SplittingField)) = 3 := by
  rw [IntermediateField.adjoin.finrank root_integral, minpoly_natDegree]

/-- β = 2α²-α-1/2 is in ℚ(α). -/
private theorem beta_in_adjoin :
    (2 * root_in_sf ^ 2 - root_in_sf - 1 / 2 : pCos7.SplittingField) ∈
    IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField)
  have hα : root_in_sf ∈ S := IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  have hαα : root_in_sf * root_in_sf ∈ S := S.mul_mem hα hα
  have h2αα : (2 : pCos7.SplittingField) * (root_in_sf * root_in_sf) ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hαα
  have h2_mem : (2 : pCos7.SplittingField) ∈ S := by
    have : ((2 : ℚ) : pCos7.SplittingField) ∈ S := S.algebraMap_mem 2
    exact_mod_cast this
  have h12 : (1 / 2 : pCos7.SplittingField) ∈ S := S.div_mem S.one_mem h2_mem
  show 2 * root_in_sf ^ 2 - root_in_sf - 1 / 2 ∈ S
  have heq : 2 * root_in_sf ^ 2 - root_in_sf - 1 / 2 =
    (2 : pCos7.SplittingField) * (root_in_sf * root_in_sf) - root_in_sf - 1 / 2 := by ring
  rw [heq]
  exact S.sub_mem (S.sub_mem h2αα hα) h12

/-- γ = 1-2α² is in ℚ(α). -/
private theorem gamma_in_adjoin :
    (1 - 2 * root_in_sf ^ 2 : pCos7.SplittingField) ∈
    IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField)
  have hα : root_in_sf ∈ S := IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  have hαα : root_in_sf * root_in_sf ∈ S := S.mul_mem hα hα
  have h2αα : (2 : pCos7.SplittingField) * (root_in_sf * root_in_sf) ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hαα
  show 1 - 2 * root_in_sf ^ 2 ∈ S
  have heq : 1 - 2 * root_in_sf ^ 2 =
    1 - (2 : pCos7.SplittingField) * (root_in_sf * root_in_sf) := by ring
  rw [heq]
  exact S.sub_mem S.one_mem h2αα

/-- Factored form: 8a³-4a²-4a+1 = 8(a-α)(a-β)(a-γ) when 8α³-4α²-4α+1=0.
    Requires CharZero (satisfied by pCos7.SplittingField as a ℚ-algebra). -/
private theorem factored_eval_eq {F : Type*} [Field F] [CharZero F] (α a : F)
    (hα : 8 * α ^ 3 - 4 * α ^ 2 - 4 * α + 1 = 0) :
    8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1 =
    8 * (a - α) * (a - (2 * α ^ 2 - α - 1 / 2)) * (a - (1 - 2 * α ^ 2)) := by
  have h : 8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1 -
    8 * (a - α) * (a - (2 * α ^ 2 - α - 1 / 2)) * (a - (1 - 2 * α ^ 2)) = 0 := by
    have key : 8 * a ^ 3 - 4 * a ^ 2 - 4 * a + 1 -
      8 * (a - α) * (a - (2 * α ^ 2 - α - 1 / 2)) * (a - (1 - 2 * α ^ 2)) =
      (4 * α * a - 4 * α ^ 2 + 1) * (8 * α ^ 3 - 4 * α ^ 2 - 4 * α + 1) := by
      field_simp; ring
    rw [key, hα, mul_zero]
  exact sub_eq_zero.mp h

/-- Every root of pCos7 in the splitting field is in ℚ(α). -/
private theorem rootSet_subset_adjoin :
    (pCos7.rootSet pCos7.SplittingField : Set pCos7.SplittingField) ⊆
    (IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField) :
      Set pCos7.SplittingField) := by
  intro r hr
  have hr_aeval : Polynomial.aeval r pCos7 = 0 := (Polynomial.mem_rootSet.mp hr).2
  have hr_root : 8 * r ^ 3 - 4 * r ^ 2 - 4 * r + 1 = 0 := by rwa [pCos7_eval_eq] at hr_aeval
  have hfact := factored_eval_eq root_in_sf r root_eq_zero
  rw [hr_root] at hfact
  have h8 : (8 : pCos7.SplittingField) ≠ 0 := by norm_num
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
    IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField) = ⊤ := by
  have hgen : Algebra.adjoin ℚ (pCos7.rootSet pCos7.SplittingField : Set pCos7.SplittingField) = ⊤ :=
    Polynomial.SplittingField.adjoin_rootSet (K := ℚ) (f := pCos7)
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField)
  have hsub := rootSet_subset_adjoin
  have halg : Algebra.adjoin ℚ (pCos7.rootSet pCos7.SplittingField : Set pCos7.SplittingField) ≤
    S.toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    exact hsub hx
  rw [eq_top_iff]
  intro x _
  have hx_alg : x ∈ S.toSubalgebra := halg (hgen ▸ Algebra.mem_top)
  exact hx_alg

/-- Module.finrank ℚ pCos7.SplittingField = 3. -/
theorem splitting_finrank :
    Module.finrank ℚ pCos7.SplittingField = 3 := by
  have htop := adjoin_root_eq_top
  have h_top_eq : Module.finrank ℚ
    (↥(IntermediateField.adjoin ℚ ({root_in_sf} : Set pCos7.SplittingField))) =
    Module.finrank ℚ pCos7.SplittingField := by
    rw [htop]
    exact LinearEquiv.finrank_eq IntermediateField.topEquiv.toLinearEquiv
  rw [← h_top_eq, adjoin_finrank]

/-
## Part VI: Main Theorem
-/

/-- |Gal(8X³-4X²-4X+1/ℚ)| = 3.

    The Galois group of the minimal polynomial of cos(π/7) over ℚ has order 3.
    This extends AngleTrisectionCos20Gal (which proved the same for cos(20°) = cos(π/9))
    to the 7-fold symmetry case. -/
theorem cos_pi_7_gal_card :
    Fintype.card (8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1 : ℚ[X]).Gal = 3 := by
  have hcard := Polynomial.Gal.card_of_separable pCos7_separable
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard, splitting_finrank]

/-- The polynomial 8X³-4X²-4X+1 is irreducible over ℚ (public interface). -/
theorem cos_pi_7_poly_irreducible :
    Irreducible (8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1 : ℚ[X]) :=
  pCos7_irreducible

end AngleTrisectionCos20GalOQ01
