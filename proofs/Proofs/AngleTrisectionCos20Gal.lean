/-
  Angle Trisection - Galois Group of cos(20°) Minimal Polynomial

  Proves: |Gal(8X³-6X-1/ℚ)| = 3

  This eliminates the `cos20_gal_order` axiom from AngleTrisectionOQ02.lean.

  Strategy:
  The polynomial p = 8X³-6X-1 is the minimal polynomial of cos(20°).
  Key insight: if α is a root, then β = 2α²-α-1 and γ = 1-2α² are also roots.
  (These correspond to cos(100°) and cos(220°) via the triple-angle formula.)
  Since all roots lie in ℚ(α), the splitting field equals ℚ(α), so
  [SplittingField:ℚ] = [ℚ(α):ℚ] = 3, giving |Gal| = 3.

  The algebraic identities are:
  8(2a²-a-1)³ - 6(2a²-a-1) - 1 = (8a³-12a²+3)(8a³-6a-1)
  8(1-2a²)³ - 6(1-2a²) - 1 = (-8a³+6a-1)(8a³-6a-1)
  Both vanish when 8a³-6a-1 = 0.

  References:
  - Wantzel, P.L. (1837): Impossible ruler-compass constructions
  - cos(20°), cos(100°), cos(220°) are the three roots of 8x³-6x-1
    (from 3θ = 60°, 300°, 660° → θ = 20°, 100°, 220°)
-/

import Mathlib

open Polynomial IntermediateField FiniteDimensional

namespace AngleTrisectionCos20Gal

/-
## Part I: Key Algebraic Identities

These are pure ring identities, verifiable by `ring`.
They express that if α is a root, then 2α²-α-1 and 1-2α² are also roots.
-/

/-- If 8a³-6a-1 = 0 in any commutative ring, then 2a²-a-1 is also a root. -/
theorem root_image_beta {R : Type*} [CommRing R] (a : R)
    (ha : 8 * a ^ 3 - 6 * a - 1 = 0) :
    8 * (2 * a ^ 2 - a - 1) ^ 3 - 6 * (2 * a ^ 2 - a - 1) - 1 = 0 := by
  have key : 8 * (2 * a ^ 2 - a - 1) ^ 3 - 6 * (2 * a ^ 2 - a - 1) - 1 =
    (8 * a ^ 3 - 12 * a ^ 2 + 3) * (8 * a ^ 3 - 6 * a - 1) := by ring
  rw [key, ha, mul_zero]

/-- If 8a³-6a-1 = 0 in any commutative ring, then 1-2a² is also a root. -/
theorem root_image_gamma {R : Type*} [CommRing R] (a : R)
    (ha : 8 * a ^ 3 - 6 * a - 1 = 0) :
    8 * (1 - 2 * a ^ 2) ^ 3 - 6 * (1 - 2 * a ^ 2) - 1 = 0 := by
  have key : 8 * (1 - 2 * a ^ 2) ^ 3 - 6 * (1 - 2 * a ^ 2) - 1 =
    (-8 * a ^ 3 + 6 * a - 1) * (8 * a ^ 3 - 6 * a - 1) := by ring
  rw [key, ha, mul_zero]

/-- The quadratic cofactor of p after dividing by (X-α) has β = 2α²-α-1 as a root.
    This identity shows: 8β² + 8αβ + (8α²-6) = (4α-2)(8α³-6α-1). -/
theorem quadratic_cofactor_root {R : Type*} [CommRing R] (a : R)
    (ha : 8 * a ^ 3 - 6 * a - 1 = 0) :
    8 * (2 * a ^ 2 - a - 1) ^ 2 + 8 * a * (2 * a ^ 2 - a - 1) + (8 * a ^ 2 - 6) = 0 := by
  have key : 8 * (2 * a ^ 2 - a - 1) ^ 2 + 8 * a * (2 * a ^ 2 - a - 1) + (8 * a ^ 2 - 6) =
    (4 * a - 2) * (8 * a ^ 3 - 6 * a - 1) := by ring
  rw [key, ha, mul_zero]

/-
## Part II: Polynomial Properties
-/

/-- Shorthand for the polynomial 8X³-6X-1. -/
private noncomputable abbrev p : ℚ[X] := 8 * X ^ 3 - 6 * X - C 1

private theorem p_ne_zero : (p : ℚ[X]) ≠ 0 := by
  intro h
  have : Polynomial.eval 0 (p : ℚ[X]) = -1 := by
    simp [p]
  rw [h, Polynomial.eval_zero] at this
  norm_num at this

private theorem p_natDegree : (p : ℚ[X]).natDegree = 3 := by
  show (8 * X ^ 3 - 6 * X - C (1 : ℚ)).natDegree = 3
  norm_num [natDegree_sub_eq_left_of_natDegree_lt, natDegree_mul, natDegree_pow,
    natDegree_X, natDegree_C, natDegree_one]

private theorem p_degree_ne_zero : (p : ℚ[X]).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree p_ne_zero, p_natDegree]
  exact (by norm_num : (3 : WithBot ℕ) ≠ 0)

/-
## Part II-B: Irreducibility of p via Eisenstein Criterion

Strategy: The polynomial q = X³-6X²+9X-3 is Eisenstein at p=3, hence irreducible
over ℤ and ℚ. The linear substitution Y = 2X+2 gives q(2X+2) = 8X³-6X-1 = p.
Since irreducibility is preserved under invertible linear substitutions, p is irreducible.
-/

/-- The Eisenstein polynomial: q = X³ - 6X² + 9X - 3 over ℤ. -/
private noncomputable def q_eis_int : ℤ[X] := X ^ 3 - C 6 * X ^ 2 + C 9 * X - C 3

private theorem q_eis_int_natDegree : q_eis_int.natDegree = 3 := by
  unfold q_eis_int; compute_degree!

private theorem q_eis_int_degree : q_eis_int.degree = 3 := by
  unfold q_eis_int; compute_degree!

private theorem q_eis_int_monic : q_eis_int.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, q_eis_int_natDegree]
  unfold q_eis_int
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
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
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · -- 0 < degree
    rw [q_eis_int_degree]; exact_mod_cast Nat.zero_lt_succ 2
  · -- coeff 0 ∉ (3)²
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold q_eis_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · -- isPrimitive (monic → primitive)
    exact q_eis_int_monic.isPrimitive

/-- The same polynomial over ℚ. -/
private noncomputable def q_eis_rat : ℚ[X] := X ^ 3 - C 6 * X ^ 2 + C 9 * X - C 3

/-- q is irreducible over ℚ (Gauss's lemma: monic + ℤ-irreducible → ℚ-irreducible). -/
private theorem q_eis_rat_irreducible : Irreducible q_eis_rat := by
  have hprim := q_eis_int_monic.isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp q_eis_int_irreducible
  have heq : q_eis_rat = Polynomial.map (Int.castRingHom ℚ) q_eis_int := by
    unfold q_eis_rat q_eis_int
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_pow]
    norm_num
  rwa [heq]

/-- Key identity: q(2X+2) = p, i.e., the linear substitution Y=2X+2 transforms q into p.
    Verified by expanding: (2X+2)³-6(2X+2)²+9(2X+2)-3 = 8X³-6X-1. -/
private theorem q_comp_eq_p :
    q_eis_rat.comp (C 2 * X + C 2) = p := by
  apply Polynomial.funext; intro x
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  unfold q_eis_rat p
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  ring

/-- 8X³-6X-1 is irreducible over ℚ.

    Proof: The shifted polynomial q = X³-6X²+9X-3 is Eisenstein at p=3,
    so q is irreducible over ℚ by Gauss's lemma. Since p = q(2X+2)
    and the substitution X ↦ 2X+2 is invertible (inverse: X ↦ X/2-1),
    irreducibility transfers from q to p. -/
private theorem p_irreducible : Irreducible (p : ℚ[X]) := by
  -- p = q.comp ℓ where ℓ = 2X+2 is invertible (inverse ℓ⁻¹ = X/2 - 1)
  rw [← q_comp_eq_p]
  -- Prove irreducibility of q.comp ℓ from irreducibility of q
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · -- q.comp ℓ is not a unit (has degree 3)
    intro h
    have hd := Polynomial.natDegree_eq_zero_of_isUnit h
    have : (q_eis_rat.comp (C 2 * X + C 2)).natDegree = 3 := by
      rw [q_comp_eq_p]; exact p_natDegree
    omega
  · -- if q.comp ℓ = a * b, then one is a unit
    intro a b hab
    -- Define the inverse substitution ℓ⁻¹ = (1/2)X - 1
    set ℓ := (C (2 : ℚ) * X + C 2 : ℚ[X])
    set ℓ_inv := (C (2⁻¹ : ℚ) * X - C 1 : ℚ[X])
    -- Key: composing both sides of hab with ℓ⁻¹ gives a factoring of q
    have hq_factor : q_eis_rat = (a.comp ℓ_inv) * (b.comp ℓ_inv) := by
      have h1 : ℓ.comp ℓ_inv = X := by
        ext n
        simp only [ℓ, ℓ_inv, Polynomial.add_comp,
          Polynomial.mul_comp, Polynomial.C_comp, Polynomial.X_comp]
        simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X, coeff_C]
        rcases n with _ | _ | _ <;> simp <;> ring
      calc q_eis_rat
          = q_eis_rat.comp X := q_eis_rat.comp_X.symm
        _ = q_eis_rat.comp (ℓ.comp ℓ_inv) := by rw [h1]
        _ = (q_eis_rat.comp ℓ).comp ℓ_inv := (q_eis_rat.comp_assoc ℓ ℓ_inv).symm
        _ = (a * b).comp ℓ_inv := by rw [hab]
        _ = (a.comp ℓ_inv) * (b.comp ℓ_inv) := Polynomial.mul_comp a b ℓ_inv
    -- Since q is irreducible, one factor is a unit
    rcases q_eis_rat_irreducible.isUnit_or_isUnit hq_factor with ha | hb
    · -- a.comp ℓ⁻¹ is a unit → a is a unit
      left
      -- A unit in k[X] is a nonzero constant C c
      rw [Polynomial.isUnit_iff] at ha
      obtain ⟨c, hc_ne, hc_eq⟩ := ha
      -- a = (a.comp ℓ⁻¹).comp ℓ = (C c).comp ℓ = C c
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
    · -- b.comp ℓ⁻¹ is a unit → b is a unit (symmetric)
      right
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

private theorem p_separable : (p : ℚ[X]).Separable :=
  p_irreducible.separable

/-
## Part III: Splitting Field Analysis

The key theorem: all roots of p lie in ℚ(α) for any root α.
This means the splitting field equals ℚ(α), so [SplittingField:ℚ] = 3.
-/

/-- Evaluation of p at an element equals 8a³-6a-1. -/
private theorem p_eval_eq {R : Type*} [CommRing R] [Algebra ℚ R] (a : R) :
    Polynomial.aeval a p = 8 * a ^ 3 - 6 * a - 1 := by
  simp [p, map_sub, map_mul, map_pow, map_ofNat, Polynomial.aeval_X]

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

/-- The root satisfies 8α³-6α-1 = 0. -/
private theorem root_eq_zero :
    8 * root_in_sf ^ 3 - 6 * root_in_sf - 1 = 0 := by
  have := root_is_root
  rwa [p_eval_eq] at this

/-- β = 2α²-α-1 is a root of p in the splitting field. -/
private theorem beta_is_root :
    Polynomial.aeval (2 * root_in_sf ^ 2 - root_in_sf - 1) p = 0 := by
  rw [p_eval_eq]
  exact root_image_beta root_in_sf root_eq_zero

/-- γ = 1-2α² is a root of p in the splitting field. -/
private theorem gamma_is_root :
    Polynomial.aeval (1 - 2 * root_in_sf ^ 2) p = 0 := by
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

Key argument: all roots of p are polynomial expressions of α,
so the splitting field ℚ(α) has degree 3 over ℚ.
-/

/-- The root α is integral over ℚ. -/
private theorem root_integral : IsIntegral ℚ root_in_sf :=
  .of_finite ℚ root_in_sf

/-- The minpoly of α has natDegree 3 (since p is irreducible and α is a root). -/
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

/-- β = 2α²-α-1 is in ℚ(α) (polynomial expression in α). -/
private theorem beta_in_adjoin :
    (2 * root_in_sf ^ 2 - root_in_sf - 1 : p.SplittingField) ∈
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  have hα : root_in_sf ∈ S :=
    IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  have hαα : root_in_sf * root_in_sf ∈ S := S.mul_mem hα hα
  have h2αα : (2 : p.SplittingField) * (root_in_sf * root_in_sf) ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hαα
  show 2 * root_in_sf ^ 2 - root_in_sf - 1 ∈ S
  have heq : 2 * root_in_sf ^ 2 - root_in_sf - 1 =
    (2 : p.SplittingField) * (root_in_sf * root_in_sf) - root_in_sf - 1 := by ring
  rw [heq]
  exact S.sub_mem (S.sub_mem h2αα hα) S.one_mem

/-- γ = 1-2α² is in ℚ(α) (polynomial expression in α). -/
private theorem gamma_in_adjoin :
    (1 - 2 * root_in_sf ^ 2 : p.SplittingField) ∈
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) := by
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  have hα : root_in_sf ∈ S :=
    IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
  have hαα : root_in_sf * root_in_sf ∈ S := S.mul_mem hα hα
  have h2αα : (2 : p.SplittingField) * (root_in_sf * root_in_sf) ∈ S :=
    S.mul_mem (S.algebraMap_mem 2) hαα
  show 1 - 2 * root_in_sf ^ 2 ∈ S
  have heq : 1 - 2 * root_in_sf ^ 2 =
    1 - (2 : p.SplittingField) * (root_in_sf * root_in_sf) := by ring
  rw [heq]
  exact S.sub_mem S.one_mem h2αα

/-- Factored form: 8a³-6a-1 = 8(a-α)(a-β)(a-γ) when 8α³-6α-1 = 0.
    This identity holds in any commutative ring. -/
private theorem factored_eval_eq {R : Type*} [CommRing R] (α a : R)
    (hα : 8 * α ^ 3 - 6 * α - 1 = 0) :
    8 * a ^ 3 - 6 * a - 1 =
    8 * (a - α) * (a - (2 * α ^ 2 - α - 1)) * (a - (1 - 2 * α ^ 2)) := by
  have h : 8 * a ^ 3 - 6 * a - 1 -
    8 * (a - α) * (a - (2 * α ^ 2 - α - 1)) * (a - (1 - 2 * α ^ 2)) = 0 := by
    have key : 8 * a ^ 3 - 6 * a - 1 -
      8 * (a - α) * (a - (2 * α ^ 2 - α - 1)) * (a - (1 - 2 * α ^ 2)) =
      ((4 * α - 2) * a + (-4 * α ^ 2 + 2 * α + 1)) * (8 * α ^ 3 - 6 * α - 1) := by ring
    rw [key, hα, mul_zero]
  exact sub_eq_zero.mp h

/-- Every root of p in the splitting field is in ℚ(α).

    Proof: By the factored form, if 8r³-6r-1 = 0 and 8α³-6α-1 = 0, then
    8(r-α)(r-β)(r-γ) = 0. Since the splitting field is a domain and 8 ≠ 0,
    one of r = α, r = β, r = γ. All three are in ℚ(α). -/
private theorem rootSet_subset_adjoin :
    (p.rootSet p.SplittingField : Set p.SplittingField) ⊆
    (IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) :
      Set p.SplittingField) := by
  intro r hr
  -- r is a root of p
  have hr_aeval : Polynomial.aeval r p = 0 := (Polynomial.mem_rootSet.mp hr).2
  have hr_root : 8 * r ^ 3 - 6 * r - 1 = 0 := by rwa [p_eval_eq] at hr_aeval
  -- Factored form: 8r³-6r-1 = 8(r-α)(r-β)(r-γ)
  have hfact := factored_eval_eq root_in_sf r root_eq_zero
  -- Substituting hr_root: 0 = 8(r-α)(r-β)(r-γ)
  rw [hr_root] at hfact
  -- So ((8 * (r-α)) * (r-β)) * (r-γ) = 0
  have h8 : (8 : p.SplittingField) ≠ 0 := by norm_num
  -- hfact.symm : 8 * (r-α) * (r-β) * (r-γ) = 0
  -- Lean parses as: ((8 * (r-α)) * (r-β)) * (r-γ) = 0
  rcases mul_eq_zero.mp hfact.symm with h12 | h3
  · rcases mul_eq_zero.mp h12 with h8a | h2
    · -- 8 * (r - α) = 0, so r = α (since 8 ≠ 0)
      rw [sub_eq_zero.mp ((mul_eq_zero.mp h8a).resolve_left h8)]
      exact IntermediateField.mem_adjoin_simple_self ℚ root_in_sf
    · -- r = β = 2α²-α-1
      rw [sub_eq_zero.mp h2]
      exact beta_in_adjoin
  · -- r = γ = 1-2α²
    rw [sub_eq_zero.mp h3]
    exact gamma_in_adjoin

/-- The splitting field is generated by α alone.
    Proof: rootSet ⊂ ℚ(α), and adjoin(rootSet) = ⊤, so ℚ(α) = ⊤. -/
private theorem adjoin_root_eq_top :
    IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField) = ⊤ := by
  -- Algebra.adjoin ℚ (rootSet p SplittingField) = ⊤
  have hgen : Algebra.adjoin ℚ (p.rootSet p.SplittingField : Set p.SplittingField) = ⊤ :=
    Polynomial.SplittingField.adjoin_rootSet (K := ℚ) (f := p)
  set S := IntermediateField.adjoin ℚ ({root_in_sf} : Set p.SplittingField)
  -- rootSet ⊆ S (from rootSet_subset_adjoin)
  have hsub := rootSet_subset_adjoin
  -- Therefore Algebra.adjoin ℚ rootSet ≤ S.toSubalgebra
  have halg : Algebra.adjoin ℚ (p.rootSet p.SplittingField : Set p.SplittingField) ≤
    S.toSubalgebra := by
    apply Algebra.adjoin_le
    intro x hx
    exact hsub hx
  -- Since Algebra.adjoin rootSet = ⊤, we have S.toSubalgebra = ⊤
  rw [eq_top_iff]
  intro x _
  have hx_alg : x ∈ S.toSubalgebra := halg (hgen ▸ Algebra.mem_top)
  exact hx_alg

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

/-- |Gal(8X³-6X-1/ℚ)| = 3. -/
theorem cos20_gal_card :
    Fintype.card (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]).Gal = 3 := by
  have hcard := Polynomial.Gal.card_of_separable p_separable
  rw [Nat.card_eq_fintype_card] at hcard
  rw [hcard, splitting_finrank]

/-- The polynomial 8X³-6X-1 is irreducible over ℚ (public interface).
    Proved via Eisenstein's criterion on the shifted polynomial X³-6X²+9X-3. -/
theorem trisection_poly_irreducible :
    Irreducible (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]) :=
  p_irreducible

end AngleTrisectionCos20Gal
