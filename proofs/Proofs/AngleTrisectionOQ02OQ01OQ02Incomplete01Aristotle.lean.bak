/-
Aristotle companion for AngleTrisectionOQ02OQ01OQ02Incomplete01.lean
Problem: angle-trisection-oq-02-oq-01-oq-02-incomplete-01

Two target lemmas:

1. `finrank_adjoin_β_over_adjoin_a_dvd_two` (Session 32 — PROVED by Aristotle 2026-05-03):
   Goal: Module.finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ ∣ 2
   Context: β : ℂ algebraic over ℚ, β² = a, ℚ⟮a⟯ ≤ ℚ⟮β⟯.
   Proof: tower law + minpoly ℚ β ∣ (minpoly ℚ a).comp(X²) + interval_cases.

2. `adjoin_β_in_sup_eq_top` (Session 33-34):
   Goal: IntermediateField.adjoin ↥K_a {β_in_Kaβ} = ⊤
   Context: K_a K_aβ : IntermediateField ℚ ℂ, K_aβ = K_a ⊔ ℚ⟮β⟯, β_in_Kaβ : ↥K_aβ
   Proof plan: K_aβ = K_a(β), so β generates K_aβ over K_a.
   Strategy: restrictScalars_injective + restrict (K_a image in ↥K_aβ) + lift_injective.
-/

import Mathlib

open Polynomial IntermediateField

namespace AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle

-- Helper: a is algebraic over ℚ (since a = β² and β is algebraic)
private lemma a_isAlgebraic (β a : ℂ) (halg_β : IsAlgebraic ℚ β) (hβ2 : β * β = a) :
    IsAlgebraic ℚ a :=
  hβ2 ▸ IsAlgebraic.mul halg_β halg_β

/-
Helper: aeval β ((minpoly ℚ a).comp (X ^ 2)) = 0
-/
private lemma aeval_comp_eq_zero (β a : ℂ) (halg_β : IsAlgebraic ℚ β) (hβ2 : β * β = a) :
    Polynomial.aeval β ((minpoly ℚ a).comp (X ^ 2)) = 0 := by
  rw [ Polynomial.aeval_comp ];
  norm_num [ sq, hβ2 ]

/-
Helper: finrank ℚ ℚ⟮β⟯ ≤ 2 * finrank ℚ ℚ⟮a⟯
Proof: minpoly ℚ β divides (minpoly ℚ a).comp(X²), which has degree 2·deg(minpoly ℚ a).
finrank ℚ ℚ⟮β⟯ = natDegree(minpoly ℚ β) ≤ natDegree((minpoly ℚ a).comp(X²)) = 2·natDegree(minpoly ℚ a) = 2·finrank ℚ ℚ⟮a⟯
-/
private lemma finrank_β_le_two_mul_finrank_a (β a : ℂ)
    (halg_β : IsAlgebraic ℚ β) (hβ2 : β * β = a) :
    Module.finrank ℚ ↥(ℚ⟮β⟯) ≤ 2 * Module.finrank ℚ ↥(ℚ⟮a⟯) := by
  rw [ IntermediateField.adjoin.finrank, IntermediateField.adjoin.finrank ];
  · have h_deg : minpoly ℚ β ∣ (minpoly ℚ a).comp (X^2) := by
      refine' minpoly.dvd ℚ β _;
      convert aeval_comp_eq_zero β a halg_β hβ2 using 1;
    refine' le_trans ( Polynomial.natDegree_le_of_dvd h_deg _ ) _;
    · have := minpoly.ne_zero ( show IsIntegral ℚ a from ?_ );
      · simp_all +decide [ Polynomial.comp_eq_zero_iff ];
      · exact hβ2 ▸ halg_β.isIntegral.mul halg_β.isIntegral;
    · rw [ Polynomial.natDegree_comp, Polynomial.natDegree_X_pow, mul_comm ];
  · exact hβ2 ▸ halg_β.isIntegral.mul halg_β.isIntegral;
  · exact halg_β.isIntegral

/-- Key lemma: if β is algebraic over ℚ and β² = a, then
    the degree [ℚ⟮β⟯:ℚ⟮a⟯] divides 2.

    Proved by Aristotle (2026-05-03, job 594e3160).
    Proof: tower law + minpoly ℚ β ∣ (minpoly ℚ a).comp(X²) + interval_cases. -/
theorem finrank_adjoin_β_over_adjoin_a_dvd_two
    (β a : ℂ)
    (halg_β : IsAlgebraic ℚ β)
    (hβ2 : β * β = a)
    (ha_le_β : (ℚ⟮a⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮β⟯)
    [hAlg : Algebra ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)]
    [hST : IsScalarTower ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)] :
    Module.finrank ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) ∣ 2 := by
  -- By the tower law, the degree [ℚ⟮β⟯:ℚ] is equal to the product of the degrees [ℚ⟮β⟯:ℚ⟮a⟯] and [ℚ⟮a⟯:ℚ].
  have h_tower : Module.finrank ℚ ↥(ℚ⟮β⟯) = Module.finrank ℚ⟮a⟯ ↥(ℚ⟮β⟯) * Module.finrank ℚ ↥(ℚ⟮a⟯) := by
    rw [ mul_comm, Module.finrank_mul_finrank ];
  have h_deg_le : Module.finrank ℚ ↥(ℚ⟮β⟯) ≤ 2 * Module.finrank ℚ ↥(ℚ⟮a⟯) := by
    apply finrank_β_le_two_mul_finrank_a β a halg_β hβ2;
  have h_deg_pos : 0 < Module.finrank ℚ ↥(ℚ⟮a⟯) := by
    have h_deg_pos : IsAlgebraic ℚ a := by
      exact a_isAlgebraic β a halg_β hβ2;
    have := IntermediateField.adjoin.finrank h_deg_pos.isIntegral;
    exact this.symm ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr ( Polynomial.degree_pos_of_irreducible ( minpoly.irreducible h_deg_pos.isIntegral ) );
  have h_deg_le : Module.finrank ℚ⟮a⟯ ↥(ℚ⟮β⟯) ≤ 2 := by
    nlinarith;
  interval_cases _ : Module.finrank ℚ⟮a⟯ ↥ℚ⟮β⟯ <;> simp_all +decide;
  have h_deg_pos : 0 < Module.finrank ℚ ↥(ℚ⟮β⟯) := by
    have h_alg : IsIntegral ℚ β := by
      exact halg_β.isIntegral
    have := IntermediateField.adjoin.finrank h_alg;
    exact this.symm ▸ Polynomial.natDegree_pos_iff_degree_pos.mpr ( Polynomial.degree_pos_of_irreducible ( minpoly.irreducible h_alg ) );
  linarith

/-- β (as an element of K_aβ = K_a ⊔ ℚ⟮β⟯) generates K_aβ over K_a.

    Since K_aβ = K_a ⊔ ℚ⟮β⟯ = K_a(β), every element of K_aβ lies in the
    K_a-closure of β, so adjoin K_a {β_in_Kaβ} = ⊤.

    Proof uses:
    - restrictScalars_injective ℚ: reduce to goal over ℚ
    - K_a_im = K_a.restrict (K_a ≤ K_aβ): image of K_a inside ↥K_aβ as IntermediateField ℚ ↥K_aβ
    - restrict_algEquiv: AlgEquiv ↥K_a ≃ₐ[ℚ] ↥K_a_im
    - restrictScalars_adjoin_of_algEquiv: convert ↥K_a-adjoin to ↥K_a_im-adjoin
    - restrictScalars_adjoin K_a_im: get adjoin ℚ (↑K_a_im ∪ {β_in_Kaβ})
    - lift_injective K_aβ + lift_adjoin + lift_top: reduce to ℂ
    - adjoin ℚ (↑K_a ∪ {β}) = K_a ⊔ ℚ⟮β⟯ = K_aβ by sup_le and adjoin.mono -/
theorem adjoin_β_in_sup_eq_top
    (K_a : IntermediateField ℚ ℂ) (β : ℂ)
    (hβ_mem : β ∈ K_a ⊔ ℚ⟮β⟯)
    (β_in_Kaβ : ↥(K_a ⊔ (ℚ⟮β⟯ : IntermediateField ℚ ℂ)))
    (hβ_val : β_in_Kaβ.val = β) :
    haveI hAlg : Algebra ↥K_a ↥(K_a ⊔ (ℚ⟮β⟯ : IntermediateField ℚ ℂ)) :=
      (IntermediateField.inclusion (le_sup_left (b := ℚ⟮β⟯))).toAlgebra
    haveI hST : IsScalarTower ℚ ↥K_a ↥(K_a ⊔ (ℚ⟮β⟯ : IntermediateField ℚ ℂ)) :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    @IntermediateField.adjoin ℚ _ ℂ _ _ _
      ↥K_a _ _ ↥(K_a ⊔ (ℚ⟮β⟯ : IntermediateField ℚ ℂ)) _ _
      hAlg _ ({β_in_Kaβ} : Set _) = ⊤ := by
  simp only
  sorry

end AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle
