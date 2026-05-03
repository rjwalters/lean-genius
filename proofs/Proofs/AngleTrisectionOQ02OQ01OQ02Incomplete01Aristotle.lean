/-
Aristotle companion for AngleTrisectionOQ02OQ01OQ02Incomplete01.lean
Problem: angle-trisection-oq-02-oq-01-oq-02-incomplete-01

Two target lemmas:

1. `finrank_adjoin_β_over_adjoin_a_dvd_two` (Session 32):
   Goal: Module.finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ ∣ 2
   Context: β : ℂ algebraic over ℚ, β² = a, ℚ⟮a⟯ ≤ ℚ⟮β⟯.
   Proof plan: β satisfies X²-a over ↥ℚ⟮a⟯, minpoly degree ≤ 2, finrank ≥ 1, hence divides 2.

2. `adjoin_β_in_sup_eq_top` (Session 33):
   Goal: IntermediateField.adjoin ↥K_a {β_in_Kaβ} = ⊤
   Context: K_a K_aβ : IntermediateField ℚ ℂ, K_aβ = K_a ⊔ ℚ⟮β⟯, β_in_Kaβ : ↥K_aβ
   Proof plan: K_aβ = K_a(β), so β generates K_aβ over K_a.
   Strategy: restrictScalars_injective + restrict (K_a image in ↥K_aβ) + lift_injective.
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

open Polynomial IntermediateField

namespace AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle

/-- Key lemma: if β is algebraic over ℚ and β² = a, then
    the degree [ℚ⟮β⟯:ℚ⟮a⟯] divides 2.

    Equivalent to: the extension ℚ⟮a⟯ ≤ ℚ⟮β⟯ has degree 1 or 2,
    which holds because β satisfies the quadratic X² - a over ℚ⟮a⟯. -/
theorem finrank_adjoin_β_over_adjoin_a_dvd_two
    (β a : ℂ)
    (halg_β : IsAlgebraic ℚ β)
    (hβ2 : β * β = a)
    (ha_le_β : (ℚ⟮a⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮β⟯)
    [hAlg : Algebra ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)]
    [hST : IsScalarTower ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)] :
    Module.finrank ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) ∣ 2 := by
  sorry

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
