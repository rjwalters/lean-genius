import Proofs.Erdos85SizeTwoSignedJointNegativeReduction
import Proofs.Erdos85BinarySquareBipartiteDefectComponentStrataConsumers
import Proofs.Erdos85OrderSixtyFourSevenComponent
import Proofs.Erdos85ComponentLocalObstruction

/-! # Excluding the extreme negative size-two mode at order 64 -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

private theorem int_eq_lower_of_extreme_sum
    {W : Type*} [DecidableEq W] (T : Finset W) (f : W → ℤ) (b : ℤ)
    (hbound : ∀ z ∈ T, b ≤ f z)
    (hsum : ∑ z ∈ T, f z = (T.card : ℤ) * b)
    {y : W} (hy : y ∈ T) : f y = b := by
  apply le_antisymm
  · by_contra hnot
    have hylt : b < f y := lt_of_not_ge hnot
    have hlt : ∑ _z ∈ T, b < ∑ z ∈ T, f z := by
      apply Finset.sum_lt_sum hbound
      exact ⟨y, hy, hylt⟩
    rw [Finset.sum_const, hsum] at hlt
    simp at hlt
  · exact hbound y hy

private theorem int_eq_upper_of_extreme_sum
    {W : Type*} [DecidableEq W] (T : Finset W) (f : W → ℤ) (b : ℤ)
    (hbound : ∀ z ∈ T, f z ≤ b)
    (hsum : ∑ z ∈ T, f z = (T.card : ℤ) * b)
    {y : W} (hy : y ∈ T) : f y = b := by
  apply le_antisymm (hbound y hy)
  by_contra hnot
  have hylt : f y < b := lt_of_not_ge hnot
  have hlt : ∑ z ∈ T, f z < ∑ _z ∈ T, b := by
    apply Finset.sum_lt_sum hbound
    exact ⟨y, hy, hylt⟩
  rw [Finset.sum_const, hsum] at hlt
  simp at hlt

/-- An eight-vertex seven-regular graph admits no proper two-coloring. -/
private theorem sevenRegular_eightVertex_no_boolColor
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (hcard : Fintype.card W = 8) (hreg : ∀ x, H.degree x = 7)
    (col : W → Bool) (hcol : ∀ x y, H.Adj x y → col x ≠ col y) : False := by
  have hinj : Function.Injective col := by
    intro x y hxy
    by_contra hne
    have hsub : H.neighborFinset x ⊆ Finset.univ.erase x := by
      intro z hz
      have hxz := (H.mem_neighborFinset x z).mp hz
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      exact (H.ne_of_adj hxz).symm
    have hneighborCard : (H.neighborFinset x).card = 7 := by
      rw [H.card_neighborFinset_eq_degree, hreg]
    have heraseCard : (Finset.univ.erase x).card = 7 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
    have heq : H.neighborFinset x = Finset.univ.erase x :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hy : y ∈ H.neighborFinset x := by
      rw [heq]
      exact Finset.mem_erase.mpr ⟨fun hyx => hne hyx.symm, Finset.mem_univ y⟩
    exact hcol x y ((H.mem_neighborFinset x y).mp hy) hxy
  have := Fintype.card_le_of_injective col hinj
  simp only [Fintype.card_bool, hcard] at this
  omega

/-- In the seven-component order-64 stratum, the extreme signed size-two
defect eigenvalue `-7` is impossible.  It makes the unique size-16 component
bipartite, while every fellow size-8 component is necessarily complete and
hence non-bipartite; the nonsquare residue obstruction then applies. -/
theorem orderSixtyFour_sevenComponents_sizeTwo_muNegSeven_false
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (s : Fin 64 → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = -7 * s z) : False := by
  let D := secondOrderDefectGraph G
  have hcard : Fintype.card (Fin 64) = 8 * 8 := by norm_num
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c (by simpa using hc) s (-7) hs_out hs_in hH
      (by intro z hz; simpa using hD z hz)
  have hclosed : ∀ x y, x ∈ c.supp → D.Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [ConnectedComponent.mem_supp_iff c] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  have hflip : ∀ x y, x ∈ c.supp → D.Adj x y → s y = -s x := by
    intro x y hx hxy
    have hy := hclosed x y hx hxy
    have hymem : y ∈ D.neighborFinset x := (D.mem_neighborFinset x y).mpr hxy
    have hTcard : (D.neighborFinset x).card = 7 := by
      rw [D.card_neighborFinset_eq_degree, P.defectDegree]
    rcases hs_in x hx with hsx | hsx
    · have hbound : ∀ z ∈ D.neighborFinset x, s z ≤ (1 : ℤ) := by
        intro z hz
        have hzc := hclosed x z hx ((D.mem_neighborFinset x z).mp hz)
        rcases hs_in z hzc with h | h <;> omega
      rw [hsx]
      apply int_eq_upper_of_extreme_sum (D.neighborFinset x) s 1 hbound _ hymem
      rw [hD x hx, hsx, hTcard]
      norm_num
    · have hbound : ∀ z ∈ D.neighborFinset x, (-1 : ℤ) ≤ s z := by
        intro z hz
        have hzc := hclosed x z hx ((D.mem_neighborFinset x z).mp hz)
        rcases hs_in z hzc with h | h <;> omega
      rw [hsx]
      apply int_eq_lower_of_extreme_sum (D.neighborFinset x) s (-1) hbound _ hymem
      rw [hD x hx, hsx, hTcard]
      norm_num
  let col : Fin 64 → Bool := fun x => decide (s x = 1)
  have hbip : ∀ x y, x ∈ c.supp → y ∈ c.supp →
      D.Adj x y → col x ≠ col y := by
    intro x y hx hy hxy
    have hsy := hflip x y hx hxy
    rcases hs_in x hx with hsx | hsx <;>
      rcases hs_in y hy with hsy' | hsy' <;>
      simp [col, hsx, hsy'] at hsy ⊢
  obtain ⟨base, hbase, hsmall⟩ := orderSixtyFour_seven_defect_components_partition
    G hfree (fun x => by rw [hreg]) (fun {_ _} _ => Or.inl (hreg _)) hcount
  have hcb : c = base := by
    by_contra hne
    have := hsmall c hne
    omega
  apply binarySquare_regular_bipartite_defectComponent_false_of_others_not_bipartite
    G hfree (q := 8) (by norm_num) hreg hcard
      (fun t => by exact fourteen_not_square t) c (m := 2) (by simpa using hc)
      col hbip
  intro c₁ hc₁ col₁ hcol₁
  have hc₁card : c₁.supp.ncard = 8 := by
    apply hsmall c₁
    intro hc₁base
    exact hc₁ (hc₁base.trans hcb.symm)
  let K := D.induce c₁.supp
  apply sevenRegular_eightVertex_no_boolColor K
    (by
      calc
        Fintype.card c₁.supp = c₁.supp.ncard := by
          simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c₁.supp
        _ = 8 := hc₁card)
    (fun x => by rw [degree_induce_connectedComponent_supp, P.defectDegree])
    (fun x => col₁ x.1)
  intro x y hxy
  exact hcol₁ x.1 y.1 x.2 y.2 hxy

/-- Complete signed-mode dispatcher for the seven-component stratum.  The
positive modes and `-7` are internal; only `-5,-3,-1` remain as callbacks. -/
theorem orderSixtyFour_sevenComponents_sizeTwo_signedJoint_false_of_three_negative_cases
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16)
    (s : Fin 64 → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z)
    (x : Fin 64) (hx : x ∈ c.supp)
    (hnegFive : mu = -5 → False)
    (hnegThree : mu = -3 → False)
    (hnegOne : mu = -1 → False) : False := by
  apply orderSixtyFour_sizeTwo_signedJoint_false_of_negative_cases
    G hfree hreg (by norm_num) c (by simpa using hc) s mu hs_out hs_in
      hH hD x hx
  · intro hmu
    subst mu
    exact orderSixtyFour_sevenComponents_sizeTwo_muNegSeven_false
      G hfree hreg hcount c hc s hs_out hs_in hH (by
        intro z hz
        simpa using hD z hz)
  · exact hnegFive
  · exact hnegThree
  · exact hnegOne

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sevenComponents_sizeTwo_muNegSeven_false
#print axioms Erdos85.orderSixtyFour_sevenComponents_sizeTwo_signedJoint_false_of_three_negative_cases
