import Proofs.Erdos85BinarySquareSizeTwoSignedJointPackage

/-! # Defect-neighbour census at the extreme negative joint eigenvalue -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At defect eigenvalue `-5`, a positive vertex of the signed size-two
component has one positive and six negative defect neighbours.  A negative
vertex has the dual census. -/
theorem orderSixtyFour_sizeTwo_muNegFive_defectNeighborCensus_of_local
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = (-5 : ℤ) * s z) :
    ∀ x, x ∈ c.supp →
      (s x = 1 →
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = 1).card = 1 ∧
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = -1).card = 6) ∧
      (s x = -1 →
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = -1).card = 1 ∧
        (((secondOrderDefectGraph G).neighborFinset x).filter
          fun y ↦ s y = 1).card = 6) := by
  let D := secondOrderDefectGraph G
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s (-5) hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔ D.connectedComponentMk x = c :=
    fun x ↦ ConnectedComponent.mem_supp_iff c x
  have hclosed : ∀ x y, x ∈ c.supp → D.Adj x y → y ∈ c.supp := by
    intro x y hx hxy
    rw [hmem] at hx ⊢
    rw [← hx]
    exact (ConnectedComponent.connectedComponentMk_eq_of_adj hxy).symm
  intro x hx
  let T := D.neighborFinset x
  let Tp := T.filter fun y ↦ s y = 1
  let Tm := T.filter fun y ↦ s y = -1
  have hTcard : T.card = 7 := P.defectDegree x
  have hcover : T = Tp ∪ Tm := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Tp, Tm]
    constructor
    · intro hy
      have hyc := hclosed x y hx ((D.mem_neighborFinset x y).mp hy)
      rcases hs_in y hyc with hs | hs
      · exact Or.inr ⟨hy, hs⟩
      · exact Or.inl ⟨hy, hs⟩
    · rintro (hy | hy) <;> exact hy.1
  have hdisj : Disjoint Tp Tm := by
    rw [Finset.disjoint_left]
    intro y hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hcards : Tp.card + Tm.card = 7 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hcover, hTcard]
  have hsum : (Tp.card : ℤ) - Tm.card = -5 * s x := by
    have hact := hD x hx
    change ∑ y ∈ T, s y = -5 * s x at hact
    rw [hcover, Finset.sum_union hdisj] at hact
    have hp : ∑ y ∈ Tp, s y = (Tp.card : ℤ) := by
      calc
        _ = ∑ _y ∈ Tp, (1 : ℤ) := Finset.sum_congr rfl
          (fun y hy ↦ (Finset.mem_filter.mp hy).2)
        _ = _ := by simp
    have hm : ∑ y ∈ Tm, s y = -(Tm.card : ℤ) := by
      calc
        _ = ∑ _y ∈ Tm, (-1 : ℤ) := Finset.sum_congr rfl
          (fun y hy ↦ (Finset.mem_filter.mp hy).2)
        _ = _ := by simp
    rw [hp, hm] at hact
    exact hact
  constructor
  · intro hs
    change Tp.card = 1 ∧ Tm.card = 6
    rw [hs] at hsum
    omega
  · intro hs
    change Tm.card = 1 ∧ Tp.card = 6
    rw [hs] at hsum
    omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegFive_defectNeighborCensus_of_local
