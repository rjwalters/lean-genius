import Proofs.Erdos85BinarySquareSizeTwoSignedJointPackage

/-! # The internal ambient factor of a signed size-two component is bipartite -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two ambient neighbours inside a normalized signed size-two defect
component always have sign opposite to the row vertex.  This statement is
uniform in the defect eigenvalue. -/
theorem orderSixtyFour_sizeTwo_signedJoint_ambientNeighborCensus_of_local
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
    (s : V → ℤ) (mu : ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y = mu * s z) :
    ∀ x, x ∈ c.supp →
      let T := (G.neighborFinset x).filter
        (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c)
      (s x = 1 →
        (T.filter fun y ↦ s y = 1).card = 0 ∧
        (T.filter fun y ↦ s y = -1).card = 2) ∧
      (s x = -1 →
        (T.filter fun y ↦ s y = -1).card = 0 ∧
        (T.filter fun y ↦ s y = 1).card = 2) := by
  have P := orderSixtyFour_sizeTwo_signedJoint_derived
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  have hmem : ∀ x, x ∈ c.supp ↔
      (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun x ↦ ConnectedComponent.mem_supp_iff c x
  intro x hx
  dsimp only
  let T := (G.neighborFinset x).filter
    (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c)
  let Tp := T.filter fun y ↦ s y = 1
  let Tm := T.filter fun y ↦ s y = -1
  have hTcard : T.card = 2 := P.componentNeighborCard x
  have hsign : ∀ y ∈ T, s y = -1 ∨ s y = 1 := by
    intro y hy
    exact hs_in y ((hmem y).mpr (Finset.mem_filter.mp hy).2)
  have hcover : T = Tp ∪ Tm := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter, Tp, Tm]
    constructor
    · intro hy
      rcases hsign y hy with hs | hs
      · exact Or.inr ⟨hy, hs⟩
      · exact Or.inl ⟨hy, hs⟩
    · rintro (hy | hy) <;> exact hy.1
  have hdisj : Disjoint Tp Tm := by
    rw [Finset.disjoint_left]
    intro y hp hm
    have hp' := (Finset.mem_filter.mp hp).2
    have hm' := (Finset.mem_filter.mp hm).2
    omega
  have hcards : Tp.card + Tm.card = 2 := by
    rw [← Finset.card_union_of_disjoint hdisj, ← hcover, hTcard]
  have hsum : (Tp.card : ℤ) - Tm.card = -2 * s x := by
    have hact := hH x hx
    change ∑ y ∈ T, s y = -2 * s x at hact
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
    change Tp.card = 0 ∧ Tm.card = 2
    rw [hs] at hsum
    omega
  · intro hs
    change Tm.card = 0 ∧ Tp.card = 2
    rw [hs] at hsum
    omega

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_ambientNeighborCensus_of_local
