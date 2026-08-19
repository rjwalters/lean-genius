import Proofs.Erdos85SizeTwoMuNegThreeSixTenCrossDefectCensus

/-! # Long-column cross-defect census in the `mu=-3` six-plus-ten stratum -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Swapping the two endpoints preserves the number of cross incidences cut out
by a symmetric predicate. -/
theorem sigma_cross_symmetric_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (K : SimpleGraph X) [DecidableRel K.Adj]
    (A B : Finset X) (P : X → X → Prop) [DecidableRel P]
    (hP : ∀ x y, P x y ↔ P y x) :
    (A.sigma fun x ↦ B.filter fun y ↦ K.Adj x y ∧ P x y).card =
      (B.sigma fun y ↦ A.filter fun x ↦ K.Adj y x ∧ P y x).card := by
  apply Finset.card_bij (fun p _ ↦ ⟨p.2, p.1⟩)
  · intro p hp
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp ⊢
    exact ⟨hp.2.1, hp.1, hp.2.2.1.symm, (hP _ _).mp hp.2.2.2⟩
  · intro p₁ hp₁ p₂ hp₂ heq
    cases p₁
    cases p₂
    simp_all
  · intro p hp
    refine ⟨⟨p.2, p.1⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_filter] at hp ⊢
    exact ⟨hp.2.1, hp.1, hp.2.2.1.symm, (hP _ _).mpr hp.2.2.2⟩

set_option maxHeartbeats 400000 in
/-- The signed `D`-incidence census is orientation-free: viewed from the
ten-point complement of the short cycle, its columns contain twelve same-sign
and eighteen opposite-sign incidences. -/
theorem orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_census
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
    [DecidableEq (G.induce c.supp).ConnectedComponent]
    (hc : c.supp.ncard = 8 * 2)
    (s : V → ℤ)
    (hs_out : ∀ x, x ∉ c.supp → s x = 0)
    (hs_in : ∀ x, x ∈ c.supp → s x = -1 ∨ s x = 1)
    (hH : ∀ z ∈ c.supp, ∑ y ∈ (G.neighborFinset z).filter
      (fun y ↦ (secondOrderDefectGraph G).connectedComponentMk y = c),
        s y = -2 * s z)
    (hD : ∀ z, z ∈ c.supp →
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z,
        s y = (-3 : ℤ) * s z)
    (a b : (G.induce c.supp).ConnectedComponent)
    (ha : a.supp.ncard = 6) (hb : b.supp.ncard = 10) :
    let K := (secondOrderDefectGraph G).induce c.supp
    let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
    let L := (Finset.univ : Finset c.supp).filter fun y ↦ y ∉ a.supp
    let Csame := L.sigma fun y ↦
      A.filter fun x ↦ K.Adj y x ∧ s y.1 = s x.1
    let Copp := L.sigma fun y ↦
      A.filter fun x ↦ K.Adj y x ∧ s x.1 = -s y.1
    Csame.card = 12 ∧ Copp.card = 18 := by
  classical
  dsimp only
  let K := (secondOrderDefectGraph G).induce c.supp
  let A := (Finset.univ : Finset c.supp).filter fun x ↦ x ∈ a.supp
  let L := (Finset.univ : Finset c.supp).filter fun y ↦ y ∉ a.supp
  let Csame := L.sigma fun y ↦
    A.filter fun x ↦ K.Adj y x ∧ s y.1 = s x.1
  let Copp := L.sigma fun y ↦
    A.filter fun x ↦ K.Adj y x ∧ s x.1 = -s y.1
  have hcensus := orderSixtyFour_sizeTwo_muNegThree_sixTen_crossDefect_census
    G hfree hreg hcard c hc s hs_out hs_in hH hD a b ha hb
  have hsameSwap := sigma_cross_symmetric_card K A L
    (fun x y ↦ s x.1 = s y.1) (by simp [eq_comm])
  have hoppSwap := sigma_cross_symmetric_card K A L
    (fun x y ↦ s y.1 = -s x.1) (by
      intro x y
      constructor <;> intro h <;> omega)
  have hsameDirect :
      (A.sigma fun x ↦ L.filter fun y ↦ K.Adj x y ∧ s x.1 = s y.1).card = 12 := by
    rw [← hcensus.1]
    congr 1
    ext p
    simp [A, L, K, SimpleGraph.mem_neighborFinset, eq_comm,
      and_assoc, and_left_comm, and_comm]
  have hoppDirect :
      (A.sigma fun x ↦ L.filter fun y ↦ K.Adj x y ∧ s y.1 = -s x.1).card = 18 := by
    rw [← hcensus.2.1]
    congr 1
    ext p
    simp [A, L, K, SimpleGraph.mem_neighborFinset,
      and_assoc, and_left_comm, and_comm]
  constructor
  · rw [← hsameDirect]
    simpa only [Csame] using hsameSwap.symm
  · rw [← hoppDirect]
    simpa only [Copp] using hoppSwap.symm

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_sizeTwo_muNegThree_sixTen_crossColumn_census
