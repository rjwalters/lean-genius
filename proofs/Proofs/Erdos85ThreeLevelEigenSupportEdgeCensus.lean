import Proofs.Erdos85ThreeLevelEigenSupportIncidenceBalance
import Proofs.Erdos85BinarySquareSizeTwoNegativeSupportProfiles

/-! # Edge census of the extreme fibres -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The sum of the internal neighbour counts of a finite vertex set is twice
the number of edges in the induced graph. -/
theorem sum_internalNeighbor_card_eq_twice_induced_edges
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (∑ u ∈ S, ((G.neighborFinset u).filter fun y ↦ y ∈ S).card) =
      2 * (G.induce (↑S : Set V)).edgeFinset.card := by
  classical
  let H := G.induce (↑S : Set V)
  have hsum :
      (∑ u ∈ S, ((G.neighborFinset u).filter fun y ↦ y ∈ S).card) =
        ∑ x : (↑S : Set V), H.degree x := by
    rw [Finset.sum_subtype S (fun _ ↦ Iff.rfl)]
    apply Finset.sum_congr rfl
    intro x _hx
    have hdegree : H.degree x =
        (G.neighborFinset x.1 ∩ S).card := by
      change (G.induce (↑S : Set V)).degree x = _
      rw [← (G.induce (↑S : Set V)).card_neighborFinset_eq_degree]
      apply Finset.card_bij (fun y _ ↦ y.1)
      · intro y hy
        have hxy : G.Adj x.1 y.1 :=
          ((G.induce (↑S : Set V)).mem_neighborFinset x y).mp hy
        exact Finset.mem_inter.mpr ⟨
          (G.mem_neighborFinset x.1 y.1).mpr hxy,
          Finset.mem_coe.mp y.2⟩
      · intro y₁ _ y₂ _ heq
        exact Subtype.ext heq
      · intro y hy
        have hy' := Finset.mem_inter.mp hy
        refine ⟨⟨y, Finset.mem_coe.mpr hy'.2⟩, ?_, rfl⟩
        exact ((G.induce (↑S : Set V)).mem_neighborFinset _ _).mpr
          ((G.mem_neighborFinset x.1 y).mp hy'.1)
    rw [hdegree]
    congr 1
  rw [hsum]
  exact H.sum_degrees_eq_twice_card_edges

/-- Exact induced-edge census forced by the local `+2` same-sign degree
imbalance.  The two extreme induced graphs have equally many edges, the
cross-incidence count is even, and each internal edge count is the support
size plus half the cross count. -/
theorem extreme_support_edgeCensus_of_degreeBalance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Sp Sm : Finset V) (hbal : Sp.card = Sm.card)
    (hp : ∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2)
    (hm : ∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) :
    let cross := ∑ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
    let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
    let em := (G.induce (↑Sm : Set V)).edgeFinset.card
    Even cross ∧ ep = em ∧
      2 * ep = cross + 2 * Sp.card ∧
      2 * em = cross + 2 * Sm.card := by
  dsimp only
  let cross := ∑ u ∈ Sp,
    ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
  let cross' := ∑ u ∈ Sm,
    ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card
  let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
  let em := (G.induce (↑Sm : Set V)).edgeFinset.card
  have hpSum :
      (∑ u ∈ Sp,
          ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card) =
        cross + 2 * Sp.card := by
    calc
      _ = ∑ u ∈ Sp,
          (((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hp u hu
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp [cross, mul_comm]
  have hmSum :
      (∑ u ∈ Sm,
          ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card) =
        cross' + 2 * Sm.card := by
    calc
      _ = ∑ u ∈ Sm,
          (((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact hm u hu
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp [cross', mul_comm]
  have hcross : cross = cross' := by
    have hcrossZ :=
      (extreme_support_incidenceBalance_of_degreeBalance G Sp Sm hp hm).2.2
    change (∑ u ∈ Sp,
      (((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card : ℤ)) =
        ∑ u ∈ Sm,
          (((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card : ℤ) at hcrossZ
    exact_mod_cast hcrossZ
  have hpEdges : 2 * ep = cross + 2 * Sp.card := by
    rw [← hpSum]
    exact (sum_internalNeighbor_card_eq_twice_induced_edges G Sp).symm
  have hmEdges : 2 * em = cross + 2 * Sm.card := by
    rw [hcross, ← hmSum]
    exact (sum_internalNeighbor_card_eq_twice_induced_edges G Sm).symm
  have heq : ep = em := by omega
  have hcrossEven : Even cross := by
    refine ⟨ep - Sp.card, ?_⟩
    omega
  exact ⟨hcrossEven, heq, hpEdges, hmEdges⟩

/-- Campaign-facing edge census from the standard local signed joint-line
interface. -/
theorem orderSixtyFour_sizeTwo_signedJoint_extreme_edgeCensus_of_local
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
    let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
    let Sp := Finset.univ.filter fun x ↦ w x = 2
    let Sm := Finset.univ.filter fun x ↦ w x = -2
    let cross := ∑ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card
    let ep := (G.induce (↑Sp : Set V)).edgeFinset.card
    let em := (G.induce (↑Sm : Set V)).edgeFinset.card
    Even cross ∧ ep = em ∧
      2 * ep = cross + 2 * Sp.card ∧
      2 * em = cross + 2 * Sm.card := by
  dsimp only
  let w := fun x ↦ (G.adjMatrix ℤ).mulVec s x + 2 * s x
  let Sp := Finset.univ.filter fun x ↦ w x = 2
  let Sm := Finset.univ.filter fun x ↦ w x = -2
  have hprofile := orderSixtyFour_sizeTwo_signedJoint_supportProfile_of_local
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  change Sp.card = Sm.card ∧ _ at hprofile
  have hdeg := orderSixtyFour_sizeTwo_signedJoint_extreme_degreeBalance_of_local
    G hfree hreg hcard c hc s mu hs_out hs_in hH hD
  change (∀ u ∈ Sp,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card + 2) ∧
    (∀ u ∈ Sm,
      ((G.neighborFinset u).filter fun y ↦ y ∈ Sm).card =
        ((G.neighborFinset u).filter fun y ↦ y ∈ Sp).card + 2) at hdeg
  exact extreme_support_edgeCensus_of_degreeBalance
    G Sp Sm hprofile.1 hdeg.1 hdeg.2

#print axioms Erdos85.extreme_support_edgeCensus_of_degreeBalance
#print axioms Erdos85.orderSixtyFour_sizeTwo_signedJoint_extreme_edgeCensus_of_local

end

end Erdos85
