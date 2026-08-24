import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddTwoLowHoleRow

/-!
# Near-perfect owner-pair packing on a low-hole circuit row

The low-hole row has at most three singleton-owner points.  All its remaining
points have two-element, pairwise-disjoint owner sets, giving at least `m-3`
disjoint pairs of full centers.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- An endpoint `m+2` even configuration contains a row whose shore points
give at least `m-3` pairwise-disjoint two-owner blocks; its singleton points
and center holes have the same cardinality, at most three. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_ownerPairPacking
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let owner := fun y : V => G.neighborFinset y ∩ F
    let K := fun w : V =>
      (secondOrderDefectGraph G).neighborFinset w ∩ F
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 2 →
      ∃ w ∈ T,
        let B := G.neighborFinset w.1 ∩ S
        let P₁ := B.filter fun y => (owner y).card = 1
        let P₂ := B.filter fun y => (owner y).card = 2
        (K w.1).card ≤ 3 ∧
        P₁.card = (K w.1).card ∧
        P₁.card + P₂.card = m ∧
        m ≤ P₂.card + 3 ∧
        (∀ y ∈ P₂, (owner y).card = 2) ∧
        (∀ y ∈ P₂, ∀ z ∈ P₂, y ≠ z → Disjoint (owner y) (owner z)) ∧
        B.biUnion owner = F \ K w.1 := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  let K : V → Finset V := fun w =>
    (secondOrderDefectGraph G).neighborFinset w ∩ F
  intro T heven hTcard
  obtain ⟨w, hwT, hwK, _hdegree, _hdegreeLe⟩ :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_exists_lowHoleRow
      G hfree hq hqm hmEven hreg hcard S hempty hCcard hshore htri
      T heven hTcard
  let B := G.neighborFinset w.1 ∩ S
  let P₁ := B.filter fun y => (owner y).card = 1
  let P₂ := B.filter fun y => (owner y).card = 2
  have hwF : w.1 ∉ F := Finset.mem_compl.mp w.2
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hd := hnear w.1 hwF
  have hP₁K : P₁.card = (K w.1).card := by
    let R₁ := S.filter fun y => (owner y).card = 1
    have hP₁ : P₁ = G.neighborFinset w.1 ∩ R₁ := by
      ext y
      simp [P₁, B, R₁, and_assoc]
    rw [hP₁]
    simpa [F, owner, K, R₁] using hd.2.1.symm
  have hBcard : B.card = m := by
    simpa [B] using hd.1
  have hpartition : P₁ ∪ P₂ = B := by
    ext y
    constructor
    · intro hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (Finset.mem_filter.mp hy).1
      · exact (Finset.mem_filter.mp hy).1
    · intro hyB
      have hrep :=
        (c4Free_binarySquare_pureEndpoint_exterior_blockDesign
          G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.2
          y (Finset.mem_inter.mp hyB).2
      rcases hrep.1 with hone | htwo
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hyB, by
          simpa [owner, F] using hone⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyB, by
          simpa [owner, F] using htwo⟩)
  have hdisj : Disjoint P₁ P₂ := Finset.disjoint_left.mpr fun y hy1 hy2 => by
    have h1 := (Finset.mem_filter.mp hy1).2
    have h2 := (Finset.mem_filter.mp hy2).2
    omega
  have hcards : P₁.card + P₂.card = m := by
    rw [← Finset.card_union_of_disjoint hdisj, hpartition, hBcard]
  have hP₁le : P₁.card ≤ 3 := hP₁K.trans_le hwK
  have hP₂large : m ≤ P₂.card + 3 := by
    calc
      m = P₁.card + P₂.card := hcards.symm
      _ ≤ P₂.card + 3 := by omega
  have hP₂two : ∀ y ∈ P₂, (owner y).card = 2 := by
    intro y hy
    exact (Finset.mem_filter.mp hy).2
  have hpairDisjoint : ∀ y ∈ P₂, ∀ z ∈ P₂, y ≠ z →
      Disjoint (owner y) (owner z) := by
    intro y hy z hz hyz
    have hyB := (Finset.mem_filter.mp hy).1
    have hzB := (Finset.mem_filter.mp hz).1
    simpa [B, owner, F] using hd.2.2.1 hyB hzB hyz
  have hunion : B.biUnion owner = F \ K w.1 := by
    simpa [B, owner, F, K] using hd.2.2.2
  exact ⟨w, hwT, hwK, hP₁K, hcards, hP₂large, hP₂two,
    hpairDisjoint, hunion⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_two_ownerPairPacking
