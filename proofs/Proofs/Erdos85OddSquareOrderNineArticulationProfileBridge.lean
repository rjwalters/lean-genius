import Proofs.Erdos85OddSquareOrderNineArticulationGraphBridge
import Proofs.Erdos85OddSquareOrderNineThreeHighSecondProfileBinZeroDefectTypes

/-! # Actual-profile inputs for the q = 9 articulation bridge

Node: B.3 / GAP B-CLASSIFY.  This file specializes the abstract deleted-owner
articulation machinery to the `(53,27,0,1,0)` three-high profile.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In the second three-high profile, every defect neighbor of the unique
bin-three owner is a bin-zero vertex.  Consequently owner adjacency is
equivalent to membership in its five-element exceptional bin-zero set. -/
theorem squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    E.card = 5 ∧ D.neighborFinset owner = E ∧
      ∀ u : V, D.Adj u owner ↔ u ∈ E := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := D.neighborFinset owner ∩ B 0
  have hneighbors := squareOrderNine_threeHigh_secondProfile_binThree_neighbors
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner
  dsimp only at hneighbors
  have hdegree := squareOrderNine_lowIncidenceBin_pointwise_ledger
    G hfree hmin hcover hcard howner
  dsimp only at hdegree
  have hEcard : E.card = 5 := by
    exact hneighbors.1
  have hneighborCard : (D.neighborFinset owner).card = 5 := by
    rw [D.card_neighborFinset_eq_degree, hdegree.1]
  have hneighborEq : D.neighborFinset owner = E := by
    apply Finset.eq_of_subset_of_card_le
    · exact fun u hu => by
        have hcardLe : (D.neighborFinset owner).card ≤ E.card := by
          rw [hneighborCard, hEcard]
        have hinterSubset : E ⊆ D.neighborFinset owner := Finset.inter_subset_left
        exact (Finset.eq_of_subset_of_card_le hinterSubset hcardLe).symm.subset hu
    · rw [hneighborCard, hEcard]
  refine ⟨hEcard, hneighborEq, ?_⟩
  intro u
  rw [D.adj_comm, ← D.mem_neighborFinset]
  exact Iff.of_eq (congrArg (fun s : Finset V => u ∈ s) hneighborEq)

/-- After deleting the bin-three owner and its five exceptional bin-zero
neighbors from the regular class, the remaining bin-zero vertices have
three bin-one defect neighbors, while every bin-one vertex has five defect
neighbors in that regular class. -/
theorem squareOrderNine_threeHigh_secondProfile_articulation_cross_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ z : V, 9 ≤ G.degree z)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 9 ∨ G.degree v = 9)
    (hcard : Fintype.card V = 81)
    (hp : SquareOrderNonregularSectorProfile G 9)
    (hhigh : (squareOrderHighVertices G 9).card = 3)
    (hc2 : squareOrderNineHighIncidenceHistogram G 2 = 0)
    (hc3 : squareOrderNineHighIncidenceHistogram G 3 = 1)
    (hc4 : squareOrderNineHighIncidenceHistogram G 4 = 0)
    {owner : V} (howner : owner ∈ squareOrderNineLowIncidenceBin G 3) :
    let D := secondOrderDefectGraph G
    let B := squareOrderNineLowIncidenceBin G
    let E := D.neighborFinset owner ∩ B 0
    let R := B 0 \ E
    (∀ x ∈ R, (D.neighborFinset x ∩ B 0).card = 5 ∧
      (D.neighborFinset x ∩ B 1).card = 3) ∧
    ∀ y ∈ B 1, (D.neighborFinset y ∩ R).card = 5 := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let E := D.neighborFinset owner ∩ B 0
  let R := B 0 \ E
  have hB3card : (B 3).card = 1 := by
    dsimp [B]
    rw [squareOrderNine_lowIncidenceBin_card_eq_histogram_of_ne_zero
      G hp (i := 3) (by omega), hc3]
  have hEexceptional : ∀ x ∈ E,
      (D.neighborFinset x ∩ B 0).card = 7 ∧
      (D.neighborFinset x ∩ B 1).card = 0 := by
    intro x hxE
    have hxParts := Finset.mem_inter.mp hxE
    have htype :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hxParts.2
    dsimp only at htype
    rcases htype with hregular | hexceptional
    · have hownerInter : owner ∈ D.neighborFinset x ∩ B 3 := by
        refine Finset.mem_inter.mpr ⟨?_, howner⟩
        exact (D.mem_neighborFinset x owner).mpr
          ((D.adj_comm owner x).mp ((D.mem_neighborFinset owner x).mp hxParts.1))
      have : 0 < (D.neighborFinset x ∩ B 3).card :=
        Finset.card_pos.mpr ⟨owner, hownerInter⟩
      rw [hregular.2.2] at this
      omega
    · exact ⟨hexceptional.1, hexceptional.2.1⟩
  constructor
  · intro x hxR
    have hxParts := Finset.mem_sdiff.mp hxR
    have htype :=
      squareOrderNine_threeHigh_secondProfile_binZero_defect_neighbor_dichotomy
        G hfree hmin hcover hcard hp hhigh hc2 hc4 hxParts.1
    dsimp only at htype
    rcases htype with hregular | hexceptional
    · exact ⟨hregular.1, hregular.2.1⟩
    · exfalso
      have hinter : D.neighborFinset x ∩ B 3 = B 3 := by
        apply Finset.eq_of_subset_of_card_le
        · exact Finset.inter_subset_right
        · rw [hexceptional.2.2, hB3card]
      have hownerNx : owner ∈ D.neighborFinset x := by
        have : owner ∈ D.neighborFinset x ∩ B 3 := by
          rw [hinter]
          exact howner
        exact (Finset.mem_inter.mp this).1
      apply hxParts.2
      exact Finset.mem_inter.mpr ⟨
        (D.mem_neighborFinset owner x).mpr
          ((D.adj_comm x owner).mp ((D.mem_neighborFinset x owner).mp hownerNx)),
        hxParts.1⟩
  · intro y hyB1
    have hyType := squareOrderNine_threeHigh_secondProfile_binOne_defect_neighbors
      G hfree hmin hcover hcard hp hhigh hc2 hc4 hyB1
    dsimp only at hyType
    have hinter : D.neighborFinset y ∩ R = D.neighborFinset y ∩ B 0 := by
      ext x
      simp only [R, Finset.mem_inter, Finset.mem_sdiff]
      constructor
      · exact fun hx => ⟨hx.1, hx.2.1⟩
      · intro hx
        refine ⟨hx.1, hx.2, ?_⟩
        intro hxE
        have hxExceptional := hEexceptional x hxE
        have hyAtX : y ∈ D.neighborFinset x ∩ B 1 := by
          refine Finset.mem_inter.mpr ⟨?_, hyB1⟩
          exact (D.mem_neighborFinset x y).mpr
            ((D.adj_comm y x).mp ((D.mem_neighborFinset y x).mp hx.1))
        have : 0 < (D.neighborFinset x ∩ B 1).card :=
          Finset.card_pos.mpr ⟨y, hyAtX⟩
        omega
    rw [hinter]
    exact hyType.1

end

#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_owner_defect_neighbors
#print axioms Erdos85.squareOrderNine_threeHigh_secondProfile_articulation_cross_degrees

end Erdos85
