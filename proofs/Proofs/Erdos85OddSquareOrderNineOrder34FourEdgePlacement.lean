import Proofs.Erdos85OddSquareOrderNineArticulationLowSetTransfer

/-! # The corrected order-34 four-edge placement

This file isolates the part of the owner-punctured order-34 argument that
does not depend on the exceptional point's shore.  In the `(2,2)` branch,
the two selected bin-zero points must be exactly the regular local pair.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-local-edge `(2,2)` branch, the two points of `W` adjacent to
the owner are exactly its regular/nondefect bin-zero pair.  If `W` contained
the unique exceptional point, its other member would be regular, adjacent to
neither member of `W`, and hence would have only the owner as a `Z`-neighbor,
contrary to the regular point's `Z`-degree two. -/
theorem orderNine_order34_four_edge_owner_W_two_eq_regular_pair
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
    {owner : V}
    (howner : owner ∈ squareOrderNineLowIncidenceBin G 3)
    (hloc : (G.induce (G.neighborSet owner)).edgeFinset.card = 4)
    (Z P W : Finset V)
    (hpartition : Z = insert owner (P ∪ W))
    (hPsub : P ⊆ squareOrderNineLowIncidenceBin G 1)
    (hWsub : W ⊆ squareOrderNineLowIncidenceBin G 0)
    (hWcard : W.card = 2)
    (hownerW : (G.neighborFinset owner ∩ W).card = 2)
    (hregularZdegree : ∀ y ∈
      ((G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) \
        (secondOrderDefectGraph G).neighborFinset owner),
      (G.neighborFinset y ∩ Z).card = 2) :
    W = (G.neighborFinset owner ∩ squareOrderNineLowIncidenceBin G 0) \
      (secondOrderDefectGraph G).neighborFinset owner := by
  classical
  let D := secondOrderDefectGraph G
  let B := squareOrderNineLowIncidenceBin G
  let U := G.neighborFinset owner ∩ B 0
  let E := U ∩ D.neighborFinset owner
  let R := U \ D.neighborFinset owner
  have hgeom := orderNine_secondProfile_owner_four_edge_binZero_partition
    G hfree hmin hcover hcard hp hhigh hc2 hc3 hc4 howner hloc
  dsimp only at hgeom
  have hEcard : E.card = 1 := by simpa [E, U, B, D] using hgeom.1
  have hRcard : R.card = 2 := by simpa [R, U, B, D] using hgeom.2.1
  have hER : ∀ e ∈ E, ∀ r ∈ R, ¬ G.Adj e r := by
    simpa [E, R, U, B, D] using hgeom.2.2.1
  have hWinter : G.neighborFinset owner ∩ W = W := by
    apply Finset.eq_of_subset_of_card_le
    · exact Finset.inter_subset_right
    · rw [hWcard, hownerW]
  have hWsubU : W ⊆ U := by
    intro y hy
    exact Finset.mem_inter.mpr ⟨by
      have : y ∈ G.neighborFinset owner ∩ W := by rw [hWinter]; exact hy
      exact (Finset.mem_inter.mp this).1, hWsub hy⟩
  have hnotE : ∀ y ∈ W, y ∉ E := by
    intro y hyW hyE
    have hWlarge : 1 < W.card := by rw [hWcard]; omega
    obtain ⟨z, hzW, hzy⟩ := Finset.exists_mem_ne hWlarge y
    have hzU := hWsubU hzW
    have hzNotE : z ∉ E := by
      intro hzE
      have hzy' : z = y :=
        Finset.card_le_one.mp (by rw [hEcard]) z hzE y hyE
      exact hzy hzy'
    have hzNotD : z ∉ D.neighborFinset owner := by
      intro hzD
      exact hzNotE (Finset.mem_inter.mpr ⟨hzU, hzD⟩)
    have hzR : z ∈ R := Finset.mem_sdiff.mpr ⟨hzU, hzNotD⟩
    have hpairSub : ({y, z} : Finset V) ⊆ W := by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hyW
      · have hwz : w = z := Finset.mem_singleton.mp hw
        simpa [hwz] using hzW
    have hpairCard : ({y, z} : Finset V).card = 2 := by
      simp [Ne.symm hzy]
    have hWpair : W = {y, z} :=
      (Finset.eq_of_subset_of_card_le hpairSub (by
        rw [hpairCard, hWcard])).symm
    have hzWzero : (G.neighborFinset z ∩ W).card = 0 := by
      apply Finset.card_eq_zero.mpr
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      have hwParts := Finset.mem_inter.mp hw
      rw [hWpair] at hwParts
      rcases Finset.mem_insert.mp hwParts.2 with hwy | hwz
      · subst w
        exact (hER y hyE z hzR)
          ((G.adj_comm z y).mp ((G.mem_neighborFinset z y).mp hwParts.1))
      · have hwz' : w = z := Finset.mem_singleton.mp hwz
        subst w
        exact G.loopless.irrefl z ((G.mem_neighborFinset z z).mp hwParts.1)
    exact false_of_orderNine_order34_owner_neighbor_outside_low_parts
      G hfree hhigh owner z howner (Finset.mem_inter.mp hzU).2
        ((G.adj_comm owner z).mp
          ((G.mem_neighborFinset owner z).mp (Finset.mem_inter.mp hzU).1))
        Z P W hpartition hPsub hzWzero
        (hregularZdegree z (by simpa [R, U, B, D] using hzR))
  have hWsubR : W ⊆ R := by
    intro y hy
    have hyU := hWsubU hy
    exact Finset.mem_sdiff.mpr ⟨hyU, by
      intro hyD
      exact hnotE y hy (Finset.mem_inter.mpr ⟨hyU, hyD⟩)⟩
  have hWR : W = R := Finset.eq_of_subset_of_card_le hWsubR (by
    rw [hWcard, hRcard])
  simpa [R, U, B, D] using hWR

#print axioms orderNine_order34_four_edge_owner_W_two_eq_regular_pair

end

end Erdos85
