import Proofs.Erdos85EightVertexStarDegreeBudget
import Proofs.Erdos85BranchDeficitSymmetry

/-! # The eight non-neighbours of a vertex in a `(16,7)` graph -/

open Finset SimpleGraph

namespace Erdos85

/-- Vertices other than `u` which are not adjacent to `u`. -/
def nonneighborResidual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  (univ.erase u).filter fun x => ¬ G.Adj u x

/-- A degree-seven vertex on sixteen vertices has exactly eight residual
non-neighbours. -/
theorem card_nonneighborResidualSet_eq_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16) (u : V) (hu : G.degree u = 7) :
    Fintype.card (nonneighborResidual G u) = 8 := by
  classical
  rw [Fintype.card_subtype]
  let C : Finset V := insert u (G.neighborFinset u)
  have huNot : u ∉ G.neighborFinset u := by simp
  have hcardC : C.card = 8 := by simp [C, huNot, hu]
  have hfilter :
      (univ.filter fun x => x ∈ nonneighborResidual G u) = univ \ C := by
    ext x
    simp [nonneighborResidual, C, and_comm]
  rw [hfilter, card_sdiff]
  simp [hcard, hcardC]

/-- Triangle-freeness passes to the induced non-neighbour residual. -/
theorem nonneighborResidual_cliqueFree_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : G.CliqueFree 3) (u : V) :
    (G.induce (nonneighborResidual G u : Set V)).CliqueFree 3 := by
  rw [cliqueFree_induce_iff]
  intro s _ hs
  exact htriangle s hs

/-- Inducing cannot increase degree, hence the residual maximum degree is at
most the ambient regular degree seven. -/
theorem nonneighborResidual_degree_le_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (x : (nonneighborResidual G u : Set V)) :
    (G.induce (nonneighborResidual G u : Set V)).degree x ≤ 7 := by
  rw [← (G.induce (nonneighborResidual G u : Set V)).card_neighborFinset_eq_degree]
  calc
    ((G.induce (nonneighborResidual G u : Set V)).neighborFinset x).card ≤
        (G.neighborFinset x.1).card := by
      apply card_le_card_of_injOn
        (fun y : (nonneighborResidual G u : Set V) => y.1)
      · intro y hy
        have hxy : G.Adj x.1 y.1 := by
          exact ((G.induce (nonneighborResidual G u : Set V)).mem_neighborFinset x y).mp hy
        exact (G.mem_neighborFinset x.1 y.1).mpr hxy
      · exact Set.injOn_of_injective Subtype.coe_injective
    _ = G.degree x.1 := G.card_neighborFinset_eq_degree x.1
    _ = 7 := hreg x.1

/-- Induced residual degree is the cardinality of the ambient neighbour set
cut down to the residual finset. -/
theorem nonneighborResidual_degree_eq_card_inter
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (x : (nonneighborResidual G u : Set V)) :
    (G.induce (nonneighborResidual G u : Set V)).degree x =
      (G.neighborFinset x.1 ∩ nonneighborResidual G u).card := by
  classical
  rw [← (G.induce (nonneighborResidual G u : Set V)).card_neighborFinset_eq_degree]
  apply Finset.card_bij (fun y _ => y.1)
  · intro y hy
    have hxy : G.Adj x.1 y.1 :=
      ((G.induce (nonneighborResidual G u : Set V)).mem_neighborFinset x y).mp hy
    exact mem_inter.mpr ⟨(G.mem_neighborFinset x.1 y.1).mpr hxy, y.2⟩
  · intro y hy z hz hyz
    exact Subtype.ext hyz
  · intro y hy
    let z : (nonneighborResidual G u : Set V) :=
      ⟨y, (mem_inter.mp hy).2⟩
    refine ⟨z, ?_, rfl⟩
    apply ((G.induce (nonneighborResidual G u : Set V)).mem_neighborFinset x z).mpr
    change G.Adj x.1 y
    exact (G.mem_neighborFinset x.1 y).mp (mem_inter.mp hy).1

/-- Every neighbour of a residual vertex lies either in the root
neighbourhood or back in the residual, and the two pieces are disjoint. -/
theorem ambient_degree_eq_rootPart_add_residual_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (x : (nonneighborResidual G u : Set V)) :
    G.degree x.1 =
      (G.neighborFinset x.1 ∩ G.neighborFinset u).card +
      (G.induce (nonneighborResidual G u : Set V)).degree x := by
  classical
  rw [← G.card_neighborFinset_eq_degree,
    nonneighborResidual_degree_eq_card_inter]
  let A := G.neighborFinset x.1 ∩ G.neighborFinset u
  let B := G.neighborFinset x.1 ∩ nonneighborResidual G u
  have hunion : G.neighborFinset x.1 = A ∪ B := by
    ext y
    constructor
    · intro hy
      have hxy : G.Adj x.1 y := (G.mem_neighborFinset x.1 y).mp hy
      by_cases huy : G.Adj u y
      · exact mem_union_left _ (mem_inter.mpr
          ⟨hy, (G.mem_neighborFinset u y).mpr huy⟩)
      · have hyu : y ≠ u := by
          intro h
          subst y
          have hxR : x.1 ∈ nonneighborResidual G u := by simpa using x.property
          have hxNonadj : ¬ G.Adj u x.1 := (mem_filter.mp hxR).2
          exact hxNonadj ((G.adj_comm x.1 u).mp hxy)
        exact mem_union_right _ (mem_inter.mpr
          ⟨hy, by simp [nonneighborResidual, hyu, huy]⟩)
    · intro hy
      rcases mem_union.mp hy with hy | hy
      · exact (mem_inter.mp hy).1
      · exact (mem_inter.mp hy).1
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    have huy : G.Adj u y :=
      (G.mem_neighborFinset u y).mp (mem_inter.mp hyA).2
    have : ¬ G.Adj u y := by
      have hyR := (mem_inter.mp hyB).2
      exact (mem_filter.mp hyR).2
    exact this huy
  change (G.neighborFinset x.1).card = A.card + B.card
  calc
    (G.neighborFinset x.1).card = (A ∪ B).card := congrArg card hunion
    _ = A.card + B.card := card_union_of_disjoint hdisj

/-- On a residual edge, the two induced endpoint degrees sum to at least
seven.  Their ambient root-neighbour parts are disjoint subsets of the
seven-element neighbourhood of `u`. -/
theorem nonneighborResidual_adjacent_degree_add_ge_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    {x y : (nonneighborResidual G u : Set V)}
    (hxy : (G.induce (nonneighborResidual G u : Set V)).Adj x y) :
    7 ≤ (G.induce (nonneighborResidual G u : Set V)).degree x +
      (G.induce (nonneighborResidual G u : Set V)).degree y := by
  classical
  let Ax := G.neighborFinset x.1 ∩ G.neighborFinset u
  let Ay := G.neighborFinset y.1 ∩ G.neighborFinset u
  have hxyG : G.Adj x.1 y.1 := hxy
  have hdisj : Disjoint Ax Ay := by
    rw [Finset.disjoint_left]
    intro z hzX hzY
    have hxz : G.Adj x.1 z :=
      (G.mem_neighborFinset x.1 z).mp (mem_inter.mp hzX).1
    have hyz : G.Adj y.1 z :=
      (G.mem_neighborFinset y.1 z).mp (mem_inter.mp hzY).1
    exact htriangle {x.1, y.1, z} (by
      rw [is3Clique_triple_iff]
      exact ⟨hxyG, hxz, hyz⟩)
  have hroot : Ax.card + Ay.card ≤ 7 := by
    rw [← card_union_of_disjoint hdisj, ← hreg u,
      ← G.card_neighborFinset_eq_degree]
    apply card_le_card
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · exact (mem_inter.mp hz).2
    · exact (mem_inter.mp hz).2
  have hxdeg := ambient_degree_eq_rootPart_add_residual_degree G u x
  have hydeg := ambient_degree_eq_rootPart_add_residual_degree G u y
  change G.degree x.1 = Ax.card +
    (G.induce (nonneighborResidual G u : Set V)).degree x at hxdeg
  change G.degree y.1 = Ay.card +
    (G.induce (nonneighborResidual G u : Set V)).degree y at hydeg
  rw [hreg x.1] at hxdeg
  rw [hreg y.1] at hydeg
  omega

/-- Each neighbour of the root has exactly six neighbours in the residual:
its seventh neighbour is the root itself, and triangle-freeness excludes all
other root-neighbourhood edges. -/
theorem rootNeighbor_residual_neighbor_card_eq_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) {u a : V}
    (hua : G.Adj u a) :
    (G.neighborFinset a ∩ nonneighborResidual G u).card = 6 := by
  classical
  let B := G.neighborFinset a ∩ nonneighborResidual G u
  have hunion : G.neighborFinset a = {u} ∪ B := by
    ext y
    constructor
    · intro hay
      have hayG : G.Adj a y := (G.mem_neighborFinset a y).mp hay
      by_cases hyu : y = u
      · exact mem_union_left _ (by simp [hyu])
      · have huyNonadj : ¬ G.Adj u y := by
          intro huy
          exact htriangle {u, a, y} (by
            rw [is3Clique_triple_iff]
            exact ⟨hua, huy, hayG⟩)
        exact mem_union_right _ (mem_inter.mpr
          ⟨hay, by simp [nonneighborResidual, hyu, huyNonadj]⟩)
    · intro hy
      rcases mem_union.mp hy with hy | hy
      · have hyu : y = u := mem_singleton.mp hy
        subst y
        exact (G.mem_neighborFinset a u).mpr ((G.adj_comm u a).mp hua)
      · exact (mem_inter.mp hy).1
  have hdisj : Disjoint ({u} : Finset V) B := by
    rw [Finset.disjoint_left]
    intro y hyu hyB
    have hyu' : y = u := mem_singleton.mp hyu
    subst y
    have huR := (mem_inter.mp hyB).2
    simp [nonneighborResidual] at huR
  have hcardN : (G.neighborFinset a).card = 7 := by
    rw [G.card_neighborFinset_eq_degree, hreg]
  change B.card = 6
  rw [hunion, card_union_of_disjoint hdisj] at hcardN
  simp at hcardN
  omega

/-- The residual graph has total degree fourteen.  This is the `56 - 42`
double count: eight ambient degrees of seven, minus the 42 incidences into
the root neighbourhood. -/
theorem nonneighborResidual_sum_degrees_eq_fourteen
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V) :
    ∑ x : (nonneighborResidual G u : Set V),
      (G.induce (nonneighborResidual G u : Set V)).degree x = 14 := by
  classical
  let R := nonneighborResidual G u
  let A := G.neighborFinset u
  have hcardR : Fintype.card (R : Set V) = 8 := by
    exact card_nonneighborResidualSet_eq_eight G hcard u (hreg u)
  have hcardA : A.card = 7 := by
    simp [A, G.card_neighborFinset_eq_degree, hreg]
  have hsumA : ∑ a ∈ A, (G.neighborFinset a ∩ R).card = 42 := by
    calc
      ∑ a ∈ A, (G.neighborFinset a ∩ R).card = ∑ _a ∈ A, 6 := by
        apply sum_congr rfl
        intro a ha
        exact rootNeighbor_residual_neighbor_card_eq_six G htriangle hreg
          ((G.mem_neighborFinset u a).mp ha)
      _ = 42 := by simp [hcardA]
  have hsumRfin : ∑ x ∈ R, (G.neighborFinset x ∩ A).card = 42 := by
    calc
      _ = ∑ a ∈ A, (G.neighborFinset a ∩ R).card :=
        sum_card_neighbor_inter_comm G R A
      _ = 42 := hsumA
  have hsumR : ∑ x : (R : Set V),
      (G.neighborFinset x.1 ∩ A).card = 42 := by
    rw [← R.attach_eq_univ]
    change ∑ x ∈ R.attach, (G.neighborFinset x.1 ∩ A).card = 42
    have hatt : (∑ x ∈ R.attach, (G.neighborFinset x.1 ∩ A).card) =
        ∑ x ∈ R, (G.neighborFinset x ∩ A).card :=
      Finset.sum_attach R (fun x => (G.neighborFinset x ∩ A).card)
    rw [hatt]
    exact hsumRfin
  have hambient : ∑ x : (R : Set V), G.degree x.1 = 56 := by
    calc
      ∑ x : (R : Set V), G.degree x.1 = ∑ _x : (R : Set V), 7 := by
        apply sum_congr rfl
        intro x _
        exact hreg x.1
      _ = Fintype.card (R : Set V) * 7 := by simp
      _ = 56 := by rw [hcardR]
  have hdecomp : (∑ x : (R : Set V), G.degree x.1) =
      (∑ x : (R : Set V), (G.neighborFinset x.1 ∩ A).card) +
      ∑ x : (R : Set V), (G.induce (R : Set V)).degree x := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro x _
    simpa [R, A] using ambient_degree_eq_rootPart_add_residual_degree G u x
  change (∑ x : (R : Set V), (G.induce (R : Set V)).degree x) = 14
  omega

/-- The completed bridge into the eight-vertex star core.  A routine supplied
minimum-positive-degree witness in the residual produces a degree-seven
residual vertex. -/
theorem exists_degree_seven_in_nonneighborResidual
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    {v : (nonneighborResidual G u : Set V)}
    (hvpos : 0 < (G.induce (nonneighborResidual G u : Set V)).degree v)
    (hminimal : ∀ x : (nonneighborResidual G u : Set V),
      0 < (G.induce (nonneighborResidual G u : Set V)).degree x →
      (G.induce (nonneighborResidual G u : Set V)).degree v ≤
        (G.induce (nonneighborResidual G u : Set V)).degree x) :
    ∃ c : (nonneighborResidual G u : Set V),
      (G.induce (nonneighborResidual G u : Set V)).degree c = 7 := by
  let H := G.induce (nonneighborResidual G u : Set V)
  apply exists_degree_seven_of_eightVertex_residual H
    (card_nonneighborResidualSet_eq_eight G hcard u (hreg u))
    (nonneighborResidual_sum_degrees_eq_fourteen G hcard htriangle hreg u)
    (nonneighborResidual_cliqueFree_three G htriangle u)
    (fun {_ _} hxy =>
      nonneighborResidual_adjacent_degree_add_ge_seven G htriangle hreg u hxy)
    (nonneighborResidual_degree_le_seven G hreg u) hvpos hminimal

/-- The minimum witness required above always exists because the residual
degree sum is fourteen. -/
theorem exists_degree_seven_in_nonneighborResidual_unconditional
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V) :
    ∃ c : (nonneighborResidual G u : Set V),
      (G.induce (nonneighborResidual G u : Set V)).degree c = 7 := by
  classical
  let H := G.induce (nonneighborResidual G u : Set V)
  let P : Finset (nonneighborResidual G u : Set V) :=
    univ.filter fun x => 0 < H.degree x
  have hsum := nonneighborResidual_sum_degrees_eq_fourteen
    G hcard htriangle hreg u
  have hPnonempty : P.Nonempty := by
    by_contra hP
    rw [not_nonempty_iff_eq_empty] at hP
    have hzero : ∀ x : (nonneighborResidual G u : Set V), H.degree x = 0 := by
      intro x
      have hxnot : x ∉ P := by simp [hP]
      simp [P] at hxnot
      omega
    have : (∑ x : (nonneighborResidual G u : Set V), H.degree x) = 0 := by
      apply sum_eq_zero
      intro x _
      exact hzero x
    change (∑ x : (nonneighborResidual G u : Set V), H.degree x) = 14 at hsum
    omega
  obtain ⟨v, hvP, hvmin⟩ := Finset.exists_min_image P
    (fun x => H.degree x) hPnonempty
  have hvpos : 0 < H.degree v := (mem_filter.mp hvP).2
  apply exists_degree_seven_in_nonneighborResidual G hcard htriangle hreg u
    hvpos
  intro x hxpos
  exact hvmin x (mem_filter.mpr ⟨mem_univ x, hxpos⟩)

end Erdos85
