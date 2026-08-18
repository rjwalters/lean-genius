import Proofs.Erdos85SixteenVertexNonneighborResidual

/-! # Bipartition extracted from a residual star center -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

def sixteenLeftSide
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (c : (nonneighborResidual G u : Set V)) : Finset V :=
  insert c.1 (G.neighborFinset u)

def sixteenRightSide
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (c : (nonneighborResidual G u : Set V)) : Finset V :=
  insert u (G.neighborFinset c.1 ∩ nonneighborResidual G u)

/-- The root neighbourhood together with the residual star center has eight
vertices. -/
theorem card_sixteenLeftSide_eq_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V)) :
    (sixteenLeftSide G u c).card = 8 := by
  have hcR : c.1 ∈ nonneighborResidual G u := by simpa using c.property
  have hcNonadj : ¬ G.Adj u c.1 := (mem_filter.mp hcR).2
  have hcNot : c.1 ∉ G.neighborFinset u := by simpa
  simp [sixteenLeftSide, hcNot, G.card_neighborFinset_eq_degree, hreg]

/-- The root together with the seven leaves of the residual star also has
eight vertices. -/
theorem card_sixteenRightSide_eq_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7) :
    (sixteenRightSide G u c).card = 8 := by
  have hcR : c.1 ∈ nonneighborResidual G u := by simpa using c.property
  have hcNonadj : ¬ G.Adj u c.1 := (mem_filter.mp hcR).2
  have huNot : u ∉ G.neighborFinset c.1 ∩ nonneighborResidual G u := by
    simp only [mem_inter, mem_neighborFinset, not_and_or]
    exact Or.inl (fun hcu => hcNonadj ((G.adj_comm c.1 u).mp hcu))
  have hleaves :
      (G.neighborFinset c.1 ∩ nonneighborResidual G u).card = 7 := by
    rw [← nonneighborResidual_degree_eq_card_inter G u c, hc]
  simp [sixteenRightSide, huNot, hleaves]

/-- The two prospective sides are disjoint. -/
theorem disjoint_sixteenLeftSide_sixteenRightSide
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (c : (nonneighborResidual G u : Set V)) :
    Disjoint (sixteenLeftSide G u c) (sixteenRightSide G u c) := by
  rw [Finset.disjoint_left]
  intro x hxL hxR
  have hcR : c.1 ∈ nonneighborResidual G u := by simpa using c.property
  have hcNonadj : ¬ G.Adj u c.1 := (mem_filter.mp hcR).2
  rcases mem_insert.mp hxL with hxc | hxA
  · subst x
    rcases mem_insert.mp hxR with hcu | hcLeaf
    · exact (mem_erase.mp (mem_filter.mp hcR).1).1 hcu
    · exact G.loopless.irrefl c.1
        ((G.mem_neighborFinset c.1 c.1).mp (mem_inter.mp hcLeaf).1)
  · have hux : G.Adj u x := (G.mem_neighborFinset u x).mp hxA
    rcases mem_insert.mp hxR with hxu | hxLeaf
    · subst x
      exact G.loopless.irrefl u hux
    · have hxRmem := (mem_inter.mp hxLeaf).2
      exact (mem_filter.mp hxRmem).2 hux

/-- Since both disjoint sides have eight vertices in a sixteen-vertex
ambient type, they cover the universe. -/
theorem union_sixteenSides_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7) :
    sixteenLeftSide G u c ∪ sixteenRightSide G u c = univ := by
  apply eq_of_subset_of_card_le (subset_univ _)
  rw [card_univ, hcard,
    card_union_of_disjoint (disjoint_sixteenLeftSide_sixteenRightSide G u c),
    card_sixteenLeftSide_eq_eight G hreg u c,
    card_sixteenRightSide_eq_eight G u c hc]

/-- No edge lies inside the left side. -/
theorem sixteenLeftSide_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7)
    {x y : V} (hx : x ∈ sixteenLeftSide G u c)
    (hy : y ∈ sixteenLeftSide G u c) (hxy : x ≠ y) :
    ¬ G.Adj x y := by
  have hdecomp := ambient_degree_eq_rootPart_add_residual_degree G u c
  rw [hreg c.1, hc] at hdecomp
  have hrootZero :
      (G.neighborFinset c.1 ∩ G.neighborFinset u).card = 0 := by omega
  have hcRoot : ∀ {a : V}, G.Adj u a → ¬ G.Adj c.1 a := by
    intro a hua hca
    have ha : a ∈ G.neighborFinset c.1 ∩ G.neighborFinset u :=
      mem_inter.mpr ⟨(G.mem_neighborFinset c.1 a).mpr hca,
        (G.mem_neighborFinset u a).mpr hua⟩
    rw [card_eq_zero] at hrootZero
    simpa [hrootZero] using ha
  rcases mem_insert.mp hx with rfl | hxA <;>
    rcases mem_insert.mp hy with rfl | hyA
  · exact (hxy rfl).elim
  · exact hcRoot (G.mem_neighborFinset u y |>.mp hyA)
  · intro hxyG
    exact hcRoot (G.mem_neighborFinset u x |>.mp hxA)
      ((G.adj_comm x c.1).mp hxyG)
  · intro hxyG
    have hux := (G.mem_neighborFinset u x).mp hxA
    have huy := (G.mem_neighborFinset u y).mp hyA
    exact htriangle {u, x, y} (by
      rw [is3Clique_triple_iff]
      exact ⟨hux, huy, hxyG⟩)

/-- No edge lies inside the right side. -/
theorem sixteenRightSide_not_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htriangle : G.CliqueFree 3) (u : V)
    (c : (nonneighborResidual G u : Set V))
    {x y : V} (hx : x ∈ sixteenRightSide G u c)
    (hy : y ∈ sixteenRightSide G u c) (hxy : x ≠ y) :
    ¬ G.Adj x y := by
  rcases mem_insert.mp hx with rfl | hxL <;>
    rcases mem_insert.mp hy with rfl | hyL
  · exact (hxy rfl).elim
  · have hyR := (mem_inter.mp hyL).2
    exact (mem_filter.mp hyR).2
  · intro hux
    have hxR := (mem_inter.mp hxL).2
    exact (mem_filter.mp hxR).2 ((G.adj_comm x y).mp hux)
  · intro hxyG
    have hcx : G.Adj c.1 x :=
      (G.mem_neighborFinset c.1 x).mp (mem_inter.mp hxL).1
    have hcy : G.Adj c.1 y :=
      (G.mem_neighborFinset c.1 y).mp (mem_inter.mp hyL).1
    exact htriangle {c.1, x, y} (by
      rw [is3Clique_triple_iff]
      exact ⟨hcx, hcy, hxyG⟩)

/-- Every left-side vertex has all seven neighbours on the right. -/
theorem left_neighbor_inter_right_card_eq_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7)
    {x : V} (hx : x ∈ sixteenLeftSide G u c) :
    (G.neighborFinset x ∩ sixteenRightSide G u c).card = 7 := by
  have hcover := union_sixteenSides_eq_univ G hcard hreg u c hc
  have hsub : G.neighborFinset x ⊆ sixteenRightSide G u c := by
    intro y hy
    have hyUnion : y ∈ sixteenLeftSide G u c ∪ sixteenRightSide G u c := by
      rw [hcover]
      exact mem_univ y
    rcases mem_union.mp hyUnion with hyL | hyR
    · have hxyNe : x ≠ y := by
        intro h
        subst y
        exact G.loopless.irrefl x ((G.mem_neighborFinset x x).mp hy)
      exact False.elim ((sixteenLeftSide_not_adj G htriangle hreg u c hc
        hx hyL hxyNe) ((G.mem_neighborFinset x y).mp hy))
    · exact hyR
  rw [inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, hreg]

/-- Every right-side vertex has all seven neighbours on the left. -/
theorem right_neighbor_inter_left_card_eq_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 16)
    (htriangle : G.CliqueFree 3)
    (hreg : ∀ x : V, G.degree x = 7) (u : V)
    (c : (nonneighborResidual G u : Set V))
    (hc : (G.induce (nonneighborResidual G u : Set V)).degree c = 7)
    {x : V} (hx : x ∈ sixteenRightSide G u c) :
    (G.neighborFinset x ∩ sixteenLeftSide G u c).card = 7 := by
  have hcover := union_sixteenSides_eq_univ G hcard hreg u c hc
  have hsub : G.neighborFinset x ⊆ sixteenLeftSide G u c := by
    intro y hy
    have hyUnion : y ∈ sixteenLeftSide G u c ∪ sixteenRightSide G u c := by
      rw [hcover]
      exact mem_univ y
    rcases mem_union.mp hyUnion with hyL | hyR
    · exact hyL
    · have hxyNe : x ≠ y := by
        intro h
        subst y
        exact G.loopless.irrefl x ((G.mem_neighborFinset x x).mp hy)
      exact False.elim ((sixteenRightSide_not_adj G htriangle u c
        hx hyR hxyNe) ((G.mem_neighborFinset x y).mp hy))
  rw [inter_eq_left.mpr hsub, G.card_neighborFinset_eq_degree, hreg]

end

end Erdos85
