import Proofs.Erdos85C4FreeCommonNeighborUnique

/-!
# Cross-neighborhood edges form a matching

For two nonadjacent roots in a `C₄`-free graph, the ambient edges between
their open neighborhoods form a partial matching.  This is the geometric
input behind the bounded private `11` atom in `(73rnz_cjibkx)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Oriented ambient edges from the neighborhood of `E` to the neighborhood
of `G`. -/
def crossNeighborhoodEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (E G : V) : Finset (V × V) :=
  (A.neighborFinset E ×ˢ A.neighborFinset G).filter
    (fun e => A.Adj e.1 e.2)

/-- On the `G` shore, a cross-neighborhood edge has a unique endpoint once
its `E`-shore endpoint is fixed. -/
theorem crossNeighborhoodEdge_right_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {E G a b b' : V}
    (hEG : ¬ A.Adj E G)
    (haE : A.Adj E a) (hbG : A.Adj G b) (hb'G : A.Adj G b')
    (hab : A.Adj a b) (hab' : A.Adj a b') : b = b' := by
  have haG : a ≠ G := by
    intro h
    subst a
    exact hEG haE
  exact commonNeighbor_unique_of_c4Free hfree haG
    hab hbG hab' hb'G

/-- Symmetrically, fixing the `G`-shore endpoint fixes the `E`-shore
endpoint. -/
theorem crossNeighborhoodEdge_left_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {E G a a' b : V}
    (hEG : ¬ A.Adj E G)
    (haE : A.Adj E a) (ha'E : A.Adj E a') (hbG : A.Adj G b)
    (hab : A.Adj a b) (ha'b : A.Adj a' b) : a = a' := by
  have hbE : b ≠ E := by
    intro h
    subst b
    exact hEG hbG.symm
  exact commonNeighbor_unique_of_c4Free hfree hbE
    hab.symm haE ha'b.symm ha'E

/-- Cross-neighborhood edges whose two endpoints are selected.  These are
the same-side `11` atoms for the Boolean shore `B`. -/
def crossNeighborhoodElevenEdgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj] (E G : V) (B : Finset V) :
    Finset (V × V) :=
  (crossNeighborhoodEdgeFinset A E G).filter
    (fun e => e.1 ∈ B ∧ e.2 ∈ B)

/-- **Private `11` atom bound (73rnz_cjibkx).**  If the selected part of the
`E` shore is contained in the singleton `p`, at most one selected-selected
cross edge can occur. -/
theorem crossNeighborhoodElevenEdgeFinset_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (hfree : ¬ containsC4 V A) {E G p : V}
    (hEG : ¬ A.Adj E G) (B : Finset V)
    (hprivate : ∀ a, A.Adj E a → a ∈ B → a = p) :
    (crossNeighborhoodElevenEdgeFinset A E G B).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  simp only [crossNeighborhoodElevenEdgeFinset, Finset.mem_filter,
    crossNeighborhoodEdgeFinset, Finset.mem_product] at hx hy
  have hxE : A.Adj E x.1 := (A.mem_neighborFinset E x.1).mp hx.1.1.1
  have hyE : A.Adj E y.1 := (A.mem_neighborFinset E y.1).mp hy.1.1.1
  have hxG : A.Adj G x.2 := (A.mem_neighborFinset G x.2).mp hx.1.1.2
  have hyG : A.Adj G y.2 := (A.mem_neighborFinset G y.2).mp hy.1.1.2
  have hleft : x.1 = y.1 :=
    (hprivate x.1 hxE hx.2.1).trans (hprivate y.1 hyE hy.2.1).symm
  apply Prod.ext hleft
  apply crossNeighborhoodEdge_right_unique A hfree hEG hxE hxG hyG hx.1.2
  simpa only [hleft] using hy.1.2

end

end Erdos85

#print axioms Erdos85.crossNeighborhoodEdge_right_unique
#print axioms Erdos85.crossNeighborhoodEdge_left_unique
#print axioms Erdos85.crossNeighborhoodElevenEdgeFinset_card_le_one
