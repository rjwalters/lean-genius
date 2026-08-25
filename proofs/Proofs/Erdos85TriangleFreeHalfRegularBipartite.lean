import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# The half-regular triangle-free equality case

A triangle-free `q`-regular graph on `2q` vertices is complete bipartite.
The neighborhood-partition form below is the interface needed by the
size-two selector-graph argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a triangle-free regular graph of order twice its degree, the
neighborhoods of the endpoints of every edge partition the vertex set. -/
theorem neighborFinset_eq_compl_neighborFinset_of_triangleFree_halfRegular
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : SimpleGraph V) [DecidableRel S.Adj] {q : ℕ}
    (hcard : Fintype.card V = 2 * q)
    (hreg : ∀ x, S.degree x = q)
    (htri : S.CliqueFree 3) {u v : V} (huv : S.Adj u v) :
    S.neighborFinset v = Finset.univ \ S.neighborFinset u := by
  classical
  have hsubset : S.neighborFinset v ⊆
      Finset.univ \ S.neighborFinset u := by
    intro z hz
    have hvz : S.Adj v z := (S.mem_neighborFinset v z).mp hz
    have huz : ¬ S.Adj u z := by
      intro huz
      have hind := S.isIndepSet_neighborSet_of_triangleFree htri u
      exact hind huv huz hvz.ne hvz
    simp [huz]
  have hleft : (S.neighborFinset v).card = q := by
    rw [S.card_neighborFinset_eq_degree, hreg]
  have hright : (Finset.univ \ S.neighborFinset u).card = q := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      S.card_neighborFinset_eq_degree, hcard, hreg]
    omega
  exact Finset.eq_of_subset_of_card_le hsubset (by omega)

/-- Equivalently, every neighbor of a fixed vertex is adjacent to every
vertex outside that vertex's neighborhood. -/
theorem adj_of_triangleFree_halfRegular_of_mem_neighbor_of_not_mem_neighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : SimpleGraph V) [DecidableRel S.Adj] {q : ℕ}
    (hcard : Fintype.card V = 2 * q)
    (hreg : ∀ x, S.degree x = q)
    (htri : S.CliqueFree 3) {u v w : V}
    (hv : v ∈ S.neighborFinset u) (hw : w ∉ S.neighborFinset u) :
    S.Adj v w := by
  have huv : S.Adj u v := (S.mem_neighborFinset u v).mp hv
  have hpartition :=
    neighborFinset_eq_compl_neighborFinset_of_triangleFree_halfRegular
      S hcard hreg htri huv
  have hw' : w ∈ Finset.univ \ S.neighborFinset u := by simp [hw]
  rw [← hpartition] at hw'
  exact (S.mem_neighborFinset v w).mp hw'

#print axioms neighborFinset_eq_compl_neighborFinset_of_triangleFree_halfRegular
#print axioms adj_of_triangleFree_halfRegular_of_mem_neighbor_of_not_mem_neighbor

end

end Erdos85
