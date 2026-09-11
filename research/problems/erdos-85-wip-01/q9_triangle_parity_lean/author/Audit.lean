import Proofs.Erdos85Problem

/-!
# Local triangle parity in C₄-free graphs

If every edge incident to a vertex belongs to a triangle, its induced
neighbourhood is 1-regular: existence comes from the triangles and uniqueness
from C₄-freeness. The handshaking lemma then forces the vertex degree to be
even. This is the local parity obstruction used for saturated cross blocks
with no internal edges in the cyclic-action analysis of Erdős problem 85.
-/

namespace Erdos85

/-- A neighbourhood covered by triangles is 1-regular in a C₄-free graph. -/
theorem neighborhood_degree_one_of_triangle_cover
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (htri : ∀ w, G.Adj v w → ∃ x, G.Adj v x ∧ G.Adj w x)
    (w : G.neighborSet v) :
    (G.induce (G.neighborSet v)).degree w = 1 := by
  classical
  apply SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
  obtain ⟨x, hvx, hwx⟩ := htri w w.property
  refine ⟨⟨x, hvx⟩, hwx, ?_⟩
  intro y hwy
  apply Subtype.ext
  by_contra hyx
  exact hfree (containsC4_of_two_common (G.ne_of_adj w.property) hyx
    y.property.symm hwy.symm hvx.symm hwx.symm)

/-- If every incident edge lies in a triangle, the vertex has even degree. -/
theorem even_degree_of_triangle_cover
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (htri : ∀ w, G.Adj v w → ∃ x, G.Adj v x ∧ G.Adj w x) :
    Even (G.degree v) := by
  classical
  have hreg := neighborhood_degree_one_of_triangle_cover G hfree v htri
  have heven := (G.induce (G.neighborSet v)).even_card_odd_degree_vertices
  have hcard : Even (Fintype.card (G.neighborSet v)) := by
    simpa [hreg] using heven
  simpa only [G.card_neighborSet_eq_degree] using hcard

/-- Odd degree and a triangle covering every incident edge force a C₄. -/
theorem containsC4_of_odd_degree_triangle_cover
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) (hodd : Odd (G.degree v))
    (htri : ∀ w, G.Adj v w → ∃ x, G.Adj v x ∧ G.Adj w x) :
    containsC4 V G := by
  by_contra hfree
  exact (Nat.not_even_iff_odd.mpr hodd) (even_degree_of_triangle_cover G hfree v htri)

end Erdos85

#print axioms Erdos85.neighborhood_degree_one_of_triangle_cover
#print axioms Erdos85.even_degree_of_triangle_cover
#print axioms Erdos85.containsC4_of_odd_degree_triangle_cover
