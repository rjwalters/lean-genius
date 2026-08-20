import Proofs.Erdos85OddPlaneOrderBipartiteObstruction
import Proofs.Erdos85GlobalLocalTriangleCount

/-!
# Uniform local triangle count at the odd square order q = 9

The plane-minus-two local window and the global three-to-one triangle count
interact sharply at order 80.  If every vertex has the same number of edges
in its induced neighborhood (in particular, in any vertex-transitive
candidate), that number is forced to be three.
-/

open SimpleGraph

namespace Erdos85

/-- An automorphism restricts to an isomorphism between the graphs induced on
the neighborhoods of a vertex and its image. -/
def neighborInduceIsoOfAutomorphism
    {V : Type*} {G : SimpleGraph V}
    (e : G ≃g G) (x : V) :
    G.induce (G.neighborSet x) ≃g G.induce (G.neighborSet (e x)) where
  toEquiv := e.mapNeighborSet x
  map_rel_iff' := by
    intro u v
    exact e.map_rel_iff

/-- Vertex transitivity phrased directly through graph automorphisms. -/
def VertexTransitiveByIso {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ x y : V, ∃ e : G ≃g G, e x = y

/-- Vertex transitivity makes the induced-neighborhood edge count uniform. -/
theorem localTriangleEdge_card_eq_of_vertexTransitiveByIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htrans : VertexTransitiveByIso G) (x y : V) :
    (G.induce (G.neighborSet x)).edgeFinset.card =
      (G.induce (G.neighborSet y)).edgeFinset.card := by
  obtain ⟨e, he⟩ := htrans x y
  have hcard := (neighborInduceIsoOfAutomorphism e x).card_edgeFinset_eq
  rw [he] at hcard
  exact hcard

/-- **Uniform local triangle counts are multiples of three when `3 ∣ q`.**
At order `q^2-1`, the vertex count is `2 mod 3`.  The global rooted triangle
identity says that the vertex count times the uniform local count is divisible
by three, so the local count itself is divisible by three. -/
theorem three_dvd_uniform_localTriangleEdge_card_of_three_dvd_planeOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (q : ℕ) (hthree : 3 ∣ q)
    (horder : Fintype.card V + 1 = q * q)
    (hfree : ¬ containsC4 V G)
    (r : ℕ)
    (huniform : ∀ v : V,
      (G.induce (G.neighborSet v)).edgeFinset.card = r) :
    3 ∣ r := by
  have hqmod : q % 3 = 0 := Nat.mod_eq_zero_of_dvd hthree
  have hsquaremod : (q * q) % 3 = 0 := by
    rw [Nat.mul_mod, hqmod]
  have hcardSuccMod : (Fintype.card V + 1) % 3 = 0 := by
    rw [horder]
    exact hsquaremod
  have hcardMod : Fintype.card V % 3 = 2 := by omega
  have hsum := sum_localTriangleEdges_eq_three_mul_triangularCliques G hfree
  simp_rw [huniform] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hsumNat : Fintype.card V * r =
      3 * ((triangularEdgeGraph G).cliqueFinset 3).card := by
    exact_mod_cast hsum
  have hprodMod : (Fintype.card V * r) % 3 = 0 := by
    rw [hsumNat]
    exact Nat.mul_mod_right 3 _
  rw [Nat.mul_mod, hcardMod] at hprodMod
  apply Nat.dvd_of_mod_eq_zero
  omega

/-- Direct vertex-transitive form of the mod-three law: when `3 ∣ q`, every
vertex of a transitive C4-free graph of order `q^2-1` lies in a multiple of
three triangles. -/
theorem three_dvd_localTriangleEdge_card_of_vertexTransitive_three_dvd_planeOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (q : ℕ) (hthree : 3 ∣ q)
    (horder : Fintype.card V + 1 = q * q)
    (hfree : ¬ containsC4 V G)
    (htrans : VertexTransitiveByIso G) (v : V) :
    3 ∣ (G.induce (G.neighborSet v)).edgeFinset.card := by
  let r := (G.induce (G.neighborSet v)).edgeFinset.card
  have huniform : ∀ x : V,
      (G.induce (G.neighborSet x)).edgeFinset.card = r := by
    intro x
    exact localTriangleEdge_card_eq_of_vertexTransitiveByIso G htrans x v
  simpa [r] using
    (three_dvd_uniform_localTriangleEdge_card_of_three_dvd_planeOrder
      G q hthree horder hfree r huniform)

/-- A C4-free 9-regular graph on 80 vertices with uniform local triangle
count has exactly three edges in every induced neighborhood.

The local plane-order window gives `1 ≤ r ≤ 4`.  Globally, summing local
triangle edges counts each triangle three times, so `80*r` is divisible by
three.  Since `80` is coprime to three, the only value in the window is
`r = 3`. -/
theorem squareOrderNine_uniform_localTriangleEdge_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hcard : Fintype.card V = 80)
    (hregular : ∀ v : V, G.degree v = 9)
    (hfree : ¬ containsC4 V G)
    (r : ℕ)
    (huniform : ∀ v : V,
      (G.induce (G.neighborSet v)).edgeFinset.card = r) :
    r = 3 := by
  have hVpos : 0 < Fintype.card V := by omega
  let x : V := Classical.choice (Fintype.card_pos_iff.mp hVpos)
  have hbounds := planeMinusTwo_localTriangleEdge_card_bounds_of_odd
    G 9 (by norm_num) (by norm_num) (by omega) hregular hfree x
  rw [huniform x] at hbounds
  have hdiv := three_dvd_uniform_localTriangleEdge_card_of_three_dvd_planeOrder
    G 9 (by norm_num) (by omega) hfree r huniform
  obtain ⟨k, hk⟩ := hdiv
  omega

/-- Every vertex-transitive C4-free 9-regular graph on 80 vertices has exactly
three triangles through each vertex.  This is the direct algebraic/Cayley
candidate interface. -/
theorem squareOrderNine_vertexTransitive_localTriangleEdge_card_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hcard : Fintype.card V = 80)
    (hregular : ∀ v : V, G.degree v = 9)
    (hfree : ¬ containsC4 V G)
    (htrans : VertexTransitiveByIso G) (v : V) :
    (G.induce (G.neighborSet v)).edgeFinset.card = 3 := by
  let r := (G.induce (G.neighborSet v)).edgeFinset.card
  have huniform : ∀ x : V,
      (G.induce (G.neighborSet x)).edgeFinset.card = r := by
    intro x
    exact localTriangleEdge_card_eq_of_vertexTransitiveByIso G htrans x v
  have hr := squareOrderNine_uniform_localTriangleEdge_card_eq_three
    G hcard hregular hfree r huniform
  simpa [r] using hr

end Erdos85
