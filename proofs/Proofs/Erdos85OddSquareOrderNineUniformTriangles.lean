import Proofs.Erdos85OddPlaneOrderBipartiteObstruction
import Proofs.Erdos85GlobalLocalTriangleCount
import Proofs.Erdos85C4FreeFourthMoment

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

/-- An automorphism preserves the triangle-free spanning subgraph. -/
def triangleFreeEdgeGraphIsoOfAutomorphism
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G ≃g G) :
    triangleFreeEdgeGraph G ≃g triangleFreeEdgeGraph G where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    simp only [triangleFreeEdgeGraph_adj, mem_triangleFreeNeighbors]
    have hzero :
        (G.neighborFinset (e x) ∩ G.neighborFinset (e y)).card = 0 ↔
          (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by
      simp only [Finset.card_eq_zero]
      constructor
      · intro hmap
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzmap : e z ∈
            G.neighborFinset (e x) ∩ G.neighborFinset (e y) := by
          simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz ⊢
          exact ⟨e.map_rel_iff.mpr hz.1, e.map_rel_iff.mpr hz.2⟩
        rw [hmap] at hzmap
        simp at hzmap
      · intro horig
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro z hz
        have hzback : e.symm z ∈
            G.neighborFinset x ∩ G.neighborFinset y := by
          simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz ⊢
          constructor
          · apply e.map_rel_iff.mp
            simpa using hz.1
          · apply e.map_rel_iff.mp
            simpa using hz.2
        rw [horig] at hzback
        simp at hzback
    change (G.Adj (e x) (e y) ∧
        (G.neighborFinset (e x) ∩ G.neighborFinset (e y)).card = 0) ↔ _
    rw [e.map_rel_iff, hzero]

/-- Vertex transitivity descends to the triangle-free-edge shadow. -/
theorem triangleFreeEdgeGraph_vertexTransitiveByIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htrans : VertexTransitiveByIso G) :
    VertexTransitiveByIso (triangleFreeEdgeGraph G) := by
  intro x y
  obtain ⟨e, he⟩ := htrans x y
  exact ⟨triangleFreeEdgeGraphIsoOfAutomorphism G e, he⟩

/-- An automorphism also preserves the complementary spanning subgraph of
edges which lie in triangles. -/
def triangularEdgeGraphIsoOfAutomorphism
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : G ≃g G) :
    triangularEdgeGraph G ≃g triangularEdgeGraph G where
  toEquiv := e.toEquiv
  map_rel_iff' := by
    intro x y
    change (G.Adj (e x) (e y) ∧
      ¬(triangleFreeEdgeGraph G).Adj (e x) (e y)) ↔
        (G.Adj x y ∧ ¬(triangleFreeEdgeGraph G).Adj x y)
    have htf := (triangleFreeEdgeGraphIsoOfAutomorphism G e).map_rel_iff
      (a := x) (b := y)
    change (triangleFreeEdgeGraph G).Adj (e x) (e y) ↔
      (triangleFreeEdgeGraph G).Adj x y at htf
    rw [e.map_rel_iff, htf]

/-- Vertex transitivity also descends to the triangular-edge shadow. -/
theorem triangularEdgeGraph_vertexTransitiveByIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htrans : VertexTransitiveByIso G) :
    VertexTransitiveByIso (triangularEdgeGraph G) := by
  intro x y
  obtain ⟨e, he⟩ := htrans x y
  exact ⟨triangularEdgeGraphIsoOfAutomorphism G e, he⟩

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

/-- In a vertex-transitive q=9 candidate the spanning graph of triangle-free
edges is cubic. -/
theorem squareOrderNine_vertexTransitive_triangleFreeEdgeGraph_degree_eq_three
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hcard : Fintype.card V = 80)
    (hregular : ∀ v : V, G.degree v = 9)
    (hfree : ¬ containsC4 V G)
    (htrans : VertexTransitiveByIso G) (v : V) :
    (triangleFreeEdgeGraph G).degree v = 3 := by
  have hlocal :=
    squareOrderNine_vertexTransitive_localTriangleEdge_card_eq_three
      G hcard hregular hfree htrans v
  have hid := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree v
  rw [hlocal, hregular v] at hid
  rw [← (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree,
    triangleFreeEdgeGraph_neighborFinset]
  omega

/-- The triangle-free-edge shadow contains no triangle.  This is independent
of the order and degree assumptions: an edge in the shadow has no common
original neighbor. -/
theorem triangleFreeEdgeGraph_triangle_free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y z : V}
    (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hyz : (triangleFreeEdgeGraph G).Adj y z) :
    ¬(triangleFreeEdgeGraph G).Adj z x := by
  intro hzx
  have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 :=
    ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).2
  have hGyz : G.Adj y z :=
    ((mem_triangleFreeNeighbors G y z).mp
      ((triangleFreeEdgeGraph_adj G y z).mp hyz)).1
  have hGzx : G.Adj z x :=
    ((mem_triangleFreeNeighbors G z x).mp
      ((triangleFreeEdgeGraph_adj G z x).mp hzx)).1
  have hz : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hGzx.symm, hGyz⟩
  rw [Finset.card_eq_zero.mp hzero] at hz
  exact Finset.notMem_empty z hz

/-- Endpoints of an edge in the triangular shadow have no common neighbor in
the triangle-free-edge shadow.  In the configuration interpretation, every
pair of points on a line is therefore at shadow distance at least three. -/
theorem triangularEdgeGraph_adj_no_common_triangleFreeNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {x y : V}
    (hxy : (triangularEdgeGraph G).Adj x y) :
    Disjoint (triangleFreeNeighbors G x) (triangleFreeNeighbors G y) := by
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hGxy : G.Adj x y := hxy.1
  have hzero : (G.neighborFinset x ∩ G.neighborFinset z).card = 0 :=
    ((mem_triangleFreeNeighbors G x z).mp hzx).2
  have hGzy : G.Adj z y := ((mem_triangleFreeNeighbors G y z).mp hzy).1.symm
  have hy : y ∈ G.neighborFinset x ∩ G.neighborFinset z := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hGxy, hGzy⟩
  rw [Finset.card_eq_zero.mp hzero] at hy
  exact Finset.notMem_empty y hy

/-- Vertices at distance at most two in the triangle-free-edge shadow cannot
have a common neighbor in the triangular shadow of a `C₄`-free graph.

For distance one, such a common neighbor would contradict the definition of
a triangle-free edge.  For distance two, the shadow midpoint and the proposed
triangular neighbor would be two distinct common original neighbors, hence
would form a four-cycle. -/
theorem shadow_distance_le_two_no_common_triangularNeighbor
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {x y : V} (hxy : x ≠ y)
    (hnear : (triangleFreeEdgeGraph G).Adj x y ∨
      ∃ z : V, (triangleFreeEdgeGraph G).Adj z x ∧
        (triangleFreeEdgeGraph G).Adj z y)
    {w : V} (hwx : (triangularEdgeGraph G).Adj w x)
    (hwy : (triangularEdgeGraph G).Adj w y) : False := by
  rcases hnear with hshadow | ⟨z, hzx, hzy⟩
  · have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 :=
      ((mem_triangleFreeNeighbors G x y).mp
        ((triangleFreeEdgeGraph_adj G x y).mp hshadow)).2
    have hw : w ∈ G.neighborFinset x ∩ G.neighborFinset y := by
      simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hwx.1.symm, hwy.1.symm⟩
    rw [Finset.card_eq_zero.mp hzero] at hw
    exact Finset.notMem_empty w hw
  · have hGzx : G.Adj z x :=
      ((mem_triangleFreeNeighbors G z x).mp
        ((triangleFreeEdgeGraph_adj G z x).mp hzx)).1
    have hGzy : G.Adj z y :=
      ((mem_triangleFreeNeighbors G z y).mp
        ((triangleFreeEdgeGraph_adj G z y).mp hzy)).1
    have hzw : z ≠ w := by
      intro h
      subst w
      exact hwx.2 hzx
    exact hfree (containsC4_of_two_common hxy hzw hGzx hGzy hwx.1 hwy.1)

/-- A set of shadow diameter at most two meets the triangular neighborhood of
any vertex in at most one point.  Applied to a Petersen component of the
shadow, this says that every cross-component triangular bipartite graph is a
matching. -/
theorem triangularNeighbor_unique_in_shadowDiameterTwoSet
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (S : Set V)
    (hdiam : ∀ {x y : V}, x ∈ S → y ∈ S → x ≠ y →
      (triangleFreeEdgeGraph G).Adj x y ∨
        ∃ z : V, (triangleFreeEdgeGraph G).Adj z x ∧
          (triangleFreeEdgeGraph G).Adj z y)
    {w x y : V} (hx : x ∈ S) (hy : y ∈ S)
    (hwx : (triangularEdgeGraph G).Adj w x)
    (hwy : (triangularEdgeGraph G).Adj w y) : x = y := by
  by_contra hxy
  exact shadow_distance_le_two_no_common_triangularNeighbor
    G hfree hxy (hdiam hx hy hxy) hwx hwy

/-- Complete graph-theoretic interface for the finite `q = 9` shadow census:
the shadow is vertex-transitive, cubic, triangle-free, and `C₄`-free, while a
triangular-shadow edge cannot join two vertices with a common shadow
neighbor. -/
theorem squareOrderNine_vertexTransitive_triangleFreeEdgeGraph_constraints
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hcard : Fintype.card V = 80)
    (hregular : ∀ v : V, G.degree v = 9)
    (hfree : ¬ containsC4 V G)
    (htrans : VertexTransitiveByIso G) :
    VertexTransitiveByIso (triangleFreeEdgeGraph G) ∧
      (∀ v : V, (triangleFreeEdgeGraph G).degree v = 3) ∧
      (∀ x y z : V, (triangleFreeEdgeGraph G).Adj x y →
        (triangleFreeEdgeGraph G).Adj y z →
        ¬(triangleFreeEdgeGraph G).Adj z x) ∧
      ¬ containsC4 V (triangleFreeEdgeGraph G) ∧
      ∀ x y : V, (triangularEdgeGraph G).Adj x y →
        Disjoint (triangleFreeNeighbors G x) (triangleFreeNeighbors G y) := by
  refine ⟨triangleFreeEdgeGraph_vertexTransitiveByIso G htrans, ?_, ?_,
    triangleFreeEdgeGraph_not_containsC4 G hfree, ?_⟩
  · exact squareOrderNine_vertexTransitive_triangleFreeEdgeGraph_degree_eq_three
      G hcard hregular hfree htrans
  · intro x y z hxy hyz
    exact triangleFreeEdgeGraph_triangle_free G hxy hyz
  · intro x y hxy
    exact triangularEdgeGraph_adj_no_common_triangleFreeNeighbor G hxy

/-- Exact global triangle/edge census for a vertex-transitive q=9 candidate:
120 triangle-free edges, 240 edges lying in triangles, and 80 triangles. -/
theorem squareOrderNine_vertexTransitive_triangle_census
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hcard : Fintype.card V = 80)
    (hregular : ∀ v : V, G.degree v = 9)
    (hfree : ¬ containsC4 V G)
    (htrans : VertexTransitiveByIso G) :
    (triangleFreeEdgeGraph G).edgeFinset.card = 120 ∧
      (triangularEdgeGraph G).edgeFinset.card = 240 ∧
      ((triangularEdgeGraph G).cliqueFinset 3).card = 80 := by
  have hlocal : ∀ v : V,
      (G.induce (G.neighborSet v)).edgeFinset.card = 3 :=
    squareOrderNine_vertexTransitive_localTriangleEdge_card_eq_three
      G hcard hregular hfree htrans
  have htfDegree : ∀ v : V, (triangleFreeEdgeGraph G).degree v = 3 :=
    squareOrderNine_vertexTransitive_triangleFreeEdgeGraph_degree_eq_three
      G hcard hregular hfree htrans
  have htriDegree : ∀ v : V, (triangularEdgeGraph G).degree v = 6 := by
    intro v
    have h := two_mul_localTriangleEdges_eq_triangularEdgeGraph_degree G hfree v
    rw [hlocal v] at h
    omega
  have htfHandshake := (triangleFreeEdgeGraph G).sum_degrees_eq_twice_card_edges
  simp_rw [htfDegree] at htfHandshake
  simp [hcard] at htfHandshake
  have htriHandshake := (triangularEdgeGraph G).sum_degrees_eq_twice_card_edges
  simp_rw [htriDegree] at htriHandshake
  simp [hcard] at htriHandshake
  have htriangle := sum_localTriangleEdges_eq_three_mul_triangularCliques G hfree
  simp_rw [hlocal] at htriangle
  simp [hcard] at htriangle
  omega

end Erdos85
