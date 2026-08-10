import Proofs.Erdos85LocalTriangleParity

/-!
# Global count of local triangle edges

In a `C₄`-free graph, summing the number of edges in all neighborhood graphs
counts each triangle three times.  We prove this through the spanning graph of
edges lying in triangles; local linearity gives the global factor three.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Twice the number of edges in the neighborhood graph at `x` is the degree
of `x` in the spanning graph consisting of edges which lie in triangles. -/
theorem two_mul_localTriangleEdges_eq_triangularEdgeGraph_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (x : V) :
    2 * (G.induce (G.neighborSet x)).edgeFinset.card =
      (triangularEdgeGraph G).degree x := by
  have hlocal := card_triangleFreeNeighbors_add_two_mul_localEdges
    G hfree x
  have hsub : (triangleFreeNeighbors G x) ⊆ G.neighborFinset x := by
    intro y hy
    simpa [SimpleGraph.mem_neighborFinset] using
      ((mem_triangleFreeNeighbors G x y).mp hy).1
  have hneighbors : (triangularEdgeGraph G).neighborFinset x =
      G.neighborFinset x \ triangleFreeNeighbors G x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
    rw [triangularEdgeGraph_adj]
    constructor
    · rintro ⟨hxy, hcommon⟩
      exact ⟨hxy, fun htf => hcommon
        ((mem_triangleFreeNeighbors G x y).mp htf).2⟩
    · rintro ⟨hxy, hnot⟩
      refine ⟨hxy, ?_⟩
      intro hzero
      exact hnot ((mem_triangleFreeNeighbors G x y).mpr ⟨hxy, hzero⟩)
  rw [← (triangularEdgeGraph G).card_neighborFinset_eq_degree,
    hneighbors, Finset.card_sdiff_of_subset hsub,
    G.card_neighborFinset_eq_degree]
  omega

/-- The sum of all rooted local-triangle edge counts is three times the
number of triangles in the triangular-edge graph.  Its cliques are precisely
the triangles of the original graph, but this form avoids needing that
identification downstream. -/
theorem sum_localTriangleEdges_eq_three_mul_triangularCliques
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) :
    (∑ x : V, (G.induce (G.neighborSet x)).edgeFinset.card) =
      3 * ((triangularEdgeGraph G).cliqueFinset 3).card := by
  let T := triangularEdgeGraph G
  have hdegrees : 2 * (∑ x : V,
      (G.induce (G.neighborSet x)).edgeFinset.card) =
      ∑ x : V, T.degree x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    exact two_mul_localTriangleEdges_eq_triangularEdgeGraph_degree
      G hfree x
  have hhandshake : (∑ x : V, T.degree x) = 2 * T.edgeFinset.card :=
    T.sum_degrees_eq_twice_card_edges
  have hlinear : T.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have htriangles : T.edgeFinset.card =
      3 * (T.cliqueFinset 3).card := hlinear.card_edgeFinset
  rw [hhandshake, htriangles] at hdegrees
  change (∑ x : V, (G.induce (G.neighborSet x)).edgeFinset.card) =
    3 * (T.cliqueFinset 3).card
  omega

/-- In the degree-thirteen, order-192 Stage-1 residual, 328 triangles leave
exactly 264 edges which lie in no triangle.  These are precisely the
`H ∩ A` edges in the zero-layer square identity. -/
theorem degree_thirteen_order_192_triangleFreeEdgeGraph_card_eq_264
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 192)
    (hreg : ∀ x : V, G.degree x = 13)
    (htriangles : ((triangularEdgeGraph G).cliqueFinset 3).card = 328) :
    (triangleFreeEdgeGraph G).edgeFinset.card = 264 := by
  let T := triangleFreeEdgeGraph G
  let H := triangularEdgeGraph G
  have hTle : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hedgeG : G.edgeFinset.card = 1248 := by
    have hhandshake := G.sum_degrees_eq_twice_card_edges
    simp_rw [hreg] at hhandshake
    simp [hcard] at hhandshake
    omega
  have hlocal : H.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have hedgeH : H.edgeFinset.card = 984 := by
    rw [hlocal.card_edgeFinset, htriangles]
  have hpartition : G.edgeFinset.card = H.edgeFinset.card + T.edgeFinset.card := by
    have heq : H.edgeFinset = G.edgeFinset \ T.edgeFinset := by
      ext e
      simp [H, T, triangularEdgeGraph]
    rw [heq, Finset.card_sdiff_of_subset (edgeFinset_mono hTle)]
    have hle := Finset.card_le_card (edgeFinset_mono hTle)
    omega
  rw [hedgeG, hedgeH] at hpartition
  change T.edgeFinset.card = 264
  omega

/-- A degree-thirteen vertex with one triangle-free incident edge has
exactly twelve incident edges in the triangular-edge graph. -/
theorem triangularEdgeGraph_degree_eq_twelve_of_degree_thirteen_sparse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (x : V) (hdegree : G.degree x = 13)
    (hone : (triangleFreeNeighbors G x).card = 1) :
    (triangularEdgeGraph G).degree x = 12 := by
  have hsub : triangleFreeNeighbors G x ⊆ G.neighborFinset x := by
    intro y hy
    simpa [SimpleGraph.mem_neighborFinset] using
      ((mem_triangleFreeNeighbors G x y).mp hy).1
  have heq : (triangularEdgeGraph G).neighborFinset x =
      G.neighborFinset x \ triangleFreeNeighbors G x := by
    ext y
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_sdiff]
    rw [triangularEdgeGraph_adj]
    constructor
    · rintro ⟨hxy, hcommon⟩
      exact ⟨hxy, fun htf => hcommon
        ((mem_triangleFreeNeighbors G x y).mp htf).2⟩
    · rintro ⟨hxy, hnot⟩
      refine ⟨hxy, ?_⟩
      intro hzero
      exact hnot ((mem_triangleFreeNeighbors G x y).mpr ⟨hxy, hzero⟩)
  rw [← (triangularEdgeGraph G).card_neighborFinset_eq_degree, heq,
    Finset.card_sdiff_of_subset hsub, G.card_neighborFinset_eq_degree,
    hdegree, hone]

/-- Distinct centers in a C4-free graph have at most one common triangular
neighbor, since triangular edges are original graph edges. -/
theorem triangularNeighborFinset_inter_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x z : V} (hne : x ≠ z) :
    ((triangularEdgeGraph G).neighborFinset x ∩
      (triangularEdgeGraph G).neighborFinset z).card ≤ 1 := by
  have hsub : (triangularEdgeGraph G).neighborFinset x ∩
      (triangularEdgeGraph G).neighborFinset z ⊆
      G.neighborFinset x ∩ G.neighborFinset z := by
    intro y hy
    have hy' := Finset.mem_inter.mp hy
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_neighborFinset x y).mpr <|
        ((triangularEdgeGraph_adj G x y).mp
          (((triangularEdgeGraph G).mem_neighborFinset x y).mp hy'.1)).1
    · exact (G.mem_neighborFinset z y).mpr <|
        ((triangularEdgeGraph_adj G z y).mp
          (((triangularEdgeGraph G).mem_neighborFinset z y).mp hy'.2)).1
  exact (Finset.card_le_card hsub).trans
    (common_le_one_of_not_containsC4 hfree x z hne)

/-- Therefore two distinct sparse degree-thirteen centers have at least 23
distinct triangular neighbors between them. -/
theorem twenty_three_le_card_union_triangularNeighbors_of_two_sparse
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x z : V} (hne : x ≠ z)
    (hxdegree : G.degree x = 13) (hzdegree : G.degree z = 13)
    (hxone : (triangleFreeNeighbors G x).card = 1)
    (hzone : (triangleFreeNeighbors G z).card = 1) :
    23 ≤ ((triangularEdgeGraph G).neighborFinset x ∪
      (triangularEdgeGraph G).neighborFinset z).card := by
  have hx := triangularEdgeGraph_degree_eq_twelve_of_degree_thirteen_sparse
    G x hxdegree hxone
  have hz := triangularEdgeGraph_degree_eq_twelve_of_degree_thirteen_sparse
    G z hzdegree hzone
  rw [← (triangularEdgeGraph G).card_neighborFinset_eq_degree] at hx hz
  have hinter := triangularNeighborFinset_inter_card_le_one G hfree hne
  have hcard := Finset.card_union_add_card_inter
    ((triangularEdgeGraph G).neighborFinset x)
    ((triangularEdgeGraph G).neighborFinset z)
  omega

/-- A mixed third trace counts, with orientation, the common `A`-neighbors
across the edges of `H`.  This is the graph bridge for the fixed Stage-1
identity `tr(H A²) = 15696`. -/
theorem trace_adjMatrix_mul_adjMatrix_sq_eq_sum_common_over_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (H A : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel A.Adj] :
    Matrix.trace (H.adjMatrix ℤ * (A.adjMatrix ℤ * A.adjMatrix ℤ)) =
      ∑ x : V, ∑ y ∈ H.neighborFinset x,
        ((A.neighborFinset x ∩ A.neighborFinset y).card : ℤ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  rw [Matrix.diag_apply, Matrix.mul_apply]
  simp only [adjMatrix_sq_apply_eq_card_common,
    SimpleGraph.adjMatrix_apply]
  classical
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext y
    simp [SimpleGraph.mem_neighborFinset]
  · intro y hy
    simp [Finset.inter_comm]

/-- If the 192 local overlap degrees are odd and have total 528 (twice the
264 overlap edges), their total half-excess above one is exactly 168. -/
theorem sum_half_excess_eq_168_of_odd_overlap_degrees
    {V : Type*} [Fintype V]
    (overlapDegree halfExcess : V → ℕ)
    (hcard : Fintype.card V = 192)
    (hodd : ∀ x, overlapDegree x = 2 * halfExcess x + 1)
    (hsum : (∑ x : V, overlapDegree x) = 528) :
    (∑ x : V, halfExcess x) = 168 := by
  simp_rw [hodd] at hsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  simp [hcard] at hsum
  omega

/-- A nonnegative half-excess budget of 168 spread over 192 vertices leaves
at least 24 zero-excess vertices, hence at least 24 local overlap degrees
equal to one. -/
theorem twenty_four_le_card_zero_halfExcess_of_sum_eq_168
    {V : Type*} [Fintype V] [DecidableEq V]
    (halfExcess : V → ℕ)
    (hcard : Fintype.card V = 192)
    (hsum : (∑ x : V, halfExcess x) = 168) :
    24 ≤ ({x ∈ (Finset.univ : Finset V) | halfExcess x = 0}).card := by
  let nonzero := {x ∈ (Finset.univ : Finset V) | halfExcess x ≠ 0}
  have hnonzero_le : nonzero.card ≤ ∑ x : V, halfExcess x := by
    have hpoint : (∑ x : V, if halfExcess x ≠ 0 then 1 else 0) ≤
        ∑ x : V, halfExcess x := by
      apply Finset.sum_le_sum
      intro x _
      split_ifs <;> omega
    have hcount : (∑ x : V, if halfExcess x ≠ 0 then 1 else 0) =
        nonzero.card := by
      simpa [nonzero] using
        (Finset.sum_boole (R := ℕ) (fun x : V => halfExcess x ≠ 0)
          Finset.univ)
    omega
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun x : V => halfExcess x = 0) (s := Finset.univ)
  have hnot : ({x ∈ (Finset.univ : Finset V) | ¬halfExcess x = 0}) =
      nonzero := by
    ext x
    simp [nonzero]
  rw [hnot] at hpartition
  simp only [Finset.card_univ, hcard] at hpartition
  rw [hsum] at hnonzero_le
  omega

/-- Any 24 marked vertices distributed among four omitted types put at
least six marked vertices in one type. -/
theorem exists_six_le_type_fiber_of_twenty_four_le_card
    {V : Type*} [DecidableEq V]
    (S : Finset V) (type : V → Fin 4) (hS : 24 ≤ S.card) :
    ∃ e : Fin 4, 6 ≤ ({x ∈ S | type x = e}).card := by
  have hfibers : S.card = ∑ e : Fin 4, ({x ∈ S | type x = e}).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin 4))) (f := type) (by simp))
  by_contra h
  have hle : (∑ e : Fin 4, ({x ∈ S | type x = e}).card) ≤
      ∑ _e : Fin 4, 5 := by
    apply Finset.sum_le_sum
    intro e _
    have hnle : ¬6 ≤ ({x ∈ S | type x = e}).card := by
      intro he
      exact h ⟨e, he⟩
    omega
  simp at hle
  omega

/-- Six marked vertices distributed among the four orphan blocks of one
omitted type put two marked vertices in a common block. -/
theorem exists_two_le_block_fiber_of_six_le_card
    {V : Type*} [DecidableEq V]
    (S : Finset V) (block : V → Fin 4) (hS : 6 ≤ S.card) :
    ∃ o : Fin 4, 2 ≤ ({x ∈ S | block x = o}).card := by
  have hfibers : S.card = ∑ o : Fin 4, ({x ∈ S | block x = o}).card := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := S) (t := (Finset.univ : Finset (Fin 4))) (f := block) (by simp))
  by_contra h
  have hle : (∑ o : Fin 4, ({x ∈ S | block x = o}).card) ≤
      ∑ _o : Fin 4, 1 := by
    apply Finset.sum_le_sum
    intro o _
    have hnle : ¬2 ≤ ({x ∈ S | block x = o}).card := by
      intro ho
      exact h ⟨o, ho⟩
    omega
  simp at hle
  omega

end

end Erdos85
