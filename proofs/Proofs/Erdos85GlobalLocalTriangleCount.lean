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

/-- Entrywise graph form of adjacency-matrix commutation.  It is the exact
mixed-neighbor balance used to compare the two sparse centers in one Stage-1
block when `H A = A H`. -/
theorem card_mixed_neighbor_inter_eq_of_adjMatrix_commute
    {V : Type*} [Fintype V] [DecidableEq V]
    (H A : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel A.Adj]
    (hcomm : H.adjMatrix ℤ * A.adjMatrix ℤ =
      A.adjMatrix ℤ * H.adjMatrix ℤ)
    (x z : V) :
    (H.neighborFinset x ∩ A.neighborFinset z).card =
      (A.neighborFinset x ∩ H.neighborFinset z).card := by
  have hentry := congrFun (congrFun hcomm x) z
  rw [H.adjMatrix_mul_apply, A.adjMatrix_mul_apply] at hentry
  simp only [SimpleGraph.adjMatrix_apply] at hentry
  rw [Finset.sum_boole, Finset.sum_boole] at hentry
  have hleft : (H.neighborFinset x).filter (fun y => A.Adj y z) =
      H.neighborFinset x ∩ A.neighborFinset z := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, A.adj_comm]
  have hright : (A.neighborFinset x).filter (fun y => H.Adj y z) =
      A.neighborFinset x ∩ H.neighborFinset z := by
    ext y
    simp [SimpleGraph.mem_neighborFinset, H.adj_comm]
  rw [hleft, hright] at hentry
  exact_mod_cast hentry

/-- Direct square-identity consumer: once `H² = cI + J - A` and `H`
commutes with `J`, the mixed-neighbor balance follows without separately
supplying `HA=AH`. -/
theorem card_mixed_neighbor_inter_eq_of_sq_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (H A : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel A.Adj]
    (J : Matrix V V ℤ) (c : ℤ)
    (hsq : H.adjMatrix ℤ * H.adjMatrix ℤ =
      c • (1 : Matrix V V ℤ) + J - A.adjMatrix ℤ)
    (hHJ : H.adjMatrix ℤ * J = J * H.adjMatrix ℤ)
    (x z : V) :
    (H.neighborFinset x ∩ A.neighborFinset z).card =
      (A.neighborFinset x ∩ H.neighborFinset z).card := by
  apply card_mixed_neighbor_inter_eq_of_adjMatrix_commute H A
  exact matrix_comm_of_sq_eq_smul_one_add_sub
    (H.adjMatrix ℤ) (A.adjMatrix ℤ) J c hsq hHJ

/-- If every `A`-edge joins a pair with disjoint `H`-neighborhoods, then
the mixed-count matrix `HA` vanishes on every `H`-edge. -/
theorem card_mixed_neighbor_inter_eq_zero_of_H_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (H A : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel A.Adj]
    (hzero : ∀ {u v : V}, A.Adj u v →
      Disjoint (H.neighborFinset u) (H.neighborFinset v))
    {x z : V} (hxz : H.Adj x z) :
    (H.neighborFinset x ∩ A.neighborFinset z).card = 0 := by
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hy' := Finset.mem_inter.mp hy
  have hAyZ : A.Adj y z := (A.adj_comm z y).mp <|
    (A.mem_neighborFinset z y).mp hy'.2
  have hdisjoint := hzero hAyZ
  exact (Finset.disjoint_left.mp hdisjoint)
    ((H.mem_neighborFinset y x).mpr ((H.adj_comm x y).mp
      ((H.mem_neighborFinset x y).mp hy'.1)))
    ((H.mem_neighborFinset z x).mpr ((H.adj_comm x z).mp hxz))

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

/-- Combined Stage-1 pigeonhole interface: among any 24 marked vertices,
there are two distinct marked vertices in the same omitted type and the same
one of its four orphan blocks.  This extracts the actual centers needed by
the same-block `A²` profile, rather than stopping at a fiber cardinality. -/
theorem exists_distinct_same_type_and_block_of_twenty_four_le_card
    {V : Type*} [DecidableEq V]
    (S : Finset V) (type block : V → Fin 4) (hS : 24 ≤ S.card) :
    ∃ e o : Fin 4, ∃ x ∈ S, ∃ z ∈ S,
      x ≠ z ∧ type x = e ∧ type z = e ∧ block x = o ∧ block z = o := by
  obtain ⟨e, he⟩ := exists_six_le_type_fiber_of_twenty_four_le_card
    S type hS
  let T := {x ∈ S | type x = e}
  obtain ⟨o, ho⟩ := exists_two_le_block_fiber_of_six_le_card T block he
  let U := {x ∈ T | block x = o}
  have hU : 1 < U.card := by
    change 1 < ({x ∈ T | block x = o}).card
    omega
  have hUne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hxU⟩ := hUne
  obtain ⟨z, hzU, hzx⟩ :=
    (Finset.one_lt_card_iff_nontrivial.mp hU).exists_ne x
  have hx : x ∈ S ∧ type x = e ∧ block x = o := by
    have hx' : (x ∈ S ∧ type x = e) ∧ block x = o := by
      simpa [U, T] using hxU
    exact ⟨hx'.1.1, hx'.1.2, hx'.2⟩
  have hz : z ∈ S ∧ type z = e ∧ block z = o := by
    have hz' : (z ∈ S ∧ type z = e) ∧ block z = o := by
      simpa [U, T] using hzU
    exact ⟨hz'.1.1, hz'.1.2, hz'.2⟩
  exact ⟨e, o, x, hx.1, z, hz.1, hzx.symm, hx.2.1, hz.2.1,
    hx.2.2, hz.2.2⟩

/-- End-to-end sparse-center consumer for the Stage-1 overlap ledger.  Odd
local overlap degrees with total 528 on 192 vertices force two distinct
degree-one centers in one orphan block of one omitted type. -/
theorem exists_same_block_overlap_degree_one_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (overlapDegree halfExcess : V → ℕ) (type block : V → Fin 4)
    (hcard : Fintype.card V = 192)
    (hodd : ∀ x, overlapDegree x = 2 * halfExcess x + 1)
    (hsum : (∑ x : V, overlapDegree x) = 528) :
    ∃ e o : Fin 4, ∃ x z : V,
      x ≠ z ∧ type x = e ∧ type z = e ∧ block x = o ∧ block z = o ∧
        overlapDegree x = 1 ∧ overlapDegree z = 1 := by
  have hhalf := sum_half_excess_eq_168_of_odd_overlap_degrees
    overlapDegree halfExcess hcard hodd hsum
  let S := {x ∈ (Finset.univ : Finset V) | halfExcess x = 0}
  have hS : 24 ≤ S.card := by
    apply twenty_four_le_card_zero_halfExcess_of_sum_eq_168
      halfExcess hcard hhalf
  obtain ⟨e, o, x, hxS, z, hzS, hxz, hxtype, hztype, hxblock,
      hzblock⟩ :=
    exists_distinct_same_type_and_block_of_twenty_four_le_card
      S type block hS
  have hxzero : halfExcess x = 0 := by simpa [S] using hxS
  have hzzero : halfExcess z = 0 := by simpa [S] using hzS
  refine ⟨e, o, x, z, hxz, hxtype, hztype, hxblock, hzblock, ?_, ?_⟩
  · rw [hodd x, hxzero]
  · rw [hodd z, hzzero]

/-- The pointwise mixed-row sum 455 and squared norm 1255 are equivalently
a shifted-product deviation budget of 132 around the two central values
two and three. -/
theorem sum_shifted_mixedCount_product_eq_132
    {V : Type*} [Fintype V] (mixedCount : V → ℤ)
    (hcard : Fintype.card V = 192)
    (hsum : (∑ z : V, mixedCount z) = 455)
    (hsq : (∑ z : V, mixedCount z * mixedCount z) = 1255) :
    (∑ z : V, (mixedCount z - 2) * (mixedCount z - 3)) = 132 := by
  calc
    (∑ z : V, (mixedCount z - 2) * (mixedCount z - 3)) =
        ∑ z : V, (mixedCount z * mixedCount z - 5 * mixedCount z + 6) := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = (∑ z : V, mixedCount z * mixedCount z) -
        5 * (∑ z : V, mixedCount z) + 6 * Fintype.card V := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    _ = 132 := by rw [hsq, hsum, hcard]; norm_num

/-- Hence at least 126 entries of every integral mixed-count
row are exactly two or three. -/
theorem one_hundred_twenty_six_le_card_mixedCount_eq_two_or_three
    {V : Type*} [Fintype V] [DecidableEq V] (mixedCount : V → ℤ)
    (hcard : Fintype.card V = 192)
    (hbudget : (∑ z : V,
      (mixedCount z - 2) * (mixedCount z - 3)) = 132) :
    126 ≤ ({z ∈ (Finset.univ : Finset V) |
      mixedCount z = 2 ∨ mixedCount z = 3}).card := by
  let bad := {z ∈ (Finset.univ : Finset V) |
    mixedCount z ≠ 2 ∧ mixedCount z ≠ 3}
  have hpoint : (∑ z : V, if z ∈ bad then 2 else 0) ≤
      ∑ z : V, (mixedCount z - 2) * (mixedCount z - 3) := by
    apply Finset.sum_le_sum
    intro z _
    by_cases hz : z ∈ bad
    · simp only [hz, if_true]
      have hz' : mixedCount z ≠ 2 ∧ mixedCount z ≠ 3 := by
        simpa [bad] using hz
      have hcases : mixedCount z ≤ 1 ∨ 4 ≤ mixedCount z := by omega
      rcases hcases with hle | hge <;> nlinarith
    · simp only [hz, if_false]
      have hz' : mixedCount z = 2 ∨ mixedCount z = 3 := by
        by_cases htwo : mixedCount z = 2
        · exact Or.inl htwo
        · right
          by_contra hthree
          exact hz (by simp [bad, htwo, hthree])
      rcases hz' with hz' | hz' <;> simp [hz']
  have hbadZ : 2 * (bad.card : ℤ) ≤ 132 := by
    have hcount : (∑ z : V, if z ∈ bad then (2 : ℤ) else 0) =
        2 * (bad.card : ℤ) := by
      rw [← Finset.sum_filter]
      simp [bad, mul_comm]
    calc
      2 * (bad.card : ℤ) =
          ∑ z : V, if z ∈ bad then (2 : ℤ) else 0 := hcount.symm
      _ ≤ ∑ z : V, (mixedCount z - 2) * (mixedCount z - 3) := hpoint
      _ = 132 := hbudget
  have hbad : 2 * bad.card ≤ 132 := by exact_mod_cast hbadZ
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset V))
    (p := fun z => mixedCount z = 2 ∨ mixedCount z = 3)
  have hnot : ({z ∈ (Finset.univ : Finset V) |
      ¬(mixedCount z = 2 ∨ mixedCount z = 3)}) = bad := by
    ext z
    simp [bad]
  rw [hnot, Finset.card_univ, hcard] at hpartition
  omega

/-- Thirteen forced zeros use 78 units of the shifted budget.  A further
entry at least ten would use at least 56, exceeding the total budget 132.
Thus every nonnegative mixed count is at most nine. -/
theorem mixedCount_le_nine_of_thirteen_zeros
    {V : Type*} [Fintype V] [DecidableEq V] (mixedCount : V → ℤ)
    (hbudget : (∑ z : V,
      (mixedCount z - 2) * (mixedCount z - 3)) = 132)
    (Z : Finset V) (hZcard : 13 ≤ Z.card)
    (hzero : ∀ z ∈ Z, mixedCount z = 0) (z : V) :
    mixedCount z ≤ 9 := by
  by_contra hnot
  have hten : 10 ≤ mixedCount z := by omega
  have hznot : z ∉ Z := by
    intro hz
    have := hzero z hz
    omega
  let cost := fun u : V => (mixedCount u - 2) * (mixedCount u - 3)
  have hcost_nonneg : ∀ u, 0 ≤ cost u := by
    intro u
    have hcases : mixedCount u ≤ 2 ∨ 3 ≤ mixedCount u := by omega
    rcases hcases with hle | hge <;> dsimp [cost] <;> nlinarith
  have hpoint : ∀ u : V,
      (if u ∈ Z then (6 : ℤ) else if u = z then 56 else 0) ≤ cost u := by
    intro u
    by_cases huZ : u ∈ Z
    · simp [huZ, cost, hzero u huZ]
    · by_cases huz : u = z
      · subst u
        simp only [huZ, ↓reduceIte]
        dsimp [cost]
        nlinarith
      · simp [huZ, huz, hcost_nonneg u]
  have hlower : (∑ u : V,
      if u ∈ Z then (6 : ℤ) else if u = z then 56 else 0) ≤ 132 := by
    calc
      _ ≤ ∑ u : V, cost u := by
        apply Finset.sum_le_sum
        intro u _
        exact hpoint u
      _ = 132 := hbudget
  have heval : (∑ u : V,
      if u ∈ Z then (6 : ℤ) else if u = z then 56 else 0) =
      6 * Z.card + 56 := by
    calc
      _ = ∑ u : V, ((if u ∈ Z then (6 : ℤ) else 0) +
          (if u = z then 56 else 0)) := by
        apply Finset.sum_congr rfl
        intro u _
        by_cases huZ : u ∈ Z
        · have huz : u ≠ z := by
            intro huz
            subst u
            exact hznot huZ
          simp [huZ, huz]
        · simp [huZ]
      _ = (∑ u : V, if u ∈ Z then (6 : ℤ) else 0) +
          ∑ u : V, if u = z then 56 else 0 := Finset.sum_add_distrib
      _ = 6 * Z.card + 56 := by simp [mul_comm]
  rw [heval] at hlower
  exact (by omega)

end

end Erdos85
