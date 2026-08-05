import Proofs.Erdos85SecondOrderStructure
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# The even second-order combined defect graph

At order `d(d-1)+3` with even `d`, distant nonedges and triangle-free edges
together form a spanning two-regular graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The triangle-free-edge count and local degree sum partition the `d`
neighbors of a center. -/
theorem card_triangleFreeNeighbors_add_localDegreeSum_of_secondOrder
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) :
    (triangleFreeNeighbors G x).card +
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d := by
  classical
  let H := G.induce (G.neighborSet x)
  let S := ∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y
  have hle : ∀ y : {z : V // z ∈ G.neighborSet x}, H.degree y ≤ 1 := by
    intro y
    change (G.induce (G.neighborSet x)).degree y ≤ 1
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree x y.1 (G.ne_of_adj y.2)
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hdeg := degree_eq_of_minDegree_card_lt_nextMooreLayer
    G hfree (by omega) hmin hbelow x
  have hNcard : Fintype.card {z : V // z ∈ G.neighborSet x} = d := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hdeg]
  have hnonzero : S =
      (Finset.univ.filter fun y : {z : V // z ∈ G.neighborSet x} =>
        H.degree y ≠ 0).card := by
    change (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) = _
    calc
      (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
          (∑ y : {z : V // z ∈ G.neighborSet x},
            if H.degree y ≠ 0 then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        have hy := hle y
        split_ifs <;> omega
      _ = _ := by simpa using
        (Finset.sum_boole (R := ℕ)
          (fun y : {z : V // z ∈ G.neighborSet x} => H.degree y ≠ 0)
          Finset.univ)
  have hpartition := Finset.card_filter_add_card_filter_not
    (fun y : {z : V // z ∈ G.neighborSet x} => H.degree y = 0)
    (s := Finset.univ)
  have hnot : (Finset.univ.filter fun y : {z : V // z ∈ G.neighborSet x} =>
      ¬H.degree y = 0) =
      Finset.univ.filter fun y => H.degree y ≠ 0 := by
    ext y
    simp
  rw [hnot] at hpartition
  simp only [Finset.card_univ, hNcard] at hpartition
  have hisolated :
      (Finset.univ.filter fun y : {z : V // z ∈ G.neighborSet x} =>
        H.degree y = 0).card + S = d := by
    rw [hnonzero]
    exact hpartition
  rw [triangleFreeNeighbors, Finset.card_map]
  simpa [triangleFreeNeighborIndices, H, S] using hisolated

/-- Union of the two zero-common-neighbor defect relations. -/
def secondOrderDefectGraph
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : SimpleGraph V :=
  antipodalGraph G ⊔ triangleFreeEdgeGraph G

noncomputable instance secondOrderDefectGraph.instDecidableAdj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    DecidableRel (secondOrderDefectGraph G).Adj := Classical.decRel _

/-- Its neighborhood is the disjoint union of distant vertices and
triangle-free neighbors. -/
theorem secondOrderDefectGraph_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (x : V) :
    (secondOrderDefectGraph G).neighborFinset x =
      antipodalNeighbors G x ∪ triangleFreeNeighbors G x := by
  ext y
  simp [secondOrderDefectGraph, SimpleGraph.mem_neighborFinset,
    antipodalGraph_adj, triangleFreeEdgeGraph_adj]

/-- The two defect neighborhoods are disjoint because one consists of
nonneighbors and the other of neighbors. -/
theorem disjoint_antipodal_triangleFreeNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    Disjoint (antipodalNeighbors G x) (triangleFreeNeighbors G x) := by
  rw [Finset.disjoint_left]
  intro y hyA hyT
  exact ((mem_antipodalNeighbors G x y).mp hyA).2.1
    ((mem_triangleFreeNeighbors G x y).mp hyT).1

/-- Three triangle-free edges of `G` cannot form a triangle: the third vertex
would be a common neighbor of the endpoints of the first edge. -/
theorem triangleFreeEdgeGraph_not_triangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {x y z : V}
    (hxy : (triangleFreeEdgeGraph G).Adj x y)
    (hyz : (triangleFreeEdgeGraph G).Adj y z)
    (hzx : (triangleFreeEdgeGraph G).Adj z x) : False := by
  have hxy' := (mem_triangleFreeNeighbors G x y).mp hxy
  have hyz' := (mem_triangleFreeNeighbors G y z).mp hyz
  have hzx' := (mem_triangleFreeNeighbors G z x).mp hzx
  have hzmem : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hzx'.1.symm, hyz'.1⟩
  rw [Finset.card_eq_zero.mp hxy'.2] at hzmem
  exact Finset.notMem_empty z hzmem

/-- If `G` is `C₄`-free, four triangle-free edges cannot form a simple
four-cycle. -/
theorem triangleFreeEdgeGraph_not_four_cycle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {a b c d : V}
    (hab : (triangleFreeEdgeGraph G).Adj a b)
    (hbc : (triangleFreeEdgeGraph G).Adj b c)
    (hcd : (triangleFreeEdgeGraph G).Adj c d)
    (hda : (triangleFreeEdgeGraph G).Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) (hba : b ≠ a)
    (hbc' : b ≠ c) (hda' : d ≠ a) (hdc : d ≠ c) : False := by
  apply hfree
  exact containsC4_of_rim
    ((mem_triangleFreeNeighbors G a b).mp hab).1
    ((mem_triangleFreeNeighbors G b c).mp hbc).1
    ((mem_triangleFreeNeighbors G c d).mp hcd).1
    ((mem_triangleFreeNeighbors G d a).mp hda).1
    hac hbd hba hbc' hda' hdc

/-- In the even second-order template the combined defect graph is
two-regular, independent of which of the two local vertex types occurs. -/
theorem secondOrderDefectGraph_degree_eq_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) : (secondOrderDefectGraph G).degree x = 2 := by
  rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    secondOrderDefectGraph_neighborFinset G x,
    Finset.card_union_of_disjoint
      (disjoint_antipodal_triangleFreeNeighbors G x)]
  rw [antipodalNeighbors, Finset.card_map]
  have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_secondOrder
    G hfree hd hmin hcard x
  rcases secondOrder_structure_of_even G hfree hd heven hmin hcard x with h | h
  · rw [h.2] at hsum
    rw [h.1]
    omega
  · rw [h.2] at hsum
    rw [h.1]
    omega

/-- The combined defect graph is literally a disjoint union of cycles: every
vertex, and hence every nonisolated vertex in the `IsCycles` interface, has
exactly two neighbors. -/
theorem secondOrderDefectGraph_isCycles
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    (secondOrderDefectGraph G).IsCycles := by
  intro x _
  rw [← Set.fintypeCard_eq_ncard]
  exact ((secondOrderDefectGraph G).card_neighborSet_eq_degree x).trans
    (secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard x)

/-- Every connected component of the second-order defect graph is traced by
a simple cycle whose vertex set is exactly that component. -/
theorem exists_secondOrderDefect_cycle_spanning_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {x : V}
    (hx : x ∈ c.supp) :
    ∃ p : (secondOrderDefectGraph G).Walk x x,
      p.IsCycle ∧ p.toSubgraph.verts = c.supp := by
  have hdeg := secondOrderDefectGraph_degree_eq_two
    G hfree hd heven hmin hcard x
  have hn : ((secondOrderDefectGraph G).neighborSet x).Nonempty :=
    (secondOrderDefectGraph G).neighborSet_nonempty.mpr
      (((secondOrderDefectGraph G).degree_pos x).mp (by omega))
  exact SimpleGraph.IsCycles.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp
    (secondOrderDefectGraph_isCycles G hfree hd heven hmin hcard) hx hn

/-- At each vertex the two defect edges have the same kind: either two
distant-pair edges and no triangle-free edges, or conversely. -/
theorem secondOrder_defect_local_monochromatic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) :
    ((antipodalNeighbors G x).card = 0 ∧
        (triangleFreeNeighbors G x).card = 2) ∨
      ((antipodalNeighbors G x).card = 2 ∧
        (triangleFreeNeighbors G x).card = 0) := by
  rw [antipodalNeighbors, Finset.card_map]
  have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_secondOrder
    G hfree hd hmin hcard x
  rcases secondOrder_structure_of_even G hfree hd heven hmin hcard x with h | h
  · left
    refine ⟨h.1, ?_⟩
    rw [h.2] at hsum
    omega
  · right
    refine ⟨h.1, ?_⟩
    rw [h.2] at hsum
    omega

/-- Any two defect edges incident to the same vertex belong to the same
summand.  Consequently this coloring propagates around every defect cycle. -/
theorem secondOrderDefectGraph_incident_edges_monochromatic
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {x y z : V}
    (hxy : (secondOrderDefectGraph G).Adj x y)
    (hxz : (secondOrderDefectGraph G).Adj x z) :
    ((antipodalGraph G).Adj x y ∧ (antipodalGraph G).Adj x z) ∨
      ((triangleFreeEdgeGraph G).Adj x y ∧
        (triangleFreeEdgeGraph G).Adj x z) := by
  have hy : y ∈ antipodalNeighbors G x ∪ triangleFreeNeighbors G x := by
    rw [← secondOrderDefectGraph_neighborFinset G x]
    exact ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hxy
  have hz : z ∈ antipodalNeighbors G x ∪ triangleFreeNeighbors G x := by
    rw [← secondOrderDefectGraph_neighborFinset G x]
    exact ((secondOrderDefectGraph G).mem_neighborFinset x z).mpr hxz
  rcases secondOrder_defect_local_monochromatic
      G hfree hd heven hmin hcard x with h | h
  · right
    have hA : antipodalNeighbors G x = ∅ := Finset.card_eq_zero.mp h.1
    rw [hA] at hy hz
    simpa [triangleFreeEdgeGraph_adj] using And.intro hy hz
  · left
    have hT : triangleFreeNeighbors G x = ∅ := Finset.card_eq_zero.mp h.2
    rw [hT] at hy hz
    simpa [antipodalGraph_adj] using And.intro hy hz

/-- Distinct pairs have no common neighbor precisely on the combined defect
graph, and have one common neighbor otherwise. -/
theorem card_common_eq_if_secondOrderDefect_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x y : V) (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card =
      if y ∈ (secondOrderDefectGraph G).neighborFinset x then 0 else 1 := by
  classical
  rw [secondOrderDefectGraph_neighborFinset G x]
  by_cases hdefect : y ∈ antipodalNeighbors G x ∪ triangleFreeNeighbors G x
  · rw [if_pos hdefect]
    rcases Finset.mem_union.mp hdefect with hanti | htri
    · exact ((mem_antipodalNeighbors G x y).mp hanti).2.2
    · exact ((mem_triangleFreeNeighbors G x y).mp htri).2
  · rw [if_neg hdefect]
    have hupper := common_le_one_of_not_containsC4 hfree x y hxy
    apply le_antisymm hupper
    by_contra hnot
    have hzero : (G.neighborFinset x ∩ G.neighborFinset y).card = 0 := by omega
    by_cases hadj : G.Adj x y
    · exact hdefect (Finset.mem_union_right _
        ((mem_triangleFreeNeighbors G x y).mpr ⟨hadj, hzero⟩))
    · exact hdefect (Finset.mem_union_left _
        ((mem_antipodalNeighbors G x y).mpr ⟨hxy.symm, hadj, hzero⟩))

/-- **Even second-order matrix equation.**  If `D` is the combined
two-factor of distant pairs and triangle-free edges, then
`A² = (d-1)I + J - D`. -/
theorem adjMatrix_sq_eq_sub_secondOrderDefect_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V -
          (secondOrderDefectGraph G).adjMatrix ℤ := by
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by omega) hmin hbelow
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply,
    smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    rw [G.adjMatrix_mul_self_apply_self, hreg x]
    simp [SimpleGraph.adjMatrix_apply]
  · rw [adjMatrix_sq_apply_eq_card_common]
    have hcommon := card_common_eq_if_secondOrderDefect_of_even
      G hfree hd heven hmin hcard x y hxy
    by_cases hdefect : y ∈ (secondOrderDefectGraph G).neighborFinset x
    · rw [if_pos hdefect] at hcommon
      have hadj : (secondOrderDefectGraph G).Adj x y :=
        ((secondOrderDefectGraph G).mem_neighborFinset x y).mp hdefect
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]
    · rw [if_neg hdefect] at hcommon
      have hadj : ¬(secondOrderDefectGraph G).Adj x y := by
        intro hadj
        apply hdefect
        exact ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hadj
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]

/-- The original adjacency matrix commutes with the combined defect
two-factor.  Thus the cycle decomposition of the defect graph is available
to spectral arguments. -/
theorem adjMatrix_comm_secondOrderDefect_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ := by
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let C := (↑d - 1 : ℤ) • (1 : Matrix V V ℤ)
  have hsq : A * A = C + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_even
      G hfree hd heven hmin hcard
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by omega) hmin hbelow
  have hAJ : A * J = (d : ℤ) • J :=
    FriendshipTheoremOQ01.adjMatrix_mul_ones G d hreg
  have hJA : J * A = (d : ℤ) • J :=
    onesMatrix_mul_adjMatrix_of_regular G d hreg
  have hD : D = C + J - A * A := by
    rw [hsq]
    noncomm_ring
  change A * D = D * A
  rw [hD, mul_sub, sub_mul, mul_add, add_mul, hAJ, hJA]
  simp only [C, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
  noncomm_ring

/-- Entrywise form of `AD = DA`: the number of neighbors of `x` among the
two defect-neighbors of `y` equals the number of neighbors of `y` among the
two defect-neighbors of `x`.  This is the local recurrence used by the
commutation-aware finite classifier. -/
theorem card_filter_adj_defectNeighbors_comm_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x y : V) :
    (((secondOrderDefectGraph G).neighborFinset y).filter
          (fun z => G.Adj x z)).card =
      (((secondOrderDefectGraph G).neighborFinset x).filter
          (fun z => G.Adj z y)).card := by
  let D := secondOrderDefectGraph G
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even
    G hfree hd heven hmin hcard
  have hentry := congrFun (congrFun hcomm x) y
  change (G.adjMatrix ℤ * D.adjMatrix ℤ) x y =
    (D.adjMatrix ℤ * G.adjMatrix ℤ) x y at hentry
  rw [D.mul_adjMatrix_apply, D.adjMatrix_mul_apply] at hentry
  simp only [SimpleGraph.adjMatrix_apply, Finset.sum_boole,
    Int.ofNat_inj] at hentry
  simpa [D] using hentry

/-- Over the rationals, `(d-1)I-D` is nonsingular.  Strict diagonal
dominance is enough: its diagonal has size at least three and each row has
exactly two off-diagonal unit entries. -/
theorem secondOrder_scalar_sub_defect_det_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    Matrix.det ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
      (secondOrderDefectGraph G).adjMatrix ℚ) ≠ 0 := by
  let D := secondOrderDefectGraph G
  let B := (d - 1 : ℚ) • (1 : Matrix V V ℚ) - D.adjMatrix ℚ
  apply det_ne_zero_of_sum_row_lt_diag
  intro x
  have hdegree : D.degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard x
  have hoff : ∑ y ∈ Finset.univ.erase x, ‖B x y‖ = (2 : ℝ) := by
    change ∑ y ∈ Finset.univ.erase x,
      ‖((d - 1 : ℚ) • (1 : Matrix V V ℚ) - D.adjMatrix ℚ) x y‖ = _
    calc
      _ = ∑ y ∈ Finset.univ.erase x, if D.Adj x y then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        have hne : x ≠ y := by
          simpa using (Finset.mem_erase.mp hy).1.symm
        simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
          SimpleGraph.adjMatrix_apply, hne, if_false, smul_eq_mul,
          mul_zero, zero_sub]
        by_cases hadj : D.Adj x y <;> simp [hadj]
      _ = ((Finset.univ.erase x).filter (fun y => D.Adj x y)).card := by
        simpa using (Finset.sum_boole (R := ℝ)
          (fun y : V => D.Adj x y) (Finset.univ.erase x))
      _ = 2 := by
        congr 1
        have hfilt : (Finset.univ.erase x).filter (fun y => D.Adj x y) =
            D.neighborFinset x := by
          ext y
          simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
            and_true, SimpleGraph.mem_neighborFinset]
          constructor
          · exact fun h => h.2
          · intro hadj
            exact ⟨(D.ne_of_adj hadj).symm, hadj⟩
        rw [hfilt, D.card_neighborFinset_eq_degree, hdegree]
  rw [hoff]
  change (2 : ℝ) < ‖B x x‖
  dsimp only [B]
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    SimpleGraph.adjMatrix_apply, D.loopless.irrefl, if_false, sub_zero,
    smul_eq_mul]
  simp only [if_pos, mul_one]
  rw [← Rat.norm_cast_real, Real.norm_eq_abs, abs_of_nonneg]
  · exact_mod_cast (show (2 : ℤ) < (d : ℤ) - 1 by omega)
  · exact_mod_cast (show (0 : ℤ) ≤ (d : ℤ) - 1 by omega)

/-- Exact rank-one determinant relation for the second-order defect
resolvent.  The factor on the all-ones direction is changed from `d-3` to
`d²`. -/
theorem secondOrder_defect_rankOne_det
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    (d - 3 : ℚ) * Matrix.det
        ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
          (secondOrderDefectGraph G).adjMatrix ℚ +
            Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ))) =
      (d : ℚ) ^ 2 * Matrix.det
        ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
          (secondOrderDefectGraph G).adjMatrix ℚ) := by
  let D := secondOrderDefectGraph G
  let B := (d - 1 : ℚ) • (1 : Matrix V V ℚ) - D.adjMatrix ℚ
  let u : V → ℚ := fun _ => 1
  let c : ℚ := d - 3
  have hdet : B.det ≠ 0 :=
    secondOrder_scalar_sub_defect_det_ne_zero
      G hfree hd heven hmin hcard
  have hunit : IsUnit B.det := (isUnit_iff_ne_zero).mpr hdet
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B hunit
  have hBu : B.mulVec u = c • u := by
    funext x
    change (∑ y, B x y * 1) = c * 1
    simp only [mul_one]
    dsimp only [B, c]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
      SimpleGraph.adjMatrix_apply, smul_eq_mul]
    rw [Finset.sum_sub_distrib]
    have hdiag : ∑ y : V, (d - 1 : ℚ) * (if x = y then 1 else 0) = d - 1 := by
      simp
    rw [hdiag, Finset.sum_boole]
    have hfilt : Finset.univ.filter (fun y => D.Adj x y) = D.neighborFinset x := by
      ext y
      simp [SimpleGraph.mem_neighborFinset]
    rw [hfilt, D.card_neighborFinset_eq_degree,
      secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard x]
    ring
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast (show (d : ℤ) - 3 ≠ 0 by omega)
  have hinvu : B⁻¹.mulVec u = c⁻¹ • u := by
    apply Matrix.inv_mulVec_eq_vec
    calc
      u = c⁻¹ • (c • u) := by
        ext x
        simp [hc]
      _ = c⁻¹ • B.mulVec u := by rw [hBu]
      _ = B.mulVec (c⁻¹ • u) := by rw [Matrix.mulVec_smul]
  have hJ : Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ)) =
      Matrix.replicateCol Unit u * Matrix.replicateRow Unit u := by
    ext x y
    simp [Matrix.mul_apply, u]
  change c * Matrix.det (B + Matrix.of (fun (_ : V) (_ : V) => (1 : ℚ))) =
    (d : ℚ) ^ 2 * B.det
  rw [hJ, Matrix.det_add_replicateCol_mul_replicateRow hunit]
  have hscalar :
      Matrix.det ((1 : Matrix Unit Unit ℚ) +
        Matrix.replicateRow Unit u * B⁻¹ * Matrix.replicateCol Unit u) =
        1 + (Fintype.card V : ℚ) * c⁻¹ := by
    rw [Matrix.mul_assoc, ← Matrix.replicateCol_mulVec, hinvu,
      Matrix.replicateRow_mul_replicateCol]
    rw [Matrix.det_unique]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply,
      if_pos, u, Pi.smul_apply, smul_eq_mul, one_mul]
    simp [dotProduct, c]
  rw [hscalar]
  have hn : (Fintype.card V : ℚ) =
      (d : ℚ) * ((d : ℚ) - 1) + 3 := by
    rw [hcard, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega)]
    norm_num
  rw [hn]
  field_simp [hc]
  ring

/-- The determinant of the defect resolvent is constrained by the square of
the original adjacency determinant:
`(d-3) det(A)^2 = d^2 det((d-1)I-D)`. -/
theorem secondOrder_defect_det_square
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    (d - 3 : ℚ) * Matrix.det (G.adjMatrix ℚ) ^ 2 =
      (d : ℚ) ^ 2 * Matrix.det
        ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
          (secondOrderDefectGraph G).adjMatrix ℚ) := by
  let A := G.adjMatrix ℚ
  let B := (d - 1 : ℚ) • (1 : Matrix V V ℚ) -
    (secondOrderDefectGraph G).adjMatrix ℚ
  let J : Matrix V V ℚ := Matrix.of fun _ _ => 1
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨e, rfl⟩ : ∃ e : ℕ, d = e + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hreg : ∀ x : V, G.degree x = d :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by omega) hmin hbelow
  have hsq : A * A = B + J := by
    ext x y
    dsimp only [A, B, J]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, Matrix.of_apply, smul_eq_mul]
    by_cases hxy : x = y
    · subst y
      rw [G.adjMatrix_mul_self_apply_self, hreg x]
      simp [SimpleGraph.adjMatrix_apply]
    · have hsquare :
          (G.adjMatrix ℚ * G.adjMatrix ℚ) x y =
            ((G.neighborFinset x ∩ G.neighborFinset y).card : ℚ) := by
        rw [G.adjMatrix_mul_apply]
        simp only [SimpleGraph.adjMatrix_apply]
        rw [Finset.sum_boole]
        have hfilt : (G.neighborFinset x).filter (fun z => G.Adj z y) =
            G.neighborFinset x ∩ G.neighborFinset y := by
          ext z
          simp [SimpleGraph.mem_neighborFinset, G.adj_comm]
        rw [hfilt]
      rw [hsquare]
      have hcommon := card_common_eq_if_secondOrderDefect_of_even
        G hfree hd heven hmin hcard x y hxy
      by_cases hdefect : y ∈ (secondOrderDefectGraph G).neighborFinset x
      · rw [if_pos hdefect] at hcommon
        have hadj : (secondOrderDefectGraph G).Adj x y :=
          ((secondOrderDefectGraph G).mem_neighborFinset x y).mp hdefect
        simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]
      · rw [if_neg hdefect] at hcommon
        have hadj : ¬(secondOrderDefectGraph G).Adj x y := by
          intro hadj
          apply hdefect
          exact ((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hadj
        simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]
  have hrank := secondOrder_defect_rankOne_det
    G hfree hd heven hmin hcard
  change (d - 3 : ℚ) * A.det ^ 2 = (d : ℚ) ^ 2 * B.det
  calc
    (d - 3 : ℚ) * A.det ^ 2 =
        (d - 3 : ℚ) * Matrix.det (A * A) := by
      rw [Matrix.det_mul, pow_two]
    _ = (d - 3 : ℚ) * Matrix.det (B + J) := by rw [hsq]
    _ = (d : ℚ) ^ 2 * B.det := hrank

/-- Equivalently, after removing the one all-ones eigenvalue, the defect
resolvent determinant is `(d-3)` times a rational square. -/
theorem secondOrder_defect_resolvent_is_square_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    ∃ q : ℚ,
      Matrix.det ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
        (secondOrderDefectGraph G).adjMatrix ℚ) = (d - 3 : ℚ) * q ^ 2 := by
  let a := Matrix.det (G.adjMatrix ℚ)
  let b := Matrix.det ((d - 1 : ℚ) • (1 : Matrix V V ℚ) -
    (secondOrderDefectGraph G).adjMatrix ℚ)
  have h := secondOrder_defect_det_square G hfree hd heven hmin hcard
  have hd0 : (d : ℚ) ≠ 0 := by positivity
  refine ⟨a / d, ?_⟩
  change b = (d - 3 : ℚ) * (a / d) ^ 2
  change (d - 3 : ℚ) * a ^ 2 = (d : ℚ) ^ 2 * b at h
  field_simp [hd0]
  nlinarith

end

end Erdos85
