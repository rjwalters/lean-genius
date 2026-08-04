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

end

end Erdos85
