import Proofs.Erdos85SecondOrderEvenDefect

/-!
# The combined defect graph at positive excess

For a regular C4-free graph of order `d(d-1)+3+e`, the union of the
beyond-distance-two relation and the triangle-free-edge relation is
`(e+2)`-regular.  The familiar cycle decomposition is precisely the
zero-excess specialization.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a regular C4-free graph, the triangle-free neighbors of a vertex and
the incidences inside its neighborhood partition its `d` neighbors. -/
theorem card_triangleFreeNeighbors_add_localDegreeSum_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) (x : V) :
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
  have hNcard : Fintype.card {z : V // z ∈ G.neighborSet x} = d := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) =
        G.neighborFinset x := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hreg x]
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

/-- **Positive-excess defect regularity.**  At order
`d(d-1)+3+e`, a regular C4-free graph has combined second-order defect
degree exactly `e+2` at every vertex. -/
theorem secondOrderDefectGraph_degree_eq_excess_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) : (secondOrderDefectGraph G).degree x = e + 2 := by
  rw [← (secondOrderDefectGraph G).card_neighborFinset_eq_degree,
    secondOrderDefectGraph_neighborFinset G x,
    Finset.card_union_of_disjoint
      (disjoint_antipodal_triangleFreeNeighbors G x)]
  rw [antipodalNeighbors, Finset.card_map]
  have hlocal := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
    G hfree hreg x
  have hid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  rw [hcard] at hid
  have hmul : d * d = d * (d - 1) + d := by
    by_cases hd0 : d = 0
    · simp [hd0]
    · have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
      calc
        d * d = d * ((d - 1) + 1) := by rw [Nat.sub_add_cancel hd1]
        _ = d * (d - 1) + d := by ring
  rw [hmul] at hid
  omega

/-- The zero-excess specialization recovers two-regularity without any
parity assumption. -/
theorem secondOrderDefectGraph_degree_eq_two_of_regular_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (x : V) : (secondOrderDefectGraph G).degree x = 2 := by
  apply secondOrderDefectGraph_degree_eq_excess_add_two
    G hfree hreg (e := 0)
  simpa using hcard

/-- Distinct pairs have no common neighbor exactly when they are adjacent in
the combined defect graph.  Otherwise C4-freeness forces exactly one common
neighbor.  This fact is independent of the graph order and of parity. -/
theorem card_common_eq_if_secondOrderDefect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (x y : V) (hxy : x ≠ y) :
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

/-- **Order-free defect matrix equation.**  For every regular C4-free graph,
`A² = (d-1)I + J - D`; positive excess changes the degree and geometry of
`D`, but not the operator identity. -/
theorem adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℤ * G.adjMatrix ℤ =
      (↑d - 1 : ℤ) • (1 : Matrix V V ℤ) +
        FriendshipTheoremOQ01.onesMatrix V -
          (secondOrderDefectGraph G).adjMatrix ℤ := by
  ext x y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply,
    smul_eq_mul]
  by_cases hxy : x = y
  · subst y
    rw [G.adjMatrix_mul_self_apply_self, hreg x]
    simp [SimpleGraph.adjMatrix_apply]
  · rw [adjMatrix_sq_apply_eq_card_common]
    have hcommon := card_common_eq_if_secondOrderDefect G hfree x y hxy
    by_cases hdefect : y ∈ (secondOrderDefectGraph G).neighborFinset x
    · rw [if_pos hdefect] at hcommon
      have hadj : (secondOrderDefectGraph G).Adj x y :=
        ((secondOrderDefectGraph G).mem_neighborFinset x y).mp hdefect
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]
    · rw [if_neg hdefect] at hcommon
      have hadj : ¬(secondOrderDefectGraph G).Adj x y := by
        intro hadj
        exact hdefect
          (((secondOrderDefectGraph G).mem_neighborFinset x y).mpr hadj)
      simp [SimpleGraph.adjMatrix_apply, hxy, hadj, hcommon]

/-- A square identity forces commutation with its defect term.  This is the
pure matrix principle behind both the regular-graph defect commutator and
the redundant `HA = AH` cuts in the zero-layer H-lift search. -/
theorem matrix_comm_of_sq_eq_smul_one_add_sub
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (H A J : Matrix V V K) (c : K)
    (hsq : H * H = c • (1 : Matrix V V K) + J - A)
    (hHJ : H * J = J * H) : H * A = A * H := by
  have hA : A = c • (1 : Matrix V V K) + J - H * H := by
    rw [hsq]
    noncomm_ring
  rw [hA, mul_sub, sub_mul, mul_add, add_mul, hHJ]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul]
  noncomm_ring

/-- The adjacency matrix commutes with the combined defect matrix at every
excess, not only when the latter is a two-factor. -/
theorem adjMatrix_comm_secondOrderDefect_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℤ * (secondOrderDefectGraph G).adjMatrix ℤ =
      (secondOrderDefectGraph G).adjMatrix ℤ * G.adjMatrix ℤ := by
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let C := (↑d - 1 : ℤ) • (1 : Matrix V V ℤ)
  have hsq : A * A = C + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
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

end

end Erdos85
