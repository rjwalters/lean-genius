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

end

end Erdos85
