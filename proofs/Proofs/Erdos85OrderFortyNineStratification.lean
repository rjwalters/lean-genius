import Proofs.Erdos85DegreeExcessStratification
import Proofs.Erdos85PositiveExcessLocalParity

/-!
# The order-49, minimum-degree-seven laboratory

A hypothetical `C₄`-free graph on 49 vertices with minimum degree seven is
forced into two degree levels.  The local order-excess conservation law at
`q=6` determines the complete budget at each level, while the uniform parity
obstruction rules out the regular case.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At order 49 and minimum degree seven, every degree is seven or eight. -/
theorem orderFortyNine_degree_eq_seven_or_eight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) (x : V) :
    G.degree x = 7 ∨ G.degree x = 8 := by
  have hlocal :=
    secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
      G hfree (d := 7) (q := 6) (by norm_num) hmin (by omega) x
  have hx := hmin x
  omega

/-- A degree-eight vertex exhausts all six order-excess units in its own
weighted degree excess.  It therefore has defect degree zero and carries no
degree excess among its neighbors. -/
theorem orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 8) :
    (secondOrderDefectGraph G).degree x = 0 ∧
      neighborDegreeExcess G 7 x = 0 := by
  have hlocal :=
    secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
      G hfree (d := 7) (q := 6) (by norm_num) hmin (by omega) x
  omega

/-- In particular, every neighbor of a degree-eight vertex is tight. -/
theorem orderFortyNine_neighbor_degree_seven_of_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x y : V}
    (hx : G.degree x = 8) (hxy : G.Adj x y) :
    G.degree y = 7 := by
  have hzero :=
    (orderFortyNine_degreeEight_defectDegree_and_neighborExcess_zero
      G hfree hmin hcard hx).2
  rw [neighborDegreeExcess_eq_sum_neighborFinset] at hzero
  have hterms : ∀ z ∈ G.neighborFinset x, 0 ≤ G.degree z - 7 := by
    intro z _
    omega
  have hyMem : y ∈ G.neighborFinset x :=
    (G.mem_neighborFinset x y).mpr hxy
  have hyzero :=
    (Finset.sum_eq_zero_iff_of_nonneg hterms).mp hzero y hyMem
  have hylow := hmin y
  omega

/-- A degree-seven vertex divides its six units exactly between defect degree
and degree excess among its neighbors. -/
theorem orderFortyNine_degreeSeven_local_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 7) :
    (secondOrderDefectGraph G).degree x +
      neighborDegreeExcess G 7 x = 6 := by
  have hlocal :=
    secondOrderDefect_degree_add_weightedExcess_add_neighborExcess
      G hfree (d := 7) (q := 6) (by norm_num) hmin (by omega) x
  omega

/-- The regular alternative is impossible: it would be odd degree with even
second-order excess four.  Hence every hypothetical graph in the laboratory
contains a degree-eight vertex. -/
theorem orderFortyNine_exists_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    ∃ x : V, G.degree x = 8 := by
  by_contra hnone
  push_neg at hnone
  have hreg : ∀ x : V, G.degree x = 7 := by
    intro x
    rcases orderFortyNine_degree_eq_seven_or_eight
      G hfree hmin hcard x with hx | hx
    · exact hx
    · exact (hnone x hx).elim
  exact false_of_odd_degree_even_excess G hfree
    (d := 7) (e := 4) (by norm_num) (by norm_num) hreg (by omega)

/-- The total degree excess is literally the number `h` of degree-eight
vertices. -/
theorem orderFortyNine_sum_degreeExcess_eq_card_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (∑ x : V, (G.degree x - 7)) =
      (Finset.univ.filter fun x : V => G.degree x = 8).card := by
  calc
    (∑ x : V, (G.degree x - 7)) =
        ∑ x : V, if G.degree x = 8 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard x with hx | hx <;> simp [hx]
    _ = (Finset.univ.filter fun x : V => G.degree x = 8).card := by
      rw [← Finset.sum_filter]
      simp

/-- The square-excess sum is the same count, since every degree excess is
zero or one. -/
theorem orderFortyNine_sum_degreeExcess_sq_eq_card_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (∑ x : V, (G.degree x - 7) * (G.degree x - 7)) =
      (Finset.univ.filter fun x : V => G.degree x = 8).card := by
  calc
    (∑ x : V, (G.degree x - 7) * (G.degree x - 7)) =
        ∑ x : V, (G.degree x - 7) := by
      apply Finset.sum_congr rfl
      intro x _
      rcases orderFortyNine_degree_eq_seven_or_eight
        G hfree hmin hcard x with hx | hx <;> simp [hx]
    _ = _ := orderFortyNine_sum_degreeExcess_eq_card_degreeEight
      G hfree hmin hcard

/-- The degree-eight sector has odd cardinality, by the handshake lemma. -/
theorem orderFortyNine_card_degreeEight_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    Odd (Finset.univ.filter fun x : V => G.degree x = 8).card := by
  let h := (Finset.univ.filter fun x : V => G.degree x = 8).card
  have hexcess := orderFortyNine_sum_degreeExcess_eq_card_degreeEight
    G hfree hmin hcard
  have hsum : (∑ x : V, G.degree x) = 7 * 49 + h := by
    calc
      (∑ x : V, G.degree x) =
          ∑ x : V, (7 + (G.degree x - 7)) := by
        apply Finset.sum_congr rfl
        intro x _
        have hx := hmin x
        omega
      _ = 7 * Fintype.card V + ∑ x : V, (G.degree x - 7) := by
        rw [Finset.sum_add_distrib]
        simp [Nat.mul_comm]
      _ = 7 * 49 + h := by rw [hcard, hexcess]
  have hhand := G.sum_degrees_eq_twice_card_edges
  rw [hsum] at hhand
  apply Nat.odd_iff.mpr
  omega

/-- Global quadratic conservation bounds the odd high-degree sector by 21.
Equivalently, `2|E(D)| + 14h = 294`. -/
theorem orderFortyNine_card_degreeEight_le_twentyOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) :
    (Finset.univ.filter fun x : V => G.degree x = 8).card ≤ 21 := by
  have hglobal := two_mul_defectEdges_add_linearExcess_add_squareExcess_eq
    G hfree (d := 7) (q := 6) (by norm_num) hmin (by omega)
  have hsum := orderFortyNine_sum_degreeExcess_eq_card_degreeEight
    G hfree hmin hcard
  have hsquares := orderFortyNine_sum_degreeExcess_sq_eq_card_degreeEight
    G hfree hmin hcard
  rw [hcard, hsum, hsquares] at hglobal
  omega

/-- A degree-eight vertex has maximum possible common-neighbor conflict
degree: all 48 other vertices lie in its radius-two conflict layer. -/
theorem orderFortyNine_degree_commonNeighborConflict_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 8) :
    (commonNeighborConflict G).degree x = 48 := by
  rw [degree_commonNeighborConflict_eq_sum_neighbor_degree_sub_one
    G hfree x]
  have hneighbor : ∀ y : {z : V // z ∈ G.neighborSet x},
      G.degree y.1 = 7 := by
    intro y
    exact orderFortyNine_neighbor_degree_seven_of_degreeEight
      G hfree hmin hcard hx y.2
  calc
    (∑ y : {z : V // z ∈ G.neighborSet x}, (G.degree y.1 - 1)) =
        ∑ _y : {z : V // z ∈ G.neighborSet x}, 6 := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hneighbor y]
    _ = 8 * 6 := by
      rw [Finset.sum_const, Finset.card_univ,
        SimpleGraph.card_neighborSet_eq_degree, hx]
      simp
    _ = 48 := by norm_num

/-- Equivalently, the conflict neighborhood of a degree-eight vertex is the
entire punctured vertex set. -/
theorem orderFortyNine_conflictNeighborFinset_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 8) :
    (commonNeighborConflict G).neighborFinset x = Finset.univ.erase x := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    have hyAdj := ((commonNeighborConflict G).mem_neighborFinset x y).mp hy
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact hyAdj.ne.symm
  · rw [(commonNeighborConflict G).card_neighborFinset_eq_degree,
      orderFortyNine_degree_commonNeighborConflict_degreeEight
        G hfree hmin hcard hx,
      Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]

/-- Every edge incident to a degree-eight vertex lies in a triangle. -/
theorem orderFortyNine_triangleFreeNeighbors_degreeEight_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 8) :
    triangleFreeNeighbors G x = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hyData := (mem_triangleFreeNeighbors G x y).mp hy
  have hconflictSet := orderFortyNine_conflictNeighborFinset_degreeEight
    G hfree hmin hcard hx
  have hyErase : y ∈ (Finset.univ : Finset V).erase x := by
    simp [G.ne_of_adj hyData.1 |>.symm]
  have hyConflictMem : y ∈ (commonNeighborConflict G).neighborFinset x := by
    rw [hconflictSet]
    exact hyErase
  have hyConflict :=
    ((commonNeighborConflict G).mem_neighborFinset x y).mp hyConflictMem
  obtain ⟨z, hz⟩ := hyConflict.2
  have hzero := hyData.2
  rw [Finset.card_eq_zero] at hzero
  rw [hzero] at hz
  exact Finset.notMem_empty z hz

/-- Consequently the neighborhood induced by a degree-eight vertex is
1-regular: its eight neighbors form four disjoint triangle pairs. -/
theorem orderFortyNine_localNeighborhood_degree_eq_one_of_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x : V} (hx : G.degree x = 8)
    (y : {z : V // z ∈ G.neighborSet x}) :
    (G.induce (G.neighborSet x)).degree y = 1 := by
  have hle : (G.induce (G.neighborSet x)).degree y ≤ 1 := by
    rw [degree_induce_neighborSet_eq_card_common]
    exact common_le_one_of_not_containsC4 hfree x y.1
      (G.ne_of_adj y.2)
  have hne : (G.induce (G.neighborSet x)).degree y ≠ 0 := by
    intro hzero
    have hcommonzero :
        (G.neighborFinset x ∩ G.neighborFinset y.1).card = 0 := by
      rwa [degree_induce_neighborSet_eq_card_common] at hzero
    have hyTF : y.1 ∈ triangleFreeNeighbors G x :=
      (mem_triangleFreeNeighbors G x y.1).mpr ⟨y.2, hcommonzero⟩
    rw [orderFortyNine_triangleFreeNeighbors_degreeEight_eq_empty
      G hfree hmin hcard hx] at hyTF
    exact Finset.notMem_empty y.1 hyTF
  omega

/-- Distinct degree-eight vertices are nonadjacent. -/
theorem orderFortyNine_not_adj_degreeEight_degreeEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x y : V}
    (hx : G.degree x = 8) (hy : G.degree y = 8) :
    ¬ G.Adj x y := by
  intro hxy
  have hytight := orderFortyNine_neighbor_degree_seven_of_degreeEight
    G hfree hmin hcard hx hxy
  omega

/-- Every pair of distinct degree-eight vertices has exactly one common
degree-seven neighbor.  This is the pairwise-balanced-design core of the
order-49 laboratory. -/
theorem orderFortyNine_card_common_degreeEight_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49) {x y : V}
    (hx : G.degree x = 8) (_hy : G.degree y = 8) (hxy : x ≠ y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  have hconflictSet := orderFortyNine_conflictNeighborFinset_degreeEight
    G hfree hmin hcard hx
  have hyErase : y ∈ (Finset.univ : Finset V).erase x := by simp [hxy.symm]
  have hyConflictMem : y ∈ (commonNeighborConflict G).neighborFinset x := by
    rw [hconflictSet]
    exact hyErase
  have hnonempty :=
    (((commonNeighborConflict G).mem_neighborFinset x y).mp hyConflictMem).2
  have hpos : 0 < (G.neighborFinset x ∩ G.neighborFinset y).card :=
    Finset.card_pos.mpr hnonempty
  have hle := common_le_one_of_not_containsC4 hfree x y hxy
  omega

end

end Erdos85
