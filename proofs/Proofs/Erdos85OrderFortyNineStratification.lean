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

end

end Erdos85
