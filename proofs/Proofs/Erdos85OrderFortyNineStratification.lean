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

end

end Erdos85
