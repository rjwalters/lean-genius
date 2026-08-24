import Proofs.Erdos85ConnectedIncidenceBottleneckZeroRecurrence
import Proofs.Erdos85ConnectedClosedNeighborhoodEscape

/-!
# Connected incidence-bottleneck rows are nonzero

This file composes the two halves of the incidence route.  The algebraic
half says a zero bottleneck column forces the defect-square recurrence.  The
graph half says a connected regular square-order defect graph has an edge
escaping every closed neighborhood.  Evaluating the recurrence at the
outside endpoint of such an edge is impossible: its right side is zero,
whereas the escaping edge supplies a two-walk back to the center.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rational version of the standard common-neighbor square-entry formula. -/
theorem adjMatrix_sq_apply_eq_card_common_rat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) :
    (G.adjMatrix ℚ * G.adjMatrix ℚ) x y =
      ((G.neighborFinset x ∩ G.neighborFinset y).card : ℚ) := by
  have hz := adjMatrix_sq_apply_eq_card_common G x y
  calc
    (G.adjMatrix ℚ * G.adjMatrix ℚ) x y =
        ((G.adjMatrix ℤ * G.adjMatrix ℤ).map
          (Int.castRingHom ℚ)) x y := by
      rw [Matrix.map_mul]
      simp only [adjMatrix_map_intCast]
    _ = ((G.neighborFinset x ∩ G.neighborFinset y).card : ℚ) := by
      rw [Matrix.map_apply, hz]
      norm_cast

/-- An escaping edge contradicts the saturated defect-square recurrence at
the center basis vector. -/
theorem not_defect_recurrence_of_closedNeighborhood_escape
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {q : ℕ} (x u v : V)
    (hu : u = x ∨ D.Adj x u)
    (hvx : v ≠ x) (hvnot : ¬ D.Adj x v) (huv : D.Adj u v) :
    ¬ (D.adjMatrix ℚ * D.adjMatrix ℚ).mulVec (Pi.single x 1) =
      ((q : ℚ) - 2) • (D.adjMatrix ℚ).mulVec (Pi.single x 1) +
        ((q : ℚ) - 1) • Pi.single x 1 := by
  intro hrec
  have hux : u ≠ x := by
    intro h
    subst u
    exact hvnot huv
  have hxu : D.Adj x u := hu.resolve_left hux
  have huCommon :
      u ∈ D.neighborFinset v ∩ D.neighborFinset x := by
    exact Finset.mem_inter.mpr ⟨
      (D.mem_neighborFinset v u).mpr (D.adj_comm u v |>.mp huv),
      (D.mem_neighborFinset x u).mpr hxu⟩
  have hpos : 0 < (D.neighborFinset v ∩ D.neighborFinset x).card :=
    Finset.card_pos.mpr ⟨u, huCommon⟩
  have hi := congrFun hrec v
  simp only [Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul, if_neg hvx] at hi
  change (D.adjMatrix ℚ * D.adjMatrix ℚ) v x =
    ((q : ℚ) - 2) * (D.adjMatrix ℚ) v x + ((q : ℚ) - 1) * 0 at hi
  rw [adjMatrix_sq_apply_eq_card_common_rat D v x] at hi
  have hvnot' : ¬ D.Adj v x := by
    simpa [D.adj_comm] using hvnot
  simp [SimpleGraph.adjMatrix_apply, hvnot'] at hi
  rw [hi] at huCommon
  exact Finset.notMem_empty u huCommon

/-- In a connected regular square-order graph, no center basis vector can
satisfy the saturated defect recurrence. -/
theorem connected_regular_squareOrder_not_defect_recurrence
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (hconn : D.Connected) {q : ℕ} (hq : 2 ≤ q)
    (hreg : ∀ x, D.degree x = q - 1)
    (hcard : Fintype.card V = q * q) (x : V) :
    ¬ (D.adjMatrix ℚ * D.adjMatrix ℚ).mulVec (Pi.single x 1) =
      ((q : ℚ) - 2) • (D.adjMatrix ℚ).mulVec (Pi.single x 1) +
        ((q : ℚ) - 1) • Pi.single x 1 := by
  obtain ⟨u, hu, v, hvx, hvnot, huv⟩ :=
    connected_regular_squareOrder_exists_closedNeighborhood_escape
      D hconn hq hreg hcard x
  exact not_defect_recurrence_of_closedNeighborhood_escape
    D x u v hu hvx hvnot huv

/-- **Graph-facing nonvanishing capstone.**  For a connected square-order
second-order defect graph, every basis column of `E = AD-(J-A)` is nonzero. -/
theorem binarySquare_connected_incidenceBottleneck_mulVec_single_ne_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Connected) (x : V) :
    let A := G.adjMatrix ℚ
    let D := (secondOrderDefectGraph G).adjMatrix ℚ
    let J := ratOnesMatrix V
    let E := A * D - (J - A)
    E.mulVec (Pi.single x 1) ≠ 0 := by
  dsimp only
  let DG := secondOrderDefectGraph G
  let A := G.adjMatrix ℚ
  let D := DG.adjMatrix ℚ
  let J := ratOnesMatrix V
  let E := A * D - (J - A)
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ z : V, DG.degree z = q - 1 := by
    intro z
    have hz := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change DG.degree z = (q - 3) + 2 at hz
    omega
  intro hzero
  have hsq : A * A = ((q : ℚ) - 1) • (1 : Matrix V V ℚ) + J - D := by
    exact adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat G hfree hreg
  have hAJ : A * J = (q : ℚ) • J := by
    exact (adjMatrix_comm_ratOnesMatrix_of_regular G hreg).trans
      (ratOnesMatrix_mul_adjMatrix_of_regular G hreg)
  have hJD : J * D = ((q : ℚ) - 1) • J := by
    simpa [J, D, DG, Nat.cast_sub (by omega : 1 ≤ q)] using
      (ratOnesMatrix_mul_adjMatrix_of_regular DG hDreg)
  have hrec := defect_recurrence_of_incidenceBottleneck_zero
    A D J E q (Pi.single x 1) rfl hsq hAJ hJD hzero
  exact (connected_regular_squareOrder_not_defect_recurrence
    DG hconn (by omega) hDreg hcard x) hrec

end

end Erdos85

#print axioms Erdos85.adjMatrix_sq_apply_eq_card_common_rat
#print axioms Erdos85.not_defect_recurrence_of_closedNeighborhood_escape
#print axioms Erdos85.connected_regular_squareOrder_not_defect_recurrence
#print axioms Erdos85.binarySquare_connected_incidenceBottleneck_mulVec_single_ne_zero
