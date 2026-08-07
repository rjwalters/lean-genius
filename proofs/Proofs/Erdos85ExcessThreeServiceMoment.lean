import Proofs.Erdos85ExcessThreeClawStructure
import Proofs.Erdos85PositiveExcessOnePincerService

/-!
# The excess-three service moment

This file runs the excess-one service-trace computation on the odd
excess-three stratum.  Writing `A` for the adjacency matrix, `T` for the
triangle-free color, `C` for the antipodal color, `D = C + T` for the
five-regular defect operator, and `a` for the size of the degree-three
triangle-free sector, the moment resolution of `A² = (d-1)·1 + J - D`
yields the exact identity

`tr(A T A C) + tr(T C²) = |V|(d+3) + (2d-6)a`.

The left side is the total antipodal service over the commutator slots
plus the mixed chord moment; at excess one the same computation produced
`tr(A M A C) + tr(M C²) = |V|(d+1)`, the demand jaw of the pincer.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The trace against the all-ones matrix records the degree sum. -/
theorem trace_adjMatrix_mul_onesMatrix_eq_sum_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    Matrix.trace (H.adjMatrix ℤ * FriendshipTheoremOQ01.onesMatrix V) =
      ∑ x : V, (H.degree x : ℤ) := by
  rw [Matrix.trace]
  apply Finset.sum_congr rfl
  intro x _
  simp only [Matrix.diag_apply, Matrix.mul_apply,
    FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, mul_one]
  exact sum_adjMatrix_row_eq_degree_int H x

/-- At odd excess three the triangle-free degree sum is the order plus
twice the degree-three sector size. -/
theorem excessThree_sum_triangleFreeDegrees_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
      (Fintype.card V : ℤ) + 2 *
        ((Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card : ℤ) := by
  have h := trace_adjMatrix_mul_secondOrderDefect_excessThree
    G hfree hd hodd hreg hcard
  rw [trace_adjMatrix_mul_secondOrderDefect_eq_sum_triangleFreeDegrees] at h
  exact h

/-- The mixed color moment `tr(T D)` is the triangle-free degree sum at
every excess. -/
theorem trace_triangleFree_mul_secondOrderDefect_eq_sum_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) =
      ∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ) := by
  rw [secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G,
    Matrix.mul_add, Matrix.trace_add,
    trace_triangleFree_mul_antipodal_eq_zero G, zero_add,
    trace_adjMatrix_sq_eq_sum_degrees]

/-- In the second defect moment of the triangle-free color, every word
except `T C²` vanishes at every excess. -/
theorem trace_triangleFree_mul_secondOrderDefect_sq_eq_antipodal_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) =
      Matrix.trace ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) := by
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  have hD : D = C + T :=
    secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hCTT : Matrix.trace (C * (T * T)) = 0 :=
    trace_antipodal_mul_triangleFree_sq_eq_zero G
  have hTTT : Matrix.trace (T * T * T) = 0 :=
    trace_triangleFreeEdgeGraph_cube_eq_zero G
  have hTCT : Matrix.trace (T * C * T) = 0 := by
    calc
      Matrix.trace (T * C * T) =
          Matrix.trace (T * (T * C)) := Matrix.trace_mul_comm (T * C) T
      _ = Matrix.trace ((T * T) * C) := by rw [← Matrix.mul_assoc]
      _ = Matrix.trace (C * (T * T)) := Matrix.trace_mul_comm _ _
      _ = 0 := hCTT
  have hTTC : Matrix.trace (T * T * C) = 0 := by
    calc
      Matrix.trace ((T * T) * C) =
          Matrix.trace (C * (T * T)) := Matrix.trace_mul_comm _ _
      _ = 0 := hCTT
  have hexpand :
      T * D * D = T * C * C + T * C * T + T * T * C + T * T * T := by
    rw [hD]
    noncomm_ring
  change Matrix.trace (T * D * D) = Matrix.trace (T * C * C)
  rw [hexpand, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    hTCT, hTTC, hTTT]
  ring

/-- **Excess-three service moment identity.**  The mixed fourth moment
controlling total antipodal service, together with the chord moment
`tr(T C²)`, is completely pinned by the degree-three sector size. -/
theorem excessThree_trace_serviceMoment_add_triangleFree_antipodal_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    let A := G.adjMatrix ℤ
    let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let a := (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card
    Matrix.trace (A * T * A * C) + Matrix.trace (T * C * C) =
      (Fintype.card V : ℤ) * ((d : ℤ) + 3) +
        (2 * (d : ℤ) - 6) * (a : ℤ) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let T := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  let a := (Finset.univ.filter fun x : V =>
    (triangleFreeEdgeGraph G).degree x = 3).card
  have hD : D = C + T :=
    secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hC : C = D - T := by rw [hD]; module
  have hcomm : A * D = D * A :=
    adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hA2 : A * A = ((d : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hTG : triangleFreeEdgeGraph G ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hdegsum : (∑ x : V, ((triangleFreeEdgeGraph G).degree x : ℤ)) =
      (Fintype.card V : ℤ) + 2 * (a : ℤ) :=
    excessThree_sum_triangleFreeDegrees_eq G hfree hd hodd hreg hcard
  have hTD : Matrix.trace (T * D) =
      (Fintype.card V : ℤ) + 2 * (a : ℤ) := by
    have h := trace_triangleFree_mul_secondOrderDefect_eq_sum_degrees G
    rw [hdegsum] at h
    exact h
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 5 := by
    intro x
    simpa using secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 3) (by omega) x
  have hDJ := FriendshipTheoremOQ01.adjMatrix_mul_ones
    (secondOrderDefectGraph G) 5 hDreg
  have hTDJ : Matrix.trace (T * D * J) =
      5 * ((Fintype.card V : ℤ) + 2 * (a : ℤ)) := by
    rw [Matrix.mul_assoc]
    change Matrix.trace (T * ((secondOrderDefectGraph G).adjMatrix ℤ *
      FriendshipTheoremOQ01.onesMatrix V)) = _
    rw [hDJ, Matrix.mul_smul, Matrix.trace_smul,
      trace_adjMatrix_mul_onesMatrix_eq_sum_degrees, hdegsum]
    push_cast
    ring
  have hTD2 : Matrix.trace (T * D * D) = Matrix.trace (T * C * C) :=
    trace_triangleFree_mul_secondOrderDefect_sq_eq_antipodal_sq G
  have hATAT : Matrix.trace (A * T * A * T) =
      (Fintype.card V : ℤ) + 14 * (a : ℤ) := by
    have halt := trace_adj_subgraph_adj_subgraph_eq_trace_subgraph_fourth
      G (triangleFreeEdgeGraph G) hfree hTG
    have h4 := trace_triangleFreeEdgeGraph_fourth_excessThree
      G hfree hd hodd hreg hcard
    dsimp only at h4
    calc
      Matrix.trace (A * T * A * T) =
          Matrix.trace ((A * T) * (A * T)) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace ((T * T) * (T * T)) := halt
      _ = (Fintype.card V : ℤ) + 14 * (a : ℤ) := h4
  have hcycle : Matrix.trace (A * T * A * D) =
      Matrix.trace (T * D * (A * A)) := by
    calc
      Matrix.trace (A * T * A * D) =
          Matrix.trace (A * (T * A * D)) := by
        congr 1
        noncomm_ring
      _ = Matrix.trace ((T * A * D) * A) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (T * D * (A * A)) := by
        congr 1
        calc
          T * A * D * A = T * (A * D) * A := by
            simp only [Matrix.mul_assoc]
          _ = T * (D * A) * A := by rw [hcomm]
          _ = T * D * (A * A) := by simp only [Matrix.mul_assoc]
  have hresolve : Matrix.trace (T * D * (A * A)) =
      ((d : ℤ) - 1) * Matrix.trace (T * D) +
        Matrix.trace (T * D * J) - Matrix.trace (T * D * D) := by
    rw [hA2]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add,
      Matrix.trace_smul]
    ring
  have hsplit : Matrix.trace (A * T * A * C) =
      Matrix.trace (A * T * A * D) - Matrix.trace (A * T * A * T) := by
    rw [hC]
    simp only [Matrix.mul_sub, Matrix.trace_sub]
  change Matrix.trace (A * T * A * C) + Matrix.trace (T * C * C) = _
  rw [hsplit, hcycle, hresolve, hTD, hTDJ, hTD2, hATAT]
  ring

end

end Erdos85
