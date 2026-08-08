import Proofs.Erdos85PositiveExcessOnePropagation

/-!
# Trace accounting for excess-one service slots

The number of double-service slots is controlled by a mixed fourth moment.
This file reduces that moment to the relative position of the perfect
matching and the antipodal two-factor.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The matching and antipodal colors are edge-disjoint, so their mixed
quadratic trace vanishes. -/
theorem trace_triangleFree_mul_antipodal_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj] :
    Matrix.trace
      ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (antipodalGraph G).adjMatrix ℤ) = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro x _
  change ((triangleFreeEdgeGraph G).adjMatrix ℤ *
    (antipodalGraph G).adjMatrix ℤ) x x = 0
  rw [(antipodalGraph G).mul_adjMatrix_apply]
  apply Finset.sum_eq_zero
  intro z hz
  rw [SimpleGraph.adjMatrix_apply, if_neg]
  intro ha
  have hzAnti : z ∈ antipodalNeighbors G x := by
    rw [← antipodalGraph_neighborFinset G x]
    exact hz
  have haTF : z ∈ triangleFreeNeighbors G x :=
    (triangleFreeEdgeGraph_adj G x z).mp ha
  exact (Finset.disjoint_left.mp
    (disjoint_antipodal_triangleFreeNeighbors G x))
      hzAnti haTF

/-- In odd excess one, `tr(MD)=|V|`. -/
theorem trace_triangleFree_mul_secondOrderDefect_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    Matrix.trace
      ((triangleFreeEdgeGraph G).adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) = Fintype.card V := by
  have hD := secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hM2 := triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_odd_excessOne
    G hfree hd hodd hreg hcard
  rw [hD, Matrix.mul_add, Matrix.trace_add,
    trace_triangleFree_mul_antipodal_eq_zero G, hM2, Matrix.trace_one]
  simp

/-- The mixed defect/constant-sector moment is `3|V|`. -/
theorem trace_triangleFree_mul_secondOrderDefect_mul_ones_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let J := FriendshipTheoremOQ01.onesMatrix V
    Matrix.trace (M * D * J) = 3 * Fintype.card V := by
  dsimp only
  have hMreg : ∀ x, (triangleFreeEdgeGraph G).degree x = 1 :=
    triangleFreeEdgeGraph_degree_eq_one_of_odd_excessOne
      G hfree hd hodd hreg hcard
  have hDreg : ∀ x, (secondOrderDefectGraph G).degree x = 3 := by
    intro x
    exact secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg (e := 1) (by simpa using hcard) x
  have hDJ := FriendshipTheoremOQ01.adjMatrix_mul_ones
    (secondOrderDefectGraph G) 3 hDreg
  have hMJ := FriendshipTheoremOQ01.adjMatrix_mul_ones
    (triangleFreeEdgeGraph G) 1 hMreg
  calc
    Matrix.trace
        ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          (secondOrderDefectGraph G).adjMatrix ℤ *
            FriendshipTheoremOQ01.onesMatrix V) =
      Matrix.trace
        ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          ((secondOrderDefectGraph G).adjMatrix ℤ *
            FriendshipTheoremOQ01.onesMatrix V)) := by
              rw [Matrix.mul_assoc]
    _ = Matrix.trace
        ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          ((3 : ℤ) • FriendshipTheoremOQ01.onesMatrix V)) := by
      exact congrArg
        (fun Q => Matrix.trace
          ((triangleFreeEdgeGraph G).adjMatrix ℤ * Q)) hDJ
    _ = Matrix.trace
        ((3 : ℤ) • ((triangleFreeEdgeGraph G).adjMatrix ℤ *
          FriendshipTheoremOQ01.onesMatrix V)) := by
      exact congrArg Matrix.trace
        (Matrix.mul_smul
          ((triangleFreeEdgeGraph G).adjMatrix ℤ) (3 : ℤ)
          (FriendshipTheoremOQ01.onesMatrix V))
    _ = Matrix.trace ((3 : ℤ) • FriendshipTheoremOQ01.onesMatrix V) := by
      rw [hMJ]
      simp
    _ = 3 * Fintype.card V := by
      simp [Matrix.trace, FriendshipTheoremOQ01.onesMatrix]
      ring

/-- After expanding `D=C+M`, every term of `tr(MD²)` except `tr(MC²)`
vanishes by cyclicity, `M²=I`, and looplessness. -/
theorem trace_triangleFree_mul_secondOrderDefect_sq_of_odd_excessOne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    Matrix.trace (M * D * D) = Matrix.trace (M * C * C) := by
  dsimp only
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  have hD : D = C + M :=
    secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hM2 : M * M = (1 : Matrix V V ℤ) :=
    triangleFreeEdgeGraph_adjMatrix_sq_eq_one_of_odd_excessOne
      G hfree hd hodd hreg hcard
  have hMCM : Matrix.trace (M * C * M) = 0 := by
    calc
      Matrix.trace (M * C * M) = Matrix.trace (M * (C * M)) := by
        rw [Matrix.mul_assoc]
      _ = Matrix.trace ((C * M) * M) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (C * (M * M)) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hM2]; simpa [C] using
        (SimpleGraph.trace_adjMatrix (α := ℤ) (antipodalGraph G))
  have hMMC : Matrix.trace (M * M * C) = 0 := by
    rw [hM2, Matrix.one_mul]
    simpa [C] using
      (SimpleGraph.trace_adjMatrix (α := ℤ) (antipodalGraph G))
  have hMMM : Matrix.trace (M * M * M) = 0 := by
    rw [hM2, Matrix.one_mul]
    simpa [M] using
      (SimpleGraph.trace_adjMatrix (α := ℤ) (triangleFreeEdgeGraph G))
  have hexpand :
      M * D * D = M * C * C + M * C * M + M * M * C + M * M * M := by
    rw [hD]
    noncomm_ring
  rw [hexpand, Matrix.trace_add, Matrix.trace_add, Matrix.trace_add,
    hMCM, hMMC, hMMM]
  simpa [M, C]

/-- **Service trace identity.**  The mixed fourth moment controlling total
service multiplicity is complementary to the number of matching endpoints
at antipodal distance two. -/
theorem trace_serviceMoment_add_matching_antipodal_sq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d)
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 4) :
    let A := G.adjMatrix ℤ
    let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    Matrix.trace (A * M * A * C) + Matrix.trace (M * C * C) =
      (Fintype.card V : ℤ) * ((d : ℤ) + 1) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let M := (triangleFreeEdgeGraph G).adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hD : D = C + M :=
    secondOrderDefectGraph_adjMatrix_eq_antipodal_add_triangleFree G
  have hC : C = D - M := by rw [hD]; module
  have hcomm : A * D = D * A :=
    adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hA2 : A * A =
      ((d : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hMD : Matrix.trace (M * D) = Fintype.card V :=
    trace_triangleFree_mul_secondOrderDefect_of_odd_excessOne
      G hfree hd hodd hreg hcard
  have hMDJ : Matrix.trace (M * D * J) = 3 * Fintype.card V :=
    trace_triangleFree_mul_secondOrderDefect_mul_ones_of_odd_excessOne
      G hfree hd hodd hreg hcard
  have hMD2 : Matrix.trace (M * D * D) = Matrix.trace (M * C * C) :=
    trace_triangleFree_mul_secondOrderDefect_sq_of_odd_excessOne
      G hfree hd hodd hreg hcard
  have hAMAM : Matrix.trace (A * M * A * M) = Fintype.card V := by
    simpa [A, M, Matrix.mul_assoc] using
      trace_adjMatrix_mul_triangleFreeEdgeGraph_sq_of_odd_excessOne
        G hfree hd hodd hreg hcard
  have hcycle : Matrix.trace (A * M * A * D) =
      Matrix.trace (M * D * (A * A)) := by
    calc
      Matrix.trace (A * M * A * D) =
          Matrix.trace (A * (M * A * D)) := by
            congr 1
            noncomm_ring
      _ = Matrix.trace ((M * A * D) * A) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (M * D * (A * A)) := by
        congr 1
        calc
          M * A * D * A = M * (A * D) * A := by
            simp only [Matrix.mul_assoc]
          _ = M * (D * A) * A := by rw [hcomm]
          _ = M * D * (A * A) := by simp only [Matrix.mul_assoc]
  have hresolve : Matrix.trace (M * D * (A * A)) =
      ((d : ℤ) - 1) * Matrix.trace (M * D) +
        Matrix.trace (M * D * J) - Matrix.trace (M * D * D) := by
    rw [hA2]
    simp only [Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_sub, Matrix.trace_add,
      Matrix.trace_smul]
    ring
  have hsplit : Matrix.trace (A * M * A * C) =
      Matrix.trace (A * M * A * D) - Matrix.trace (A * M * A * M) := by
    rw [hC]
    simp only [Matrix.mul_sub, Matrix.trace_sub]
  rw [hsplit, hcycle, hresolve, hMD, hMDJ, hMD2, hAMAM]
  push_cast
  ring

end

end Erdos85
