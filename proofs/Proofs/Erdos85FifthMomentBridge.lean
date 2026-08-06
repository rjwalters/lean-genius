import Proofs.Erdos85DefectSecondMixedMoment

/-!
# Fifth-moment bridge for a regular defect operator

The square relation `A² = κI + J - D` determines the fifth adjacency
moment up to the first two mixed defect moments.  This is the colored
near-Moore analogue of the extra spectral-moment equation used by Brown in
the classical small-excess girth-five problem.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- Abstract fifth-moment expansion. -/
theorem trace_fifth_eq_of_sq_eq_scalar_add_ones_sub_defect
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D J : Matrix V V ℤ) (κ n r : ℤ)
    (hsq : A * A = κ • (1 : Matrix V V ℤ) + J - D)
    (hJJ : J * J = n • J)
    (hJD : J * D = r • J)
    (hDJ : D * J = r • J)
    (htraceA : Matrix.trace A = 0) :
    Matrix.trace (A * A * A * A * A) =
      (n + 2 * κ - 2 * r) * Matrix.trace (A * J) -
        2 * κ * Matrix.trace (A * D) +
          Matrix.trace (A * D * D) := by
  have hword : A * A * A * A * A = A * ((A * A) * (A * A)) := by
    noncomm_ring
  rw [hword, hsq]
  have hraw :
      A * ((κ • (1 : Matrix V V ℤ) + J - D) *
          (κ • (1 : Matrix V V ℤ) + J - D)) =
        κ • (κ • A) + κ • (A * J) + κ • (A * J) -
          κ • (A * D) - κ • (A * D) +
          A * (J * J) - A * (J * D) - A * (D * J) + A * D * D := by
    noncomm_ring
    module
  have hexpand :
      A * ((κ • (1 : Matrix V V ℤ) + J - D) *
          (κ • (1 : Matrix V V ℤ) + J - D)) =
        κ • (κ • A) + (n + 2 * κ - 2 * r) • (A * J) -
          (2 * κ) • (A * D) + A * D * D := by
    rw [hraw, hJJ, hJD, hDJ]
    simp only [Matrix.mul_smul]
    module
  rw [hexpand]
  simp only [Matrix.trace_add, Matrix.trace_sub, Matrix.trace_smul]
  rw [htraceA]
  simp

/-- Graph-facing fifth-moment bridge at arbitrary nonnegative second-order
excess.  The only undetermined terms are the color trace `tr(AD)` and the
antipodal service moment `tr(AC²)`. -/
theorem trace_adjMatrix_fifth_eq_colorTrace_add_antipodalService
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) :
    let A := G.adjMatrix ℤ
    let C := (antipodalGraph G).adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    Matrix.trace (A * A * A * A * A) =
      ((Fintype.card V : ℤ) + 2 * ((d : ℤ) - 1) -
          2 * ((e : ℤ) + 2)) *
          ((d : ℤ) * (Fintype.card V : ℤ)) -
        2 * ((d : ℤ) - 1) * Matrix.trace (A * D) +
          Matrix.trace (A * C * C) := by
  dsimp only
  let A := G.adjMatrix ℤ
  let C := (antipodalGraph G).adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hregD : ∀ x, (secondOrderDefectGraph G).degree x = e + 2 := by
    intro x
    exact secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcard x
  have hsq : A * A = ((d : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hJJ : J * J = (Fintype.card V : ℤ) • J :=
    FriendshipTheoremOQ01.onesMatrix_sq
  have hJD : J * D = ((e : ℤ) + 2) • J := by
    simpa [D, J] using
      (onesMatrix_mul_adjMatrix_of_regular
        (secondOrderDefectGraph G) (e + 2) hregD)
  have hDJ : D * J = ((e : ℤ) + 2) • J := by
    simpa [D, J] using
      (FriendshipTheoremOQ01.adjMatrix_mul_ones
        (secondOrderDefectGraph G) (e + 2) hregD)
  have htraceA : Matrix.trace A = 0 := by
    exact SimpleGraph.trace_adjMatrix ℤ G
  have hbase := trace_fifth_eq_of_sq_eq_scalar_add_ones_sub_defect
    A D J ((d : ℤ) - 1) (Fintype.card V : ℤ) ((e : ℤ) + 2)
    hsq hJJ hJD hDJ htraceA
  have hAJ : A * J = (d : ℤ) • J := by
    simpa [A, J] using
      (FriendshipTheoremOQ01.adjMatrix_mul_ones G d hreg)
  have htraceJ : Matrix.trace J = (Fintype.card V : ℤ) :=
    FriendshipTheoremOQ01.trace_onesMatrix
  have hservice : Matrix.trace (A * D * D) = Matrix.trace (A * C * C) := by
    exact trace_adj_mul_secondOrderDefect_sq_eq_antipodal_sq G
  rw [hAJ, Matrix.trace_smul, htraceJ, hservice] at hbase
  simpa [smul_eq_mul] using hbase

/-- The cubic color partition requires only regularity, not an exact-boundary
parity hypothesis. -/
theorem trace_adjMatrix_cube_add_colorTrace_eq_card_mul_degree_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    Matrix.trace
        (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ) +
      Matrix.trace (G.adjMatrix ℤ *
        (secondOrderDefectGraph G).adjMatrix ℤ) =
      (Fintype.card V : ℤ) * d := by
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let J := FriendshipTheoremOQ01.onesMatrix V
  have hsq : A * A = ((d : ℤ) - 1) • (1 : Matrix V V ℤ) + J - D :=
    adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hJA : J * A = (d : ℤ) • J :=
    onesMatrix_mul_adjMatrix_of_regular G d hreg
  have hcube : A * A * A =
      ((d : ℤ) - 1) • A + (d : ℤ) • J - D * A := by
    rw [show A * A * A = (A * A) * A by rfl, hsq,
      Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
      Matrix.one_mul, hJA]
  change Matrix.trace (A * A * A) + Matrix.trace (A * D) = _
  rw [hcube, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_mul_comm D A]
  have htraceA : Matrix.trace A = 0 := SimpleGraph.trace_adjMatrix ℤ G
  have htraceJ : Matrix.trace J = (Fintype.card V : ℤ) :=
    FriendshipTheoremOQ01.trace_onesMatrix
  rw [htraceA, htraceJ]
  simp
  ring

/-- Algebraic endpoint for the forthcoming closed-walk count: any integer
`q₅` satisfying the standard length-five walk decomposition obeys the exact
five-cycle/antipodal-service equation. -/
theorem ten_mul_fiveCycleCount_eq_antipodalService_of_walk_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (q₅ : ℤ)
    (hwalk : Matrix.trace
        (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ *
          G.adjMatrix ℤ * G.adjMatrix ℤ) =
      10 * q₅ + 5 * ((d : ℤ) - 1) *
        Matrix.trace
          (G.adjMatrix ℤ * G.adjMatrix ℤ * G.adjMatrix ℤ)) :
    10 * q₅ =
      Matrix.trace
          (G.adjMatrix ℤ * (antipodalGraph G).adjMatrix ℤ *
            (antipodalGraph G).adjMatrix ℤ) +
        ((Fintype.card V : ℤ) - 3 * ((d : ℤ) - 1) -
            2 * ((e : ℤ) + 2)) *
            ((d : ℤ) * (Fintype.card V : ℤ)) +
          3 * ((d : ℤ) - 1) *
            Matrix.trace (G.adjMatrix ℤ *
              (secondOrderDefectGraph G).adjMatrix ℤ) := by
  have hfive := trace_adjMatrix_fifth_eq_colorTrace_add_antipodalService
    G hfree hreg hcard
  dsimp only at hfive
  have hcube :=
    trace_adjMatrix_cube_add_colorTrace_eq_card_mul_degree_of_regular
      G hfree hreg
  rw [hwalk] at hfive
  linear_combination hfive - 5 * ((d : ℤ) - 1) * hcube

end

end Erdos85
