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

end

end Erdos85
