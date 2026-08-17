import Proofs.Erdos85BinarySquareCenteredOwnerCubicResolution

/-!
# Cubic trace of the binary square-order defect resolution

This computes the defect side of the centered-owner cubic resolution.  The
only non-scalar datum left is the number of closed defect walks of length
three, represented by `trace(D³)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cubic trace of `q ((q-1)I-D)`.  In particular, any partition-sensitive
owner-side cubic formula must balance against the defect triangle trace. -/
theorem binarySquare_regular_trace_defectResolution_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q) :
    let A := (secondOrderDefectGraph G).adjMatrix ℤ
    let R := (q : ℤ) •
      (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A)
    Matrix.trace ((R * R) * R) =
      (q : ℤ) ^ 3 *
        (((q : ℤ) ^ 2 * ((q : ℤ) - 1) ^ 2 * ((q : ℤ) + 2)) -
          Matrix.trace ((A * A) * A)) := by
  dsimp
  let D := secondOrderDefectGraph G
  let A := D.adjMatrix ℤ
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDreg : ∀ x : V, D.degree x = q - 1 := by
    intro x
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus x
    change D.degree x = (q - 3) + 2 at h
    omega
  have htrA : Matrix.trace A = 0 :=
    SimpleGraph.trace_adjMatrix (α := ℤ) D
  have htrA2 : Matrix.trace (A * A) =
      (Fintype.card V : ℤ) * ((q - 1 : ℕ) : ℤ) :=
    FriendshipTheoremOQ01.trace_adjMatrix_sq D (q - 1) hDreg
  have hexpand :
      ((((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A)) *
          ((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A))) *
          ((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A))) =
        ((q : ℤ) ^ 3 * (((q - 1 : ℕ) : ℤ) ^ 3)) •
            (1 : Matrix V V ℤ) -
          ((3 : ℤ) * (q : ℤ) ^ 3 * (((q - 1 : ℕ) : ℤ) ^ 2)) • A +
          ((3 : ℤ) * (q : ℤ) ^ 3 * ((q - 1 : ℕ) : ℤ)) • (A * A) -
          ((q : ℤ) ^ 3) • ((A * A) * A) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one,
      sub_mul, mul_sub, smul_sub, smul_smul]
    module
  change Matrix.trace
      (((((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A)) *
        ((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A))) *
        ((q : ℤ) • (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) - A)))) = _
  rw [hexpand, Matrix.trace_sub, Matrix.trace_add, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, htrA, htrA2, hcard]
  simp only [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
  push_cast
  ring

end

end Erdos85
