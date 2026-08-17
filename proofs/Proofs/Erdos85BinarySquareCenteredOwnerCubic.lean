import Proofs.Erdos85BinarySquareCenteredOwnerResolution

/-!
# Cubic resolution of the centered owner sectors

The quadratic Parseval identity is only a Frobenius budget and is automatic
from the owner degrees.  The first moment that can see the self-indexed
diagonal blocks is the cubic one.  This file lifts pairwise centered-owner
annihilation to an exact additive cube identity, ready for triangle-count and
parity consumers in the surviving mixed-partition branch.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Abstract cubic Parseval identity for matrix summands selected by their
sum.  This is the next moment after `sum_matrix_sq_eq_sq_of_sum_eq_of_mul_sum_eq_sq`.
-/
theorem sum_matrix_cube_eq_cube_of_sum_eq_of_mul_sum_eq_sq
    {I V K : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    [CommRing K]
    (C : I → Matrix V V K) (R : Matrix V V K)
    (hsum : ∑ i, C i = R) (hselect : ∀ i, C i * R = C i * C i) :
    ∑ i, C i * C i * C i = R * R * R := by
  have hsq : ∑ i, C i * C i = R * R :=
    sum_matrix_sq_eq_sq_of_sum_eq_of_mul_sum_eq_sq C R hsum hselect
  calc
    ∑ i, C i * C i * C i = ∑ i, (C i * C i) * R := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        C i * C i * C i = C i * (C i * C i) := by rw [Matrix.mul_assoc]
        _ = C i * (C i * R) := by rw [hselect i]
        _ = (C i * C i) * R := by rw [Matrix.mul_assoc]
    _ = (∑ i, C i * C i) * R := by rw [Finset.sum_mul]
    _ = R * R * R := by rw [hsq]

/-- **Centered-owner cubic resolution.**  The cubes of the mutually
annihilating centered owner sectors add to the cube of the centered defect
operator.  Unlike the squared identity, tracing this formula retains the
triangle counts in each owner graph and in the defect graph. -/
theorem binarySquare_regular_sum_centeredOwnerGrams_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) :
    let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
      fun c =>
        (q : ℤ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m c : ℤ) • (1 : Matrix V V ℤ)) -
          (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    let R := (q : ℤ) •
      (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ)
    ∑ c, C c * C c * C c = R * R * R := by
  dsimp
  let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
    fun c =>
      (q : ℤ) •
          ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
            (m c : ℤ) • (1 : Matrix V V ℤ)) -
        (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
  let R : Matrix V V ℤ := (q : ℤ) •
    (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
      (secondOrderDefectGraph G).adjMatrix ℤ)
  apply sum_matrix_cube_eq_cube_of_sum_eq_of_mul_sum_eq_sq C R
  · exact binarySquare_regular_sum_centeredOwnerGrams G hfree (by omega) m hsum
  · intro c
    exact binarySquare_regular_centeredOwnerGram_mul_defectResolution
      G hfree hq hreg hcard m hm hsum c

/-- Trace form of the centered-owner cubic resolution.  This is the direct
interface for substituting the standard `trace Adj^3 = 6 · triangles`
identities on the owner and defect graphs. -/
theorem binarySquare_regular_sum_trace_centeredOwnerGrams_cube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) :
    let C : (secondOrderDefectGraph G).ConnectedComponent → Matrix V V ℤ :=
      fun c =>
        (q : ℤ) •
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
              (m c : ℤ) • (1 : Matrix V V ℤ)) -
          (m c : ℤ) • FriendshipTheoremOQ01.onesMatrix V
    let R := (q : ℤ) •
      (((q - 1 : ℕ) : ℤ) • (1 : Matrix V V ℤ) -
        (secondOrderDefectGraph G).adjMatrix ℤ)
    ∑ c, Matrix.trace (C c * C c * C c) = Matrix.trace (R * R * R) := by
  dsimp
  have hcube := binarySquare_regular_sum_centeredOwnerGrams_cube
    G hfree hq hreg hcard m hm hsum
  have htrace := congrArg Matrix.trace hcube
  simpa only [Matrix.trace_sum] using htrace

end

end Erdos85
