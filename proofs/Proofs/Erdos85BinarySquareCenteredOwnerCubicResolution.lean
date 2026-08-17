import Proofs.Erdos85BinarySquareCenteredOwnerResolution

/-!
# Cubic resolution of centered owner sectors

The mutually annihilating centered owner sectors resolve not only the square
but also the cube of the centered defect operator.  This is the algebraic
bridge between colorwise cubic traces and the defect-side third moment.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Abstract cubic Parseval identity for matrix summands selected by their
sum.  No commutativity assumption is needed. -/
theorem sum_matrix_cube_eq_cube_of_sum_eq_of_mul_sum_eq_sq
    {I V K : Type*} [Fintype I] [DecidableEq I] [Fintype V]
    [CommRing K]
    (C : I → Matrix V V K) (R : Matrix V V K)
    (hsum : ∑ i, C i = R) (hselect : ∀ i, C i * R = C i * C i) :
    ∑ i, (C i * C i) * C i = (R * R) * R := by
  have hsquare : ∑ i, C i * C i = R * R :=
    sum_matrix_sq_eq_sq_of_sum_eq_of_mul_sum_eq_sq C R hsum hselect
  calc
    ∑ i, (C i * C i) * C i = ∑ i, (C i * C i) * R := by
      apply Finset.sum_congr rfl
      intro i _hi
      calc
        (C i * C i) * C i = C i * (C i * C i) := by rw [Matrix.mul_assoc]
        _ = C i * (C i * R) := by rw [hselect i]
        _ = (C i * C i) * R := by rw [Matrix.mul_assoc]
    _ = (∑ i, C i * C i) * R := by rw [Finset.sum_mul]
    _ = (R * R) * R := by rw [hsquare]

/-- **Centered-owner cubic resolution.**  The sum of the cubed color sectors
is exactly the cube of `q ((q-1)I-D)`. -/
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
    ∑ c, (C c * C c) * C c = (R * R) * R := by
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

end

end Erdos85
