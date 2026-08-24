import Proofs.Erdos85SecondOrderDefectSetTransfer
import Proofs.Erdos85ExcessDefectRegular

/-!
# Centered image of a q-divisible shore

For a `q`-regular C4-free graph and a shore `S` of size `q*a`, put

`y = A 1_S - a 1`.

The square identity `A²=(q-1)I+J-D` and regularity cancel the principal
term exactly, leaving

`A y = ((q-1)I-D) 1_S`.

This is the algebraic bridge that places the C4 support lower bound and the
defect-cut endpoint upper bound on the same vector.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact centered-shore image identity at a q-divisible support size. -/
theorem c4Free_regular_centeredShore_image_eq_defectLaplacian
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q a : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (S : Finset V) (hScard : S.card = q * a) :
    let A := G.adjMatrix ℤ
    let D := (secondOrderDefectGraph G).adjMatrix ℤ
    let chi := finsetIndicatorInt S
    let one : V → ℤ := fun _ => 1
    let y := A.mulVec chi - (a : ℤ) • one
    A.mulVec y =
      (((q : ℤ) - 1) • (1 : Matrix V V ℤ) - D).mulVec chi := by
  dsimp only
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  have hsq : A * A = ((q : ℤ) - 1) • (1 : Matrix V V ℤ) +
      FriendshipTheoremOQ01.onesMatrix V - D := by
    exact adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have hAone : A.mulVec one = (q : ℤ) • one := by
    ext x
    dsimp [A, one]
    change (G.adjMatrix ℤ).mulVec (Function.const V 1) x = (q : ℤ) * 1
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, hreg x]
  have hJchi :
      (FriendshipTheoremOQ01.onesMatrix V).mulVec chi =
        (S.card : ℤ) • one := by
    ext x
    simpa [chi, one] using
      onesMatrix_mulVec_finsetIndicatorInt_apply S x
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hAone, smul_smul]
  rw [Matrix.mulVec_mulVec, hsq, Matrix.sub_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, hJchi]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  ext x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hScard]
  push_cast
  ring

end

end Erdos85

#print axioms Erdos85.c4Free_regular_centeredShore_image_eq_defectLaplacian
