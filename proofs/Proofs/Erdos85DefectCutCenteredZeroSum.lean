import Proofs.Erdos85DefectCutCenteredImage
import Proofs.Erdos85BinarySquareSignedEigenvectorSupport

/-!
# Zero sum of the centered shore vector

At square order, if `|S| = q a`, then the centered incidence vector
`y = A 1_S - a 1` has coordinate sum zero. This is the graph-facing
conservation hypothesis needed to apply the integral zero-sum support bounds
in the maximal defect-connectivity argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The centered vector attached to a `q`-divisible shore has total sum zero
in a `q`-regular graph on `q²` vertices. -/
theorem regular_squareOrder_centeredShore_sum_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {q a : ℕ} (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) (hScard : S.card = q * a) :
    let A := G.adjMatrix ℤ
    let chi := finsetIndicatorInt S
    let one : V → ℤ := fun _ => 1
    let y := A.mulVec chi - (a : ℤ) • one
    ∑ x, y x = 0 := by
  dsimp only
  simp_rw [Pi.sub_apply]
  rw [Finset.sum_sub_distrib,
    sum_adjMatrix_mulVec_of_regular_int G q hreg]
  have hchi : ∑ x : V, finsetIndicatorInt S x = (S.card : ℤ) := by
    simp [finsetIndicatorInt]
  rw [hchi]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_const,
    nsmul_eq_mul, mul_one]
  rw [hScard, Finset.card_univ, hcard]
  push_cast
  ring

#print axioms regular_squareOrder_centeredShore_sum_eq_zero

end

end Erdos85
