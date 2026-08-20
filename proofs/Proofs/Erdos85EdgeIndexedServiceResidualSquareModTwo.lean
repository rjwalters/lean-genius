import Proofs.Erdos85EdgeIndexedServiceIntegralResidual
import Proofs.Erdos85AdjacencyCharpolySquareModTwo

/-! # The integral service residual is a square modulo two -/

open SimpleGraph Matrix Polynomial

namespace Erdos85

noncomputable section

theorem h305CenteredServiceFactorInt_map_zmodTwo :
    h305CenteredServiceFactorInt.map (Int.castRingHom (ZMod 2)) = X ^ 16 := by
  simp only [h305CenteredServiceFactorInt, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C]
  simp [show (2 : ZMod 2) = 0 by decide,
    show (6 : ZMod 2) = 0 by decide]
  ring

/-- After removing the explicit centered `C8 ⊔ C8` factor, the remaining
degree-32 integral characteristic factor is still a square modulo two.  The
explicit factor reduces to `X^16`; differentiating and cancelling that
nonzero factor transfers the characteristic-two square constraint. -/
theorem edgeIndexedService_integralResidual_isSquare_zmodTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (P : ℤ[X])
    (hfactor : (Cedge.adjMatrix ℤ).charpoly =
      P * h305CenteredServiceFactorInt)
    (hcard : Even (Fintype.card R.edgeFinset)) :
    ∃ p : (ZMod 2)[X],
      P.map (Int.castRingHom (ZMod 2)) = p ^ 2 := by
  let f := Int.castRingHom (ZMod 2)
  let Pbar := P.map f
  have hadjMap : (Cedge.adjMatrix ℤ).map f = Cedge.adjMatrix (ZMod 2) := by
    exact adjMatrix_map_intCast Cedge
  have hcharMap : (Cedge.adjMatrix ℤ).charpoly.map f =
      (Cedge.adjMatrix (ZMod 2)).charpoly := by
    rw [← Matrix.charpoly_map, hadjMap]
  have hmapped := congrArg (Polynomial.map f) hfactor
  rw [Polynomial.map_mul, hcharMap,
    h305CenteredServiceFactorInt_map_zmodTwo] at hmapped
  change (Cedge.adjMatrix (ZMod 2)).charpoly = Pbar * X ^ 16 at hmapped
  have hderivFull := adjMatrix_charpoly_derivative_eq_zero_zmodTwo Cedge hcard
  rw [hmapped, Polynomial.derivative_mul] at hderivFull
  have hderivX : (X ^ 16 : (ZMod 2)[X]).derivative = 0 := by
    rw [Polynomial.derivative_pow]
    have h16 : (16 : ZMod 2) = 0 := by decide
    change C (16 : ZMod 2) * X ^ (16 - 1) * derivative X = 0
    rw [h16]
    simp
  rw [hderivX, mul_zero, add_zero] at hderivFull
  have hderiv : Pbar.derivative = 0 := by
    exact (mul_eq_zero.mp hderivFull).resolve_right (pow_ne_zero 16 X_ne_zero)
  let p := Polynomial.contract 2 Pbar
  refine ⟨p, ?_⟩
  have hexpand : Polynomial.expand (ZMod 2) 2 p = Pbar :=
    Polynomial.expand_contract' 2 hderiv
  have hfrob := Polynomial.map_frobenius_expand (R := ZMod 2) 2 p
  rw [hexpand] at hfrob
  simpa [Pbar, p, frobenius_def] using hfrob

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_integralResidual_isSquare_zmodTwo
