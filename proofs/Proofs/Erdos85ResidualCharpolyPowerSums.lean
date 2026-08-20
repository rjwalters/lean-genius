import Proofs.Erdos85SurjectiveIntertwinerCharpoly
import Proofs.Erdos85HermitianCharpolyPowerSums

/-!
# Power sums of an exact residual characteristic factor

An exact Hermitian characteristic factorization turns closed-walk trace
moments into residual root moments by subtraction.  This file packages that
step independently of the later h305 arithmetic.
-/

open Polynomial Matrix

namespace Erdos85

noncomputable section

/-- In an exact factorization `charpoly A = p * charpoly B`, every residual
root power sum is the ambient trace moment minus the quotient trace moment. -/
theorem residualRootPowerSum_eq_trace_sub_trace
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (A : Matrix X X ℂ) (B : Matrix Y Y ℂ) (p : ℂ[X])
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hp : p ≠ 0) (hfactor : A.charpoly = p * B.charpoly)
    (n : ℕ) :
    complexRootPowerSum p n = Matrix.trace (A ^ n) - Matrix.trace (B ^ n) := by
  have hmul := complexRootPowerSum_mul hp (Matrix.charpoly_monic B).ne_zero n
  rw [← hfactor,
    complexRootPowerSum_charpoly_eq_trace_pow A hA n,
    complexRootPowerSum_charpoly_eq_trace_pow B hB n] at hmul
  exact eq_sub_of_add_eq hmul.symm

/-- Numerical h305 residual ledger once the ambient and centered-shore trace
moments are supplied.  The cubic moment is retained symbolically because it
records the service triangle count. -/
theorem h305_residualRootPowerSum_ledger_of_trace_moments
    {X Y : Type*} [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    (A : Matrix X X ℂ) (B : Matrix Y Y ℂ) (p : ℂ[X])
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hp : p ≠ 0) (hfactor : A.charpoly = p * B.charpoly)
    (hAone : Matrix.trace (A ^ 1) = 0)
    (hAtwo : Matrix.trace (A ^ 2) = 288)
    (hAfour : Matrix.trace (A ^ 4) = 3168)
    (hBone : Matrix.trace (B ^ 1) = 8)
    (hBtwo : Matrix.trace (B ^ 2) = 64)
    (hBthree : Matrix.trace (B ^ 3) = 224)
    (hBfour : Matrix.trace (B ^ 4) = 1376) :
    complexRootPowerSum p 1 = -8 ∧
      complexRootPowerSum p 2 = 224 ∧
      complexRootPowerSum p 3 = Matrix.trace (A ^ 3) - 224 ∧
      complexRootPowerSum p 4 = 1792 := by
  have h1 := residualRootPowerSum_eq_trace_sub_trace
    A B p hA hB hp hfactor 1
  have h2 := residualRootPowerSum_eq_trace_sub_trace
    A B p hA hB hp hfactor 2
  have h3 := residualRootPowerSum_eq_trace_sub_trace
    A B p hA hB hp hfactor 3
  have h4 := residualRootPowerSum_eq_trace_sub_trace
    A B p hA hB hp hfactor 4
  rw [hAone, hBone] at h1
  rw [hAtwo, hBtwo] at h2
  rw [hBthree] at h3
  rw [hAfour, hBfour] at h4
  norm_num at h1 h2 h4
  exact ⟨h1, h2, h3, h4⟩

end

end Erdos85

#print axioms Erdos85.residualRootPowerSum_eq_trace_sub_trace
#print axioms Erdos85.h305_residualRootPowerSum_ledger_of_trace_moments
