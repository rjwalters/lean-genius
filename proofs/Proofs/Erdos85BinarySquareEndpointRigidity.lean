import Proofs.Erdos85BinarySquareUnitOwnerSpectralInterval
import Mathlib.Analysis.Matrix.PosDef

/-!
# Endpoint rigidity for unit centered-owner sectors

The sharp second-moment identity becomes rigid once a positive sector is
trapped below the scalar endpoint.  This file packages that equality case.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

open scoped MatrixOrder

/-- A PSD real matrix trapped below `r I` and attaining the sharp quadratic
trace bound is a scaled orthogonal projection. -/
theorem posSemidef_mul_self_eq_smul_of_upper_of_trace_sq_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (r : ℝ)
    (hA : A.PosSemidef)
    (hupper : (r • (1 : Matrix V V ℝ) - A).PosSemidef)
    (htrace : Matrix.trace (A * A) = r * Matrix.trace A) :
    A * A = r • A := by
  let B : Matrix V V ℝ := r • (1 : Matrix V V ℝ) - A
  have hcomm : Commute A B := by
    dsimp [B]
    change A * (r • 1 - A) = (r • 1 - A) * A
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  have hprod_nonneg : 0 ≤ A * B :=
    Commute.mul_nonneg hA.nonneg (by simpa [B] using hupper.nonneg) hcomm
  have hprod : (A * B).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hprod_nonneg
  have htrprod : Matrix.trace (A * B) = 0 := by
    dsimp [B]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, htrace]
    ring
  have hzero : A * B = 0 := (hprod.trace_eq_zero_iff).mp htrprod
  dsimp [B] at hzero
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- Under the sharp PSD trace equality, every real eigenvalue lies at one of
the two endpoints. -/
theorem eigenvalue_eq_zero_or_endpoint_of_posSemidef_of_upper_of_trace_sq_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (r eig : ℝ)
    (hA : A.PosSemidef)
    (hupper : (r • (1 : Matrix V V ℝ) - A).PosSemidef)
    (htrace : Matrix.trace (A * A) = r * Matrix.trace A)
    (v : V → ℝ) (hv : A.mulVec v = eig • v) (hv0 : v ≠ 0) :
    eig = 0 ∨ eig = r := by
  have hpoly := posSemidef_mul_self_eq_smul_of_upper_of_trace_sq_eq
    A r hA hupper htrace
  have hvec := congrArg (fun M : Matrix V V ℝ ↦ M.mulVec v) hpoly
  have hleft : (A * A).mulVec v = (eig * eig) • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv]
    simp [smul_smul]
  rw [hleft, Matrix.smul_mulVec, hv] at hvec
  simp only [smul_smul] at hvec
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv0
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  obtain ⟨i, hi⟩ := hex
  have hiEq := congrFun hvec i
  simp only [Pi.smul_apply, smul_eq_mul] at hiEq
  have hz : (eig * (eig - r)) * v i = 0 := by
    calc
      (eig * (eig - r)) * v i = eig * eig * v i - r * eig * v i := by ring
      _ = 0 := sub_eq_zero.mpr hiEq
  rcases mul_eq_zero.mp hz with hfactor | hiv
  · rcases mul_eq_zero.mp hfactor with hzero | hend
    · exact Or.inl hzero
    · exact Or.inr (sub_eq_zero.mp hend)
  · exact (hi hiv).elim

end

end Erdos85
