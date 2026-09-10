import Proofs.Erdos85NonregularDiagonalParity

/-!
Diagonal parity for the nonregular weighted Hoffman argument. The quadratic
form cancellation is reused from `Erdos85HoffmanDiagonalParity`; unlike its
regular specialization, the even-power diagonal retains the actual row sum.
This file does not assert the spectral projector or eliminate any q7 profile.
-/
namespace Erdos85
open Matrix Polynomial Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Diagonal evaluation over an extension ring, retaining the true row sums.
The explicit coefficient sum avoids any assumption that coefficients lie in F2. -/
theorem weighted_hoffman_diagonal_sum {R : Type*} [CommRing R]
    (φ : ZMod 2 →+* R) (A : Matrix V V (ZMod 2))
    (hsymm : Aᵀ = A) (hdiag : ∀ v, A v v = 0)
    (f : R[X]) (v : V) :
    (aeval (A.map φ) f) v v =
      ∑ k ∈ Finset.range (f.natDegree+1),
        if Even k then f.coeff k * φ ((A ^ (k/2) *ᵥ (fun _ => 1)) v) else 0 := by
  rw [aeval_eq_sum_range, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hmap : (A.map φ)^k = (A^k).map φ := by
    exact (map_pow φ.mapMatrix A k).symm
  rw [hmap, Matrix.map_apply]
  obtain ⟨r, hr | hr⟩ := Nat.even_or_odd' k
  · subst k
    rw [if_pos (even_two_mul r), diagonal_even_power_mod_two A hsymm]
    rw [show 2*r/2 = r by omega]
  · subst k
    rw [if_neg (by rintro ⟨s, hs⟩; omega : ¬ Even (2*r+1)),
      diagonal_odd_power_mod_two A hsymm hdiag, map_zero, mul_zero]
end Erdos85
