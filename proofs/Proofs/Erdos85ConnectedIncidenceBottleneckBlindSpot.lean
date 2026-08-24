import Proofs.Erdos85ConnectedIncidenceBottleneckSpectrum

/-!
# Exact blind spot of the connected incidence bottleneck

On a nonzero common eigenvector the bottleneck multiplier is
`theta * (mu+1)`.  Once the ambient adjacency eigenvalue `theta` is nonzero
(as it is in the connected-defect/nonsingular branch), vanishing is therefore
equivalent to the single defect eigenvalue `mu = -1`.
-/

namespace Erdos85

noncomputable section

/-- A nonzero eigenvector with nonzero ambient eigenvalue lies in the
bottleneck kernel exactly at defect eigenvalue `-1`. -/
theorem incidenceBottleneck_mulVec_eq_zero_iff_mu_eq_neg_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Matrix V V ℚ) (theta mu : ℚ) (v : V → ℚ)
    (hv : v ≠ 0) (htheta : theta ≠ 0)
    (hEv : E.mulVec v = (theta * (mu + 1)) • v) :
    E.mulVec v = 0 ↔ mu = -1 := by
  rw [hEv]
  constructor
  · intro hzero
    have hscalar : theta * (mu + 1) = 0 :=
      (smul_eq_zero.mp hzero).resolve_right hv
    rcases mul_eq_zero.mp hscalar with hthetaZero | hmu
    · exact (htheta hthetaZero).elim
    · linarith
  · intro hmu
    subst mu
    simp

/-- Composed cubic form of the exact blind-spot equivalence. -/
theorem incidenceBottleneck_cubic_mulVec_eq_zero_iff_mu_eq_neg_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℚ) (q theta mu : ℚ) (v : V → ℚ)
    (hv0 : v ≠ 0) (htheta : theta ≠ 0)
    (hv : A.mulVec v = theta • v)
    (hJ : J.mulVec v = 0)
    (hmu : mu = q - 1 - theta ^ 2) :
    (q • A - A * A * A + (q - 1) • J).mulVec v = 0 ↔
      mu = -1 := by
  apply incidenceBottleneck_mulVec_eq_zero_iff_mu_eq_neg_one
    (q • A - A * A * A + (q - 1) • J) theta mu v hv0 htheta
  exact incidenceBottleneck_cubic_mulVec_eq_theta_mul_mu_add_one
    A J q theta mu v hv hJ hmu

end

end Erdos85

#print axioms Erdos85.incidenceBottleneck_mulVec_eq_zero_iff_mu_eq_neg_one
#print axioms Erdos85.incidenceBottleneck_cubic_mulVec_eq_zero_iff_mu_eq_neg_one
