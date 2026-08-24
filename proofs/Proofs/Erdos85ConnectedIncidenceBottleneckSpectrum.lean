import Proofs.Erdos85ConnectedIncidenceBottleneckPolynomial

/-!
# Spectrum of the connected incidence bottleneck

The cubic identity for `E = AD-(J-A)` becomes diagonal on every
nonprincipal adjacency eigenvector.  This file records both useful scalar
forms of its multiplier:

* `theta * (q-theta^2)` in adjacency coordinates;
* `theta * (mu+1)` when `mu = q-1-theta^2` is the corresponding defect
  eigenvalue.
-/

namespace Erdos85

noncomputable section

/-- The cubic bottleneck acts by `theta * (q-theta^2)` on a nonprincipal
`theta`-eigenvector. -/
theorem incidenceBottleneck_cubic_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℚ) (q theta : ℚ) (v : V → ℚ)
    (hv : A.mulVec v = theta • v)
    (hJ : J.mulVec v = 0) :
    (q • A - A * A * A + (q - 1) • J).mulVec v =
      (theta * (q - theta ^ 2)) • v := by
  have hAA : (A * A).mulVec v = theta ^ 2 • v := by
    calc
      (A * A).mulVec v = A.mulVec (A.mulVec v) :=
        (Matrix.mulVec_mulVec v A A).symm
      _ = A.mulVec (theta • v) := by rw [hv]
      _ = theta • A.mulVec v := Matrix.mulVec_smul A theta v
      _ = theta • (theta • v) := by rw [hv]
      _ = theta ^ 2 • v := by rw [← mul_smul, pow_two]
  have hAAA : (A * A * A).mulVec v = theta ^ 3 • v := by
    calc
      (A * A * A).mulVec v = (A * A).mulVec (A.mulVec v) :=
        (Matrix.mulVec_mulVec v (A * A) A).symm
      _ = (A * A).mulVec (theta • v) := by rw [hv]
      _ = theta • (A * A).mulVec v := Matrix.mulVec_smul (A * A) theta v
      _ = theta • (theta ^ 2 • v) := by rw [hAA]
      _ = theta ^ 3 • v := by rw [← mul_smul]; ring
  rw [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, hJ, smul_zero, add_zero, hAAA, hv]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Equivalent defect-eigenvalue form of the bottleneck multiplier. -/
theorem incidenceBottleneck_cubic_mulVec_eq_theta_mul_mu_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A J : Matrix V V ℚ) (q theta mu : ℚ) (v : V → ℚ)
    (hv : A.mulVec v = theta • v)
    (hJ : J.mulVec v = 0)
    (hmu : mu = q - 1 - theta ^ 2) :
    (q • A - A * A * A + (q - 1) • J).mulVec v =
      (theta * (mu + 1)) • v := by
  rw [incidenceBottleneck_cubic_mulVec A J q theta v hv hJ, hmu]
  congr 1
  ring

/-- Matrix-identity form: any bottleneck matrix identified with the cubic
polynomial has the same exact nonprincipal multiplier. -/
theorem incidenceBottleneck_mulVec_eq_theta_mul_mu_add_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (A J E : Matrix V V ℚ) (q theta mu : ℚ) (v : V → ℚ)
    (hE : E = q • A - A * A * A + (q - 1) • J)
    (hv : A.mulVec v = theta • v)
    (hJ : J.mulVec v = 0)
    (hmu : mu = q - 1 - theta ^ 2) :
    E.mulVec v = (theta * (mu + 1)) • v := by
  rw [hE]
  exact incidenceBottleneck_cubic_mulVec_eq_theta_mul_mu_add_one
    A J q theta mu v hv hJ hmu

end

end Erdos85

#print axioms Erdos85.incidenceBottleneck_cubic_mulVec
#print axioms Erdos85.incidenceBottleneck_cubic_mulVec_eq_theta_mul_mu_add_one
#print axioms Erdos85.incidenceBottleneck_mulVec_eq_theta_mul_mu_add_one
