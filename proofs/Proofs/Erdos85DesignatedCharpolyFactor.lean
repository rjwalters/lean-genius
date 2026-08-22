import Proofs.Erdos85RationalPrimaryTraceSplit

/-!
# Designated primary characteristic factor

In a pairwise-coprime three-sector decomposition, the characteristic
polynomial of the restriction to the designated sector divides the ambient
characteristic polynomial.
-/

open Polynomial

namespace Erdos85

noncomputable section

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- The designated restriction characteristic polynomial is an ambient
characteristic factor in a three-sector primary decomposition. -/
theorem charpoly_kerAevalRestrict_dvd_of_three_sector
    [FiniteDimensional K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (principal designated residual : K[X])
    (hpd : IsCoprime principal designated)
    (hdr : IsCoprime designated residual)
    (hann : aeval T (principal * designated * residual) = 0) :
    (kerAevalRestrict S T hcomm designated).charpoly ∣ S.charpoly := by
  have hcop : IsCoprime designated (principal * residual) :=
    hpd.symm.mul_right hdr
  have hann' : aeval T (designated * (principal * residual)) = 0 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hann
  have hfactor := charpoly_eq_mul_kerAevalRestrict
    S T hcomm hcop hann'
  rw [hfactor]
  exact dvd_mul_right _ _

#print axioms charpoly_kerAevalRestrict_dvd_of_three_sector

end

end Erdos85
