import Proofs.Erdos85RationalPrimaryTraceSplit

/-!
# Trace of a designated primary sector

This file isolates the final piece of three-sector trace bookkeeping used in
the Erdős 85 nonbipartite branch.  Once the total trace is zero, the principal
sector has trace `τ`, and the sign-paired residual sector has trace zero, the
remaining designated primary sector has trace `-τ`.
-/

open Polynomial

namespace Erdos85

noncomputable section

variable {K : Type*} [Field K] {E : Type*} [AddCommGroup E] [Module K E]

/-- In a three-sector primary decomposition, total trace zero, principal
trace `τ`, and residual trace zero force the designated sector trace to be
`-τ`.  The designated polynomial may bundle any number of irreducible primary
factors; no irreducibility assumption is needed for this bookkeeping step. -/
theorem designated_trace_eq_neg_of_three_sector_split [FiniteDimensional K E]
    (S T : E →ₗ[K] E) (hcomm : S * T = T * S)
    (principal designated residual : K[X])
    (hpd : IsCoprime principal designated)
    (hpr : IsCoprime principal residual)
    (hdr : IsCoprime designated residual)
    (hann : aeval T (principal * designated * residual) = 0)
    (τ : K)
    (htotal : LinearMap.trace K E S = 0)
    (hprincipal :
      LinearMap.trace K (LinearMap.ker (aeval T principal))
        (kerAevalRestrict S T hcomm principal) = τ)
    (hresidual :
      LinearMap.trace K (LinearMap.ker (aeval T residual))
        (kerAevalRestrict S T hcomm residual) = 0) :
    LinearMap.trace K (LinearMap.ker (aeval T designated))
        (kerAevalRestrict S T hcomm designated) = -τ := by
  have hsplit := trace_eq_add_add_trace_restrict_ker_aeval
    S T hcomm principal designated residual hpd hpr hdr hann
  rw [htotal, hprincipal, hresidual, add_zero] at hsplit
  rw [eq_neg_iff_add_eq_zero]
  simpa [add_comm] using hsplit.symm

#print axioms designated_trace_eq_neg_of_three_sector_split

end

end Erdos85
