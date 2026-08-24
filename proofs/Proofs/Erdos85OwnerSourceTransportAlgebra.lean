import Mathlib

/-!
# Owner source-transport algebra

These are the exact characteristic-two cancellation laws in
`(73rnz_cjibk)--(73rnz_cjibkc)`.  They expose the `rho`/`mu` bookkeeping and,
crucially, retain the inactive collision residue rather than silently
discarding it.
-/

namespace Erdos85

private theorem zmodTwo_add_self (z : ZMod 2) : z + z = 0 := by
  rw [← two_mul]
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_mul]

/-- **Active switch transport (73rnz_cjibk).**  The two complement units
cancel, leaving precisely the source `rho` plus relay `mu`. -/
theorem activeSwitch_sourceTransport
    (kSource kRelay rho mu : ZMod 2)
    (hsource : kSource = 1 + rho)
    (hrelay : kRelay = 1 + mu) :
    kSource + kRelay = rho + mu := by
  rw [hsource, hrelay]
  have hone : (1 : ZMod 2) + 1 = 0 := zmodTwo_add_self 1
  calc
    (1 + rho) + (1 + mu) = (1 + 1) + (rho + mu) := by ring
    _ = rho + mu := by rw [hone, zero_add]

/-- **Collision transport (73rnz_cjibka).**  Summing only active relay
ports cancels their active constants; the inactive-port parity survives as
an explicit source term. -/
theorem collision_sourceTransport
    {I : Type*} [DecidableEq I] (activePorts : Finset I)
    (kSource rho c cActive cInactive : ZMod 2)
    (kRelay mu : I → ZMod 2)
    (hcount : c = cActive + cInactive)
    (hsource : kSource = c + rho)
    (hrelay : (∑ i ∈ activePorts, kRelay i) =
      cActive + ∑ i ∈ activePorts, mu i) :
    kSource + ∑ i ∈ activePorts, kRelay i =
      cInactive + rho + ∑ i ∈ activePorts, mu i := by
  rw [hsource, hrelay, hcount]
  have hcancel := zmodTwo_add_self cActive
  calc
    (cActive + cInactive + rho) +
        (cActive + ∑ i ∈ activePorts, mu i) =
      (cActive + cActive) +
        (cInactive + rho + ∑ i ∈ activePorts, mu i) := by ring
    _ = cInactive + rho + ∑ i ∈ activePorts, mu i := by
      rw [hcancel, zero_add]

/-- **Active direct-exit transport (73rnz_cjibkb).**  The two complement
units on the source and leaf relay cancel. -/
theorem activeDirectExit_sourceTransport
    (kSource kRelay muSource muRelay : ZMod 2)
    (hsource : kSource = 1 + muSource)
    (hrelay : kRelay = 1 + muRelay) :
    kSource + kRelay = muSource + muRelay := by
  exact activeSwitch_sourceTransport
    kSource kRelay muSource muRelay hsource hrelay

/-- **Active cross-star through transport (73rnz_cjibkc).**  The occupied
source cell cancels the universal complement unit of its owner relay. -/
theorem activeCrossStarThrough_sourceTransport
    (sourceCell kRelay muRelay : ZMod 2)
    (hsource : sourceCell = 1)
    (hrelay : kRelay = 1 + muRelay) :
    sourceCell + kRelay = muRelay := by
  rw [hsource, hrelay]
  have hone : (1 : ZMod 2) + 1 = 0 := zmodTwo_add_self 1
  calc
    1 + (1 + muRelay) = (1 + 1) + muRelay := by ring
    _ = muRelay := by rw [hone, zero_add]

end Erdos85

#print axioms Erdos85.activeSwitch_sourceTransport
#print axioms Erdos85.collision_sourceTransport
#print axioms Erdos85.activeDirectExit_sourceTransport
#print axioms Erdos85.activeCrossStarThrough_sourceTransport
