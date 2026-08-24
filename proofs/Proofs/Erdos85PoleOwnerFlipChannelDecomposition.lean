import Mathlib

/-!
# Pole-owner inactive/flip channel decomposition

At pole `E_i`, let `sigma_i` be the split-pair bit, `k_i` the pole K-fiber
bit, and `a_i` the active-witness bit.  The primary identity is
`k_i + sigma_i = 1`.  The canonical star geometry identifies the active
flip channels as

`F00 = sigma_i a_i`, `F11 = k_i a_i`.

Consequently each primary channel is the disjoint mod-two sum of its
inactive source and its active flip.  An inactive pole supplies exactly one
source cell; an active pole supplies exactly one of the 00/11 flip cells.
This formalizes `(73rnz_cjibkl)--(73rnz_cjibkm)`.
-/

namespace Erdos85

/-- The four source/transition cells attached to one pole owner. -/
structure PoleOwnerFlipChannels where
  inactiveSplit : ZMod 2
  inactiveK : ZMod 2
  flip00 : ZMod 2
  flip11 : ZMod 2
deriving DecidableEq

/-- Canonical cells determined by split, K-fiber, and activity bits. -/
def poleOwnerFlipChannels (k sigma activity : ZMod 2) :
    PoleOwnerFlipChannels where
  inactiveSplit := sigma * (1 + activity)
  inactiveK := k * (1 + activity)
  flip00 := sigma * activity
  flip11 := k * activity

private theorem f2_self_add (x : ZMod 2) : x + x = 0 := by
  have hchar : (2 : ZMod 2) = 0 := by decide
  rw [← two_mul, hchar, zero_mul]

private theorem inactive_add_active_factor (x a : ZMod 2) :
    x = x * (1 + a) + x * a := by
  calc
    x = x * 1 := by rw [mul_one]
    _ = x * ((1 + a) + a) := by rw [add_assoc, f2_self_add, add_zero]
    _ = x * (1 + a) + x * a := mul_add x (1 + a) a

/-- The split-pair source is its inactive source cell plus the active 00
flip channel. -/
theorem split_eq_inactiveSplit_add_flip00 (k sigma activity : ZMod 2) :
    sigma = (poleOwnerFlipChannels k sigma activity).inactiveSplit +
      (poleOwnerFlipChannels k sigma activity).flip00 := by
  exact inactive_add_active_factor sigma activity

/-- The pole K-fiber source is its inactive source cell plus the active 11
flip channel. -/
theorem kFiber_eq_inactiveK_add_flip11 (k sigma activity : ZMod 2) :
    k = (poleOwnerFlipChannels k sigma activity).inactiveK +
      (poleOwnerFlipChannels k sigma activity).flip11 := by
  exact inactive_add_active_factor k activity

/-- **Pole demand channel decomposition (`73rnz_cjibkm`).**  The diagonal
owner demand one is exactly the sum of the two inactive source cells and the
two active flip cells. -/
theorem one_eq_sum_poleOwnerFlipChannels
    (k sigma activity : ZMod 2) (hsource : k + sigma = 1) :
    1 = (poleOwnerFlipChannels k sigma activity).inactiveSplit +
        (poleOwnerFlipChannels k sigma activity).inactiveK +
      (poleOwnerFlipChannels k sigma activity).flip00 +
        (poleOwnerFlipChannels k sigma activity).flip11 := by
  rw [← hsource]
  conv_lhs => rw [split_eq_inactiveSplit_add_flip00 k sigma activity,
    kFiber_eq_inactiveK_add_flip11 k sigma activity]
  abel

/-- The aggregate inactive source has value `1+a`. -/
theorem inactive_poleOwnerFlipChannels_sum
    (k sigma activity : ZMod 2) (hsource : k + sigma = 1) :
    (poleOwnerFlipChannels k sigma activity).inactiveSplit +
        (poleOwnerFlipChannels k sigma activity).inactiveK = 1 + activity := by
  simp only [poleOwnerFlipChannels]
  calc
    sigma * (1 + activity) + k * (1 + activity) =
        (k + sigma) * (1 + activity) := by ring
    _ = 1 * (1 + activity) := by rw [hsource]
    _ = 1 + activity := one_mul _

/-- The aggregate active flip channel has value `a`. -/
theorem active_poleOwnerFlipChannels_sum
    (k sigma activity : ZMod 2) (hsource : k + sigma = 1) :
    (poleOwnerFlipChannels k sigma activity).flip00 +
        (poleOwnerFlipChannels k sigma activity).flip11 = activity := by
  simp only [poleOwnerFlipChannels]
  calc
    sigma * activity + k * activity = (k + sigma) * activity := by ring
    _ = 1 * activity := by rw [hsource]
    _ = activity := one_mul _

/-- Inactivity kills both flip cells and leaves total source one. -/
theorem poleOwnerFlipChannels_of_inactive
    (k sigma : ZMod 2) (hsource : k + sigma = 1) :
    let C := poleOwnerFlipChannels k sigma 0
    C.flip00 = 0 ∧ C.flip11 = 0 ∧ C.inactiveSplit + C.inactiveK = 1 := by
  simp [poleOwnerFlipChannels, hsource, add_comm]

/-- Activity kills both inactive cells and leaves total flip mass one. -/
theorem poleOwnerFlipChannels_of_active
    (k sigma : ZMod 2) (hsource : k + sigma = 1) :
    let C := poleOwnerFlipChannels k sigma 1
    C.inactiveSplit = 0 ∧ C.inactiveK = 0 ∧ C.flip00 + C.flip11 = 1 := by
  have htwo : (1 + 1 : ZMod 2) = 0 := by decide
  simp [poleOwnerFlipChannels, htwo, hsource, add_comm]

end Erdos85

#print axioms Erdos85.one_eq_sum_poleOwnerFlipChannels
#print axioms Erdos85.inactive_poleOwnerFlipChannels_sum
#print axioms Erdos85.active_poleOwnerFlipChannels_sum
#print axioms Erdos85.poleOwnerFlipChannels_of_inactive
#print axioms Erdos85.poleOwnerFlipChannels_of_active
