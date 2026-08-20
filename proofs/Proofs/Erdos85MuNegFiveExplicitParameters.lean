import Proofs.Erdos85SizeTwoMuNegFiveEightEightParameterBounds
import Proofs.Erdos85SizeTwoMuNegThreeEightEightAllTriangleParameterBounds

/-!
# Explicit parameter ledger for the `mu = -5` canonical endpoints

The earlier graph-facing parameter theorems existentially re-extract `k`
and `r`.  Switch-orbit assembly must instead retain one concrete pair.  This
file packages the exact finite facts needed by the capacity argument and
states its all-triangle consequence for that same pair.
-/

open Finset Matrix

namespace Erdos85

noncomputable section

/-- The row facts used by the sharp `mu = -5` capacity window, with `k,r`
kept as explicit data rather than hidden behind an existential. -/
structure MuNegFiveExplicitParameterLedger
    (N M : Matrix (ZMod 8) (ZMod 8) ℤ)
    (f g : ZMod 8 → ℤ) (k r : ℕ) : Prop where
  k_le_one : k ≤ 1
  f_sign : ∀ i, f i = -1 ∨ f i = 1
  g_sign : ∀ i, g i = -1 ∨ g i = 1
  f_flip : ∀ i, f (i + 1) = -f i
  g_flip : ∀ i, g (i + 1) = -g i
  internal_row : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
    N 0 j = 1).card = 7 - r
  internal_same : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
    f j = f 0 ∧ N 0 j = 1).card = k
  cross_row : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
    M 0 j = 1).card = r
  cross_same : ((Finset.univ : Finset (ZMod 8)).filter fun j ↦
    g j = f 0 ∧ M 0 j = 1).card = 1 - k

/-- If both cycle-neighbor entries vanish, the explicit `mu = -5` ledger
has `r+k=5`.  Crucially, the conclusion refers to the very same `k,r` that
will be carried by a switch orbit. -/
theorem MuNegFiveExplicitParameterLedger.sum_eq_five_of_cycleZeros
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ} {k r : ℕ}
    (L : MuNegFiveExplicitParameterLedger N M f g k r)
    (hminus : N 0 (-1) ≠ 1) (hplus : N 0 1 ≠ 1) :
    r + k = 5 := by
  have hlower := alternating_C8_allTriangle_internal_parameter_lower
    N f k r L.f_sign L.f_flip L.internal_row L.internal_same hminus hplus
  have hbounds := alternating_C8_internal_cross_parameter_bounds_one
    N M f g k r L.k_le_one L.f_sign L.g_sign L.f_flip L.g_flip
      L.internal_row L.internal_same L.cross_row L.cross_same
  omega

/-- At the canonical endpoint `(mu,k,r)=(-5,0,3)`, at least one of the two
cycle-neighbor defect entries is present.  Thus this endpoint cannot be an
all-triangle shore; this is the first geometry reduction for leaf `h503` in
the non-recursive negative switch-orbit eliminator. -/
theorem MuNegFiveExplicitParameterLedger.zeroThree_cycleEntry
    {N M : Matrix (ZMod 8) (ZMod 8) ℤ}
    {f g : ZMod 8 → ℤ}
    (L : MuNegFiveExplicitParameterLedger N M f g 0 3) :
    N 0 (-1) = 1 ∨ N 0 1 = 1 := by
  by_contra h
  simp only [not_or] at h
  have := L.sum_eq_five_of_cycleZeros h.1 h.2
  norm_num at this

end

end Erdos85

#print axioms Erdos85.MuNegFiveExplicitParameterLedger.sum_eq_five_of_cycleZeros
#print axioms Erdos85.MuNegFiveExplicitParameterLedger.zeroThree_cycleEntry
