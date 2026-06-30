/-
Roth/Szemerédi — OQ-03-OQ-01-OQ-01-OQ-01-OQ-01:
Affine covariance of the k-AP counting operator Λ_k

Source: open question of the roth-theorem-k3 gallery (Gowers norms, OQ-03)
Parent:        Proofs/RothTheoremOQ03OQ01OQ01OQ01.lean (symmetries of Λ_k)
Grandparent:   Proofs/RothTheoremOQ03OQ01OQ01.lean   (multilinearity of Λ_k)
Greatgrandpa:  Proofs/RothTheoremOQ03OQ01.lean       (defines Λ_k, foundational identities)

## What this adds

The lineage builds the k-AP counting operator

  Λ_k(f₀,…,f_{k-1}) = E_{x,d ∈ ZMod N} ∏_{i<k} fᵢ(x + i·d)

and records its degenerate identities (greatgrandparent), its *multilinearity*
(grandparent), and two *symmetries* — translation invariance and reflection
(parent). The parent's translation invariance handles the **additive** part of
the symmetry group of an arithmetic progression. It leaves out the
**multiplicative** part: the count is also invariant under *dilation* of the
configuration by any invertible scalar.

This file proves the full **affine covariance** of Λ_k, 0-axiom:

* `kAPCount_affine` — for any unit `a : (ZMod N)ˣ` and any translate `t`,
  replacing every function `fᵢ` by `y ↦ fᵢ(a·y + t)` leaves the count
  unchanged:
  `Λ_k(f₀(a·+t),…) = Λ_k(f₀,…)`.
  The affine map `φ(y) = a·y + t` carries the progression `{x + i·d}` to
  `{φ(x) + i·(a·d)}`, again an arithmetic progression, and `(x,d) ↦ (a·x+t, a·d)`
  is a bijection of `(ZMod N)²` precisely because `a` is invertible. So the
  averaging measure is preserved and the count is fixed.

This exhibits the **one-dimensional affine group** `GA(1, ZMod N) = (ZMod N)ˣ ⋉ ZMod N`
acting on Λ_k by symmetries. Two corollaries isolate the pieces:

* `kAPCount_dilate` — the genuinely new **dilation invariance** (`t = 0`):
  `Λ_k(f₀(a·),…) = Λ_k(f₀,…)` for any unit `a`. This is *not* a consequence of
  translation (parent) or reflection: e.g. `a = -1` gives `Λ_k(f₀(-·),…) = Λ_k(f₀,…)`,
  the point reflection through the origin without reversing the slot order, which
  the reflection symmetry `i ↦ k-1-i` does not provide.

* `kAPCount_translate_of_affine` — recovers the parent's **translation invariance**
  as the `a = 1` case, confirming that affine covariance subsumes it.

The multiplicative reindexing is packaged as `mulUnit a`, the bijection
`y ↦ a·y` of `ZMod N` (an `Equiv` because `a` is a unit); the additive part reuses
`Equiv.addRight`. All results are machine-checked with only the foundational
axioms (`propext`/`Classical.choice`/`Quot.sound`), no `native_decide`.

References:
- Gowers, "A new proof of Szemerédi's theorem" (2001)
- Tao, "Higher order Fourier analysis" (2012)
-/
import Proofs.RothTheoremOQ03OQ01OQ01OQ01

open Finset BigOperators

namespace RothTheoremOQ03OQ01

variable {N : ℕ} [NeZero N]

-- ============================================================
-- Multiplication by a unit is a bijection of `ZMod N`
-- ============================================================

/-- Multiplication by a unit `a : (ZMod N)ˣ` is a permutation of `ZMod N`, with
inverse multiplication by `a⁻¹`. This is the multiplicative (dilation) part of
the affine reindexing `(x, d) ↦ (a·x + t, a·d)`. -/
def mulUnit (a : (ZMod N)ˣ) : ZMod N ≃ ZMod N where
  toFun x := (a : ZMod N) * x
  invFun x := ((a⁻¹ : (ZMod N)ˣ) : ZMod N) * x
  left_inv x := Units.inv_mul_cancel_left a x
  right_inv x := Units.mul_inv_cancel_left a x

@[simp] theorem mulUnit_apply (a : (ZMod N)ˣ) (x : ZMod N) :
    mulUnit a x = (a : ZMod N) * x := rfl

-- ============================================================
-- Affine covariance
-- ============================================================

/-- **Affine covariance.** For any unit `a : (ZMod N)ˣ` and any translate
`t : ZMod N`, replacing every function `fᵢ` by `y ↦ fᵢ(a·y + t)` does not change
the count:
`Λ_k(f₀(a·+t),…,f_{k-1}(a·+t)) = Λ_k(f₀,…,f_{k-1})`.

The affine map `φ(y) = a·y + t` sends the progression `x, x+d, …, x+(k-1)d` to the
progression with base point `a·x+t` and common difference `a·d`; the average is
reindexed by `x ↦ a·x+t` (outer) and `d ↦ a·d` (inner), each a bijection because
`a` is a unit. -/
theorem kAPCount_affine (k : ℕ) (f : Fin k → ZMod N → ℂ)
    (a : (ZMod N)ˣ) (t : ZMod N) :
    kAPCount k (fun i y => f i ((a : ZMod N) * y + t)) = kAPCount k f := by
  unfold kAPCount
  congr 1
  -- reindex the outer base-point average `x ↦ a·x + t`
  refine Fintype.sum_equiv ((mulUnit a).trans (Equiv.addRight t)) _ _ (fun x => ?_)
  -- reindex the inner common-difference average `d ↦ a·d`
  refine Fintype.sum_equiv (mulUnit a) _ _ (fun d => ?_)
  refine Finset.prod_congr rfl (fun i _ => ?_)
  -- both reindexings reduce the AP shift to the matching forward shift
  simp only [Equiv.trans_apply, mulUnit_apply, Equiv.coe_addRight, nsmul_eq_mul]
  congr 1
  ring

-- ============================================================
-- Corollaries: dilation invariance and translation invariance
-- ============================================================

/-- **Dilation invariance** (the `t = 0` case of affine covariance): for any unit
`a`, scaling the configuration by `a` leaves the count unchanged,
`Λ_k(f₀(a·),…,f_{k-1}(a·)) = Λ_k(f₀,…,f_{k-1})`.

This is the genuinely new (multiplicative) symmetry: it is not implied by the
parent's translation invariance, nor by reflection. For instance `a = -1` gives
`Λ_k(f₀(-·),…) = Λ_k(f₀,…)`, the reflection through the origin that keeps the slot
order, distinct from the order-reversing reflection symmetry `i ↦ k-1-i`. -/
theorem kAPCount_dilate (k : ℕ) (f : Fin k → ZMod N → ℂ) (a : (ZMod N)ˣ) :
    kAPCount k (fun i y => f i ((a : ZMod N) * y)) = kAPCount k f := by
  have h := kAPCount_affine k f a 0
  simpa using h

/-- **Translation invariance** recovered as the `a = 1` case of affine covariance,
confirming that affine covariance subsumes the parent's `kAPCount_translate`. -/
theorem kAPCount_translate_of_affine (k : ℕ) (f : Fin k → ZMod N → ℂ)
    (t : ZMod N) :
    kAPCount k (fun i y => f i (y + t)) = kAPCount k f := by
  have h := kAPCount_affine k f 1 t
  simpa using h

end RothTheoremOQ03OQ01
