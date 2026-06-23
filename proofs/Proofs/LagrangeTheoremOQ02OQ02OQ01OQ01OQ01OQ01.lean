import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# The Orbit-Counting Index Identity over `Nat.card`

## What This Proves

This file answers `oq-01` of the parent
`lagrange-theorem-oq-02-oq-02-oq-01-oq-01-oq-01` (the orbit-stabilizer family over
`Nat.card`).  The parent established, with **no** finiteness instance, the two
finiteness-free orbit-counting identities

  `Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G`     (product form)
  `Nat.card (orbit G x) = Nat.card (G ⧸ stabilizer G x)`              (quotient form)

The open question asks to **combine the product form with Lagrange's theorem**
`Nat.card (stabilizer G x) * [G : stabilizer G x] = Nat.card G` to derive the
**orbit-counting index identity**

  `Nat.card (orbit G x) = [G : stabilizer G x]`,

phrased over `Subgroup.index` (= `Nat.card (G ⧸ ·)`), entirely over `Nat.card`.

## The mathematical point: cancellation is *not* finiteness-free

There are two genuinely different derivations, and they differ precisely in their
finiteness needs.

1. **The direct route** transports the bijection `orbitEquivQuotientStabilizer`
   through `Nat.card` and unfolds `Subgroup.index`.  It is **unconditional** — it
   needs no `Finite`/`Fintype` instance at all (`card_orbit_eq_index_stabilizer`).

2. **The literal "combine and cancel" route** the OQ describes sets the two
   products equal,

     `Nat.card (orbit G x) * s = Nat.card G = [G : stabilizer G x] * s`,
     `s := Nat.card (stabilizer G x)`,

   and cancels the common factor `s`.  Right-cancellation in `ℕ` is valid **only
   when `s ≠ 0`**, i.e. only when the stabilizer is finite.  Over the *total*
   `Nat.card` (which is `0` on infinite types) this cancellation can fail for an
   infinite stabilizer, so this derivation genuinely requires `Finite G`
   (`card_orbit_eq_index_stabilizer_via_cancellation`).

Both routes prove the *same* statement, but only the direct bijection achieves it
in full generality.  This makes precise *why* Mathlib's orbit-stabilizer machinery
is built from the bijection rather than from cardinal arithmetic: the bijection,
not the cancellation, is what removes the finiteness hypothesis.

## Status
- [x] Orbit-counting index identity, unconditional — `0` sorries, `0` axioms
- [x] Same identity via the OQ's product-and-cancel route (needs `Finite G`)
- [x] Stabilizer-card positivity lemma underpinning the cancellation

## Mathlib Dependencies
- `Mathlib.GroupTheory.GroupAction.Quotient` : `orbitEquivQuotientStabilizer`,
  `orbitProdStabilizerEquivGroup`
- `Mathlib.GroupTheory.Index` : `Subgroup.index_eq_card`, `Subgroup.index_mul_card`
- `Mathlib.SetTheory.Cardinal.Finite` : `Nat.card_congr`, `Nat.card_prod`,
  `Nat.card_pos`
-/

namespace OrbitCountingIndex

open MulAction

variable (G : Type*) (X : Type*) [Group G] [MulAction G X]

/-- **Orbit-stabilizer product over `Nat.card`** (the parent's product form,
restated locally so this file is self-contained).  The content is the
finiteness-free bijection `orbitProdStabilizerEquivGroup` transported through the
total cardinal `Nat.card`; no `Finite`/`Fintype` instance is needed. -/
theorem card_orbit_mul_card_stabilizer (x : X) :
    Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup G x)]

/-- **Orbit-counting index identity, unconditional.**

  `Nat.card (orbit G x) = [G : stabilizer G x]`.

This is the orbit-counting half of Lagrange's theorem.  The proof unfolds
`Subgroup.index` to `Nat.card (G ⧸ stabilizer G x)` and transports the
finiteness-free bijection `orbitEquivQuotientStabilizer` through `Nat.card`, so it
holds for **any** group action with no finiteness hypothesis whatsoever. -/
theorem card_orbit_eq_index_stabilizer (x : X) :
    Nat.card (orbit G x) = (stabilizer G x).index := by
  rw [Subgroup.index_eq_card]
  exact Nat.card_congr (orbitEquivQuotientStabilizer G x)

/-- When `G` is finite the stabilizer is a finite, nonempty subgroup, so its
`Nat.card` is strictly positive.  This is exactly the hypothesis that makes the
right-cancellation in the OQ's "combine and cancel" derivation legitimate. -/
theorem card_stabilizer_pos [Finite G] (x : X) :
    0 < Nat.card (stabilizer G x) :=
  Nat.card_pos

/-- **Orbit-counting index identity via the OQ's product-and-cancel route.**

Combine the orbit-stabilizer product `Nat.card (orbit G x) * s = Nat.card G` with
Lagrange's theorem `[G : stabilizer G x] * s = Nat.card G` (where
`s = Nat.card (stabilizer G x)`), then cancel the common factor `s`.  The
cancellation needs `s ≠ 0`, which is supplied by `Finite G`; see
`card_orbit_eq_index_stabilizer` for the unconditional bijection-based proof of the
same statement. -/
theorem card_orbit_eq_index_stabilizer_via_cancellation [Finite G] (x : X) :
    Nat.card (orbit G x) = (stabilizer G x).index := by
  have hprod : Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G :=
    card_orbit_mul_card_stabilizer G X x
  have hlag : (stabilizer G x).index * Nat.card (stabilizer G x) = Nat.card G :=
    Subgroup.index_mul_card _
  have hcancel :
      Nat.card (orbit G x) * Nat.card (stabilizer G x)
        = (stabilizer G x).index * Nat.card (stabilizer G x) := by
    rw [hprod, hlag]
  exact Nat.eq_of_mul_eq_mul_right (card_stabilizer_pos G X x) hcancel

#check @card_orbit_mul_card_stabilizer
#check @card_orbit_eq_index_stabilizer
#check @card_orbit_eq_index_stabilizer_via_cancellation

end OrbitCountingIndex
