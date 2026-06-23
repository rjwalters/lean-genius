import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# The Orbit-Stabilizer Family over `Nat.card`

## What This Proves

This file answers `oq-01` of the parent
`lagrange-theorem-oq-02-oq-02-oq-01-oq-01` (Burnside's lemma over `Finite`).  The
parent observed that Mathlib's orbit-counting lemma
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` lifts off `Fintype` to
the merely `Finite` setting because its mathematical core is a *finiteness-free
bijection*.  Here we push the **same observation** through the other orbit-counting
identity that bijection's machinery bundles — the **orbit-stabilizer theorem** —
giving it a uniformly `Nat.card`-stated form.

Mathlib states orbit-stabilizer only for `Fintype`:

  `MulAction.card_orbit_mul_card_stabilizer_eq_card_group (b) [Fintype α] … :`
  `  Fintype.card (orbit α b) * Fintype.card (stabilizer α b) = Fintype.card α`.

We replace every `Fintype.card` by the total, instance-free `Nat.card`:

  `Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G`,

and add the companion **index form** `Nat.card (orbit G x) = Nat.card (G ⧸ stabilizer G x)`
(orbit size equals the index of the stabilizer — the orbit-counting half of
Lagrange's theorem).

## Why the proofs lift unchanged — and need *no* finiteness at all

The content is the finiteness-free bijection
`MulAction.orbitProdStabilizerEquivGroup : orbit G x × stabilizer G x ≃ G`
(and its sibling `orbitEquivQuotientStabilizer : orbit G x ≃ G ⧸ stabilizer G x`),
provided by Mathlib for *any* group action with no `Fintype`/`Finite` hypotheses.
Because `Nat.card` is total (it is `0` on infinite types) and `Nat.card_prod`,
`Nat.card_congr` hold unconditionally, transporting the bijection through
`Nat.card` requires **no finiteness instance whatsoever** — strictly more general
than even the parent's `Finite` Burnside form, which still needed a `Fintype G` to
collapse its `finsum`.  We recover Mathlib's exact `Fintype` statement as a
corollary, confirming the generalisation subsumes the original.

## Status
- [x] `Nat.card` orbit-stabilizer product — `0` sorries, `0` axioms, no finiteness
- [x] `Nat.card` orbit/stabilizer-index form
- [x] Original `Fintype` statement recovered as a corollary

## Mathlib Dependencies
- `Mathlib.GroupTheory.GroupAction.Quotient` : `orbitProdStabilizerEquivGroup`,
  `orbitEquivQuotientStabilizer`, `card_orbit_mul_card_stabilizer_eq_card_group`
- `Mathlib.SetTheory.Cardinal.Finite` : `Nat.card_congr`, `Nat.card_prod`,
  `Nat.card_eq_fintype_card`
-/

namespace OrbitStabilizerFinite

open MulAction

variable (G : Type*) (X : Type*) [Group G] [MulAction G X]

/-- **Orbit-stabilizer theorem over `Nat.card`.**

For any group `G` acting on any `X` and any point `x : X`,

  `Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G`.

This is the `Fintype`-free generalisation of Mathlib's
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`.  The proof transports the
finiteness-free bijection `orbitProdStabilizerEquivGroup` through `Nat.card`, so it
needs **no** `Finite` or `Fintype` instance — every step is unconditional. -/
theorem card_orbit_mul_card_stabilizer_eq_card_group_nat (x : X) :
    Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup G x)]

/-- **Orbit size equals stabilizer index, over `Nat.card`.**

  `Nat.card (orbit G x) = Nat.card (G ⧸ stabilizer G x)`.

The orbit-counting half of Lagrange's theorem, obtained by transporting the
finiteness-free bijection `orbitEquivQuotientStabilizer` through `Nat.card`.  Again
no finiteness hypothesis is required. -/
theorem card_orbit_eq_card_quotient_stabilizer_nat (x : X) :
    Nat.card (orbit G x) = Nat.card (G ⧸ stabilizer G x) :=
  Nat.card_congr (orbitEquivQuotientStabilizer G x)

/-- The original Mathlib statement
`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`, recovered as a special
case of the `Nat.card` generalisation: supplying the constructive `Fintype`
instances and unfolding `Nat.card` to `Fintype.card` returns the bundled Mathlib
lemma verbatim. -/
theorem card_orbit_mul_card_stabilizer_eq_card_group_recovered (x : X)
    [Fintype G] [Fintype (orbit G x)] [Fintype (stabilizer G x)] :
    Fintype.card (orbit G x) * Fintype.card (stabilizer G x) = Fintype.card G := by
  have h := card_orbit_mul_card_stabilizer_eq_card_group_nat G X x
  simpa only [Nat.card_eq_fintype_card] using h

#check @card_orbit_mul_card_stabilizer_eq_card_group_nat
#check @card_orbit_eq_card_quotient_stabilizer_nat
#check @card_orbit_mul_card_stabilizer_eq_card_group_recovered

end OrbitStabilizerFinite
