import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Burnside's Lemma over `Finite`: generalising `sum_card_fixedBy` off `Fintype`

## What This Proves

Mathlib's Burnside / Cauchy–Frobenius orbit-counting lemma
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group` is stated for a
`Fintype` group `G` acting on a `Fintype` set `X`:

  `∑ g : G, Fintype.card (fixedBy X g) = Fintype.card (X ⧸ G) * Fintype.card G`.

This file answers the parent's open question `oq-02`: the statement **generalises
unchanged** to the merely `Finite` setting, with no constructive `Fintype`
instances supplied.  Replacing `Fintype.card` by `Nat.card` and the finite sum by
a `finsum` (`∑ᶠ`, the canonical "sum over a `Finite` type without choosing a
`Fintype`" idiom — cf. `Group.sum_card_conj_classes_eq_card` in
`Mathlib/GroupTheory/ClassEquation.lean`):

  `∑ᶠ g : G, Nat.card (fixedBy X g) = Nat.card (orbitRel.Quotient G X) * Nat.card G`.

## Why the proof lifts unchanged

The mathematical content of Burnside's lemma is the **finiteness-free** bijection

  `MulAction.sigmaFixedByEquivOrbitsProdGroup : (Σ g : G, fixedBy X g) ≃ (X ⧸ G) × G`,

which Mathlib already provides for *any* group action — it requires no `Fintype`
or `Finite` hypotheses at all.  The original corollary only invokes finiteness to
pass from this equivalence to a `Fintype.card` identity.  Consequently the
generalisation to `Finite` is immediate: take cardinalities of both sides of the
same equivalence with `Nat.card` (which is total and instance-free), using
`Nat.card_congr`, `Nat.card_sigma`, and `Nat.card_prod`.  The single `Fintype`
instance still needed — a `Fintype G` to turn the `finsum` into a `Finset` sum —
is obtained non-constructively from `Finite G` via `nonempty_fintype`.

We then recover Mathlib's exact `Fintype` statement as a corollary, confirming the
generalisation genuinely subsumes the original.

## Status
- [x] `Finite` generalisation (`finsum` / `Nat.card` form) — `0` sorries, `0` axioms
- [x] Original `Fintype` statement recovered as a corollary

## Mathlib Dependencies
- `Mathlib.GroupTheory.GroupAction.Quotient` : `sigmaFixedByEquivOrbitsProdGroup`,
  `sum_card_fixedBy_eq_card_orbits_mul_card_group`
- `Mathlib.SetTheory.Cardinal.Finite` : `Nat.card_congr`, `Nat.card_sigma`,
  `Nat.card_prod`, `Nat.card_eq_fintype_card`
- `Mathlib.Algebra.BigOperators.Finprod` : `finsum_eq_sum_of_fintype`
-/

namespace BurnsideFinite

open MulAction

variable (G : Type*) (X : Type*) [Group G] [MulAction G X]

/-- **Burnside's lemma over `Finite`.**

For a `Finite` group `G` acting on a `Finite` set `X`, the total number of fixed
points (summed over the group as a `finsum`) equals the number of orbits times the
group order, all measured by the instance-free `Nat.card`:

  `∑ᶠ g : G, Nat.card (fixedBy X g) = Nat.card (orbitRel.Quotient G X) * Nat.card G`.

This is the `Fintype`-free generalisation of
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`.  The proof routes
through the finiteness-free bijection `sigmaFixedByEquivOrbitsProdGroup`, so no
part of the orbit-counting argument changes — only the bookkeeping that converts
the equivalence into a cardinality identity. -/
theorem sum_card_fixedBy_eq_card_orbits_mul_card_group_of_finite
    [Finite G] [Finite X] :
    ∑ᶠ g : G, Nat.card (fixedBy X g)
      = Nat.card (orbitRel.Quotient G X) * Nat.card G := by
  -- A (non-constructive) `Fintype G` lets us turn the `finsum` into a `Finset` sum.
  cases nonempty_fintype G
  rw [finsum_eq_sum_of_fintype, ← Nat.card_sigma,
    Nat.card_congr (sigmaFixedByEquivOrbitsProdGroup G X), Nat.card_prod]

/-- The original Mathlib statement
`MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, recovered as a special
case of the `Finite` generalisation.  This certifies that
`sum_card_fixedBy_eq_card_orbits_mul_card_group_of_finite` genuinely subsumes the
`Fintype` form: supplying the constructive `Fintype` instances and unfolding
`Nat.card` to `Fintype.card` returns the bundled Mathlib lemma verbatim. -/
theorem sum_card_fixedBy_eq_card_orbits_mul_card_group_recovered
    [Fintype G] [∀ g : G, Fintype (fixedBy X g)] [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g)
      = Fintype.card (orbitRel.Quotient G X) * Fintype.card G := by
  have h := sum_card_fixedBy_eq_card_orbits_mul_card_group_of_finite G X
  rw [finsum_eq_sum_of_fintype] at h
  simpa only [Nat.card_eq_fintype_card] using h

#check @sum_card_fixedBy_eq_card_orbits_mul_card_group_of_finite
#check @sum_card_fixedBy_eq_card_orbits_mul_card_group_recovered

end BurnsideFinite
