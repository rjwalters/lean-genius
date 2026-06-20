import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-
# The Stabilizer Sum: ∑ₓ |Stab(x)| = |X/G| · |G|

## Open Question (lagrange-theorem-oq-02-oq-01-oq-02)
For a finite group `G` acting on a finite set `X`, evaluate the sum of stabilizer
orders over the *points* of `X`:

  `∑ₓ |Stab(x)| = |X⧸G| · |G|`.

This is the "dual" of Burnside / Cauchy–Frobenius, which sums fixed-point counts
over the *group*: `∑_g |Fix(g)| = |X⧸G| · |G|`.

## Answer: YES — it is the same orbit-count `|X⧸G| · |G|`, by Fubini on fixed pairs.

Both sums count the **same set of fixed pairs** `{(g, x) : g • x = x}`:

  `∑ₓ |Stab(x)| = #{(x, g) : g • x = x} = #{(g, x) : g • x = x} = ∑_g |Fix(g)|`,

because `g ∈ Stab(x) ↔ g • x = x ↔ x ∈ Fix(g)` — the two membership conditions are
literally the same proposition.  The swap of summation order is realized by the
explicit `Equiv`

  `stabSigmaEquivFixedBySigma : (Σ x : X, Stab(x)) ≃ (Σ g : G, Fix(g))`,

which transposes a pair `(x, ⟨g, hg⟩)` to `(g, ⟨x, hx⟩)` (the proofs `hg` and `hx`
coincide).  Composing it with Mathlib's finiteness-free orbit-counting bijection
`MulAction.sigmaFixedByEquivOrbitsProdGroup : (Σ g, Fix(g)) ≃ (X⧸G) × G` and taking
`Nat.card` of both sides yields the result directly — never passing through
Burnside's sum as an intermediate quantity.

We state the result with the instance-free `Nat.card` and a `finsum` (`∑ᶠ`), the
canonical way to sum over a `Finite` type without choosing a `Fintype`, exactly as
the sibling `BurnsideFinite` entry does, and then recover the bundled `Fintype`
form as a corollary.

No new axioms: `propext`, `Classical.choice`, `Quot.sound` only.
-/

namespace StabilizerSum

open MulAction

variable (G : Type*) (X : Type*) [Group G] [MulAction G X]

/-- **The transposition of fixed pairs.** Sending `(x, ⟨g, hg⟩)` to `(g, ⟨x, hx⟩)`
is a bijection between `Σ x, Stab(x)` and `Σ g, Fix(g)`: the stabilizer condition
`g ∈ stabilizer G x` and the fixed-point condition `x ∈ fixedBy X g` are both the
single proposition `g • x = x`. -/
def stabSigmaEquivFixedBySigma :
    (Σ x : X, stabilizer G x) ≃ Σ g : G, fixedBy X g where
  toFun := fun ⟨x, g, hg⟩ => ⟨g, x, (mem_fixedBy).2 ((mem_stabilizer_iff).1 hg)⟩
  invFun := fun ⟨g, x, hx⟩ => ⟨x, g, (mem_stabilizer_iff).2 ((mem_fixedBy).1 hx)⟩
  left_inv := fun ⟨_, _, _⟩ => rfl
  right_inv := fun ⟨_, _, _⟩ => rfl

/-- **The stabilizer sum over `Finite`.**

For a `Finite` group `G` acting on a `Finite` set `X`, the sum of stabilizer orders
over the points of `X` equals the number of orbits times the group order:

  `∑ᶠ x : X, Nat.card (stabilizer G x) = Nat.card (X ⧸ G) · Nat.card G`.

The proof transposes the fixed-pair sigma type via `stabSigmaEquivFixedBySigma`,
then applies Mathlib's orbit-counting bijection `sigmaFixedByEquivOrbitsProdGroup`
— so it equals `|X⧸G|·|G|` without computing Burnside's group-side sum. -/
theorem sum_card_stabilizer_eq_card_orbits_mul_card_group_of_finite
    [Finite G] [Finite X] :
    ∑ᶠ x : X, Nat.card (stabilizer G x)
      = Nat.card (orbitRel.Quotient G X) * Nat.card G := by
  -- A (non-constructive) `Fintype X` turns the `finsum` into a `Finset` sum.
  cases nonempty_fintype X
  rw [finsum_eq_sum_of_fintype, ← Nat.card_sigma,
    Nat.card_congr ((stabSigmaEquivFixedBySigma G X).trans
      (sigmaFixedByEquivOrbitsProdGroup G X)),
    Nat.card_prod]

/-- The same identity in bundled `Fintype` form, summing `Fintype.card (stabilizer G x)`
over a `Finset` and matching the shape of Mathlib's
`sum_card_fixedBy_eq_card_orbits_mul_card_group`. -/
theorem sum_card_stabilizer_eq_card_orbits_mul_card_group
    [Fintype G] [Fintype X] [∀ x : X, Fintype (stabilizer G x)]
    [Fintype (orbitRel.Quotient G X)] :
    ∑ x : X, Fintype.card (stabilizer G x)
      = Fintype.card (orbitRel.Quotient G X) * Fintype.card G := by
  have h := sum_card_stabilizer_eq_card_orbits_mul_card_group_of_finite G X
  rw [finsum_eq_sum_of_fintype] at h
  simpa only [Nat.card_eq_fintype_card] using h

end StabilizerSum
