import Mathlib.Tactic
import Proofs.WilsonsTheoremOQ02ExtOQ01

/-
# Gauss-Wilson Theorem: Rings of Integers in Number Fields (OQ-02-ext OQ-02)

**Open question (`wilsons-theorem-oq-02-ext-oq-02`):** Does the Gauss-Wilson
theorem extend from `(ZMod n)ˣ` to the unit groups of quotients `O_K / 𝔞`,
where `O_K` is the ring of integers of an algebraic number field `K` and `𝔞`
is a nonzero ideal?

**Answer: yes — and for a structural reason that requires nothing specific to
number fields.** For a nonzero ideal `𝔞`, the quotient `O_K / 𝔞` is a *finite
commutative ring* `R`, so its unit group `Rˣ` is a finite abelian group. The
general two-involution theorem proved in `WilsonsTheoremOQ02ExtOQ01.lean`,

  `prod_eq_one_or_unique_involution` :
      `∏ x : G, x = 1`  or  `∃! involution t`, in which case `∏ x : G, x = t`,

holds for *every* `[CommGroup G] [Fintype G] [DecidableEq G]`. Specialising to
`G = Rˣ` gives Gauss-Wilson for any finite commutative ring, and hence for
`O_K / 𝔞`. The Lean corollary `prod_units_eq_one_or_unique_involution` below is
therefore a one-line instantiation.

## Number-theoretic refinement

Writing `𝔞 = ∏ 𝔭ᵢ^{eᵢ}` and using CRT,
`(O_K/𝔞)ˣ ≅ ∏ (O_K/𝔭ᵢ^{eᵢ})ˣ`. The product of all units equals `-1` **iff**
`-1` is the *unique* element of order two, i.e. iff exactly one local factor
contributes an involution and that involution is `-1` — the number-field
analogue of the classical `n ∈ {1, 2, 4, pᵏ, 2pᵏ}` criterion.

A genuinely new phenomenon (absent for `ZMod n`, where the product is always
`±1`): when `-1 = 1` in `R` (e.g. `R = ℤ[i]/(2)`, residue characteristic 2),
the product can be a unit of order two that is neither `1` nor `-1`
(`∏ u = i` in `ℤ[i]/(2)`). The abstract characterization still holds verbatim.

Verified by exact integer enumeration over `94` quotients of five rings of
integers (`ℤ[i]`, `ℤ[ω]`, `ℤ[√-2]`, `ℤ[√2]`, `ℤ[(1+√5)/2]`): every product
equals the predicted unique involution (or `1`), with `0` mismatches. See
`research/problems/wilsons-theorem-oq-02-ext-oq-02/verification/`.

## Main results

* `prod_units_eq_one_or_unique_involution` — Gauss-Wilson for an arbitrary
  finite commutative ring `R`: `∏ u : Rˣ, u` is the unique element of order two
  if one exists, and `1` otherwise.
* `prod_units_coe_eq_neg_one` — classical packaging: when `-1` is the unique
  involution of `Rˣ`, the product of all units, coerced to `R`, is `-1`.

Both apply directly to `R = O_K / 𝔞`.
-/

namespace WilsonsTheoremOQ02ExtOQ02

open Finset

/-- **Gauss-Wilson for a finite commutative ring.** The product of all units of
    a finite commutative ring is the unique element of order two of `Rˣ` if such
    an element exists, and `1` otherwise.

    This is `WilsonsTheoremOQ02ExtOQ01.prod_eq_one_or_unique_involution`
    specialised to the finite abelian group `G = Rˣ`. Taking `R = O_K / 𝔞`
    (finite for any nonzero ideal `𝔞` of a ring of integers `O_K`) answers the
    open question affirmatively. -/
theorem prod_units_eq_one_or_unique_involution
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] :
    (∏ u : Rˣ, u = 1) ∨
      (∃ t : Rˣ, t ≠ 1 ∧ t ^ 2 = 1 ∧
        (∀ s : Rˣ, s ^ 2 = 1 → s = 1 ∨ s = t) ∧ ∏ u : Rˣ, u = t) :=
  WilsonsTheoremOQ02ExtOQ01.prod_eq_one_or_unique_involution

/-- **Classical packaging.** If `-1` is the unique element of order two in `Rˣ`,
    then the product of all units of `R`, taken in `R`, equals `-1`. This is the
    direct analogue of the classical `(ZMod n)ˣ` statement
    `∏ (units) = -1 ⇔ n ∈ {1,2,4,pᵏ,2pᵏ}`. -/
theorem prod_units_coe_eq_neg_one
    {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    (hne : (-1 : Rˣ) ≠ 1)
    (huniq : ∀ s : Rˣ, s ^ 2 = 1 → s = 1 ∨ s = -1) :
    (∏ u : Rˣ, (u : R)) = -1 := by
  have hsq : (-1 : Rˣ) ^ 2 = 1 := by ext; push_cast; ring
  have hprod : (∏ u : Rˣ, u) = (-1 : Rˣ) :=
    WilsonsTheoremOQ02ExtOQ01.prod_eq_unique_involution hne hsq huniq
  have hcoe : ((∏ u : Rˣ, u : Rˣ) : R) = ∏ u : Rˣ, (u : R) :=
    map_prod (Units.coeHom R) _ _
  rw [← hcoe, hprod]
  simp

end WilsonsTheoremOQ02ExtOQ02
