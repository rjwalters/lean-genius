import Mathlib

/-
# The abelian Inverse Galois Problem over ℚ: the cyclotomic realization

## Open Question (abel-ruffini-oq-03)

The **Inverse Galois Problem** asks which finite groups `G` arise as `Gal(L/ℚ)`
for some finite Galois extension `L/ℚ`. The general problem is open; for finite
*solvable* groups it is Shafarevich's theorem (recorded as an axiom in the sibling
entry `abel-ruffini-galois-extensions-oq-05`, since its proof needs class field
theory). For finite *abelian* groups it is a **theorem**, traditionally derived
from the Kronecker–Weber theorem together with Dirichlet's theorem on primes in
arithmetic progressions: every finite abelian group `A` is a quotient of
`(ZMod n)ˣ` for a suitable `n` and is realized inside the `n`-th cyclotomic field.

This file isolates and **proves, with zero axioms**, the load-bearing arithmetic
core of that argument, the part that `Mathlib` already supports in full:

> For every `n ≥ 1`, the `n`-th cyclotomic field `ℚ(ζₙ)` is an **abelian Galois
> extension of `ℚ`** whose Galois group is `(ZMod n)ˣ`.

Consequently every group of the form `(ZMod n)ˣ` is realized as a Galois group over
`ℚ` by an explicit abelian extension. This is exactly the family of groups out of
which the Kronecker–Weber realization builds an *arbitrary* finite abelian group:
the only remaining ingredients are Dirichlet's theorem (to find `n` with `A` a
quotient of `(ZMod n)ˣ`) and the Galois correspondence (to descend to the fixed
field). Those steps are flagged in `kroneckerWeber_realization_target` below but
are **not** part of the verified content here.

## What is proved (all 0-sorry, 0-axiom)

- `cyclotomicField_isGalois`      : `ℚ(ζₙ) / ℚ` is Galois.
- `autEquivUnitsZMod`             : `Gal(ℚ(ζₙ)/ℚ) ≃* (ZMod n)ˣ` (Mathlib's `autEquivPow`,
                                    specialized to `ℚ` via `cyclotomic.irreducible_rat`).
- `galois_mul_comm`               : the Galois group is **abelian** — `ℚ(ζₙ)/ℚ` is an
                                    abelian extension.
- `galois_finite`                 : the Galois group is finite.
- `RealizationOverRat`            : a bundle "the finite group `G` is `Gal(L/ℚ)` for a
                                    Galois extension `L/ℚ`".
- `unitsZMod_realizableOverRat`   : `(ZMod n)ˣ` is realizable over `ℚ` (the cyclotomic
                                    field is the witness).

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for each
result above.
-/

namespace AbelRuffiniOQ03

open Polynomial IsCyclotomicExtension

/-- The `n`-th cyclotomic field over `ℚ` is a Galois extension of `ℚ`. -/
theorem cyclotomicField_isGalois (n : ℕ) [NeZero n] :
    IsGalois ℚ (CyclotomicField n ℚ) :=
  IsCyclotomicExtension.isGalois (S := {n}) (K := ℚ) (L := CyclotomicField n ℚ)

/-- **Cyclotomic Galois group.** The Galois group of `ℚ(ζₙ)/ℚ` is `(ZMod n)ˣ`.
This is `Mathlib`'s `IsCyclotomicExtension.autEquivPow`, specialized to the base
field `ℚ` where the `n`-th cyclotomic polynomial is irreducible. -/
noncomputable def autEquivUnitsZMod (n : ℕ) [NeZero n] :
    (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) ≃* (ZMod n)ˣ :=
  IsCyclotomicExtension.autEquivPow (CyclotomicField n ℚ)
    (cyclotomic.irreducible_rat (NeZero.pos n))

/-- **The cyclotomic extension is abelian.** Any two automorphisms of `ℚ(ζₙ)/ℚ`
commute, because the Galois group is isomorphic to the commutative group
`(ZMod n)ˣ`. -/
theorem galois_mul_comm (n : ℕ) [NeZero n]
    (σ τ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :
    σ * τ = τ * σ := by
  have e := autEquivUnitsZMod n
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

/-- The Galois group `Gal(ℚ(ζₙ)/ℚ)` is finite. -/
theorem galois_finite (n : ℕ) [NeZero n] :
    Finite (CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ) :=
  Finite.of_equiv _ (autEquivUnitsZMod n).symm.toEquiv

/-- A bundle witnessing that the finite group `G` is the Galois group of a Galois
extension of `ℚ`. The carrier field and its `ℚ`-algebra structure are packaged as
instance fields so that `Carrier ≃ₐ[ℚ] Carrier` is well-typed. -/
structure RealizationOverRat (G : Type*) [Group G] where
  /-- The realizing field `L`. -/
  Carrier : Type
  [field : Field Carrier]
  [algebra : Algebra ℚ Carrier]
  /-- `L/ℚ` is a Galois extension. -/
  isGalois : IsGalois ℚ Carrier
  /-- An isomorphism `Gal(L/ℚ) ≃* G`. -/
  equiv : (Carrier ≃ₐ[ℚ] Carrier) ≃* G

attribute [instance] RealizationOverRat.field RealizationOverRat.algebra

/-- **Cyclotomic realization.** For every `n ≥ 1`, the group `(ZMod n)ˣ` is the
Galois group over `ℚ` of the `n`-th cyclotomic field. -/
noncomputable def unitsZModRealization (n : ℕ) [NeZero n] :
    RealizationOverRat (ZMod n)ˣ where
  Carrier := CyclotomicField n ℚ
  isGalois := cyclotomicField_isGalois n
  equiv := autEquivUnitsZMod n

/-- **`(ZMod n)ˣ` is realizable over `ℚ`** by an explicit abelian Galois extension. -/
theorem unitsZMod_realizableOverRat (n : ℕ) [NeZero n] :
    Nonempty (RealizationOverRat (ZMod n)ˣ) :=
  ⟨unitsZModRealization n⟩

/-!
## The full Kronecker–Weber realization (not verified here)

The complete abelian Inverse Galois statement — *every* finite abelian group `A`
is `Gal(L/ℚ)` for some `L` — follows from the verified core above together with two
classical inputs that are out of scope for this file:

1. **Dirichlet's theorem on primes in arithmetic progressions**, used to choose `n`
   so that `A` is a quotient of `(ZMod n)ˣ` (e.g. take distinct primes
   `p ≡ 1 (mod mᵢ)` for the invariant factors `mᵢ` of `A`).
2. **The Galois correspondence for abelian extensions**: a quotient `G/N` of an
   abelian Galois group is realized by the fixed field `L^N`, which is itself
   Galois over `ℚ` with group `G/N`.

The statement of that target theorem is recorded below for reference; we do not
assert it.

```
theorem kroneckerWeber_realization_target :
    ∀ (A : Type) [AddCommGroup A] [Finite A], Nonempty (RealizationOverRat (Multiplicative A))
```
-/

end AbelRuffiniOQ03
