# The Abelian Inverse Galois Problem over ℚ — Cyclotomic Realization

## Result

For every `n ≥ 1`, the `n`-th cyclotomic field `ℚ(ζₙ)` is an **abelian Galois
extension of `ℚ`** whose Galois group is `(ZMod n)ˣ`. Consequently every group of
the form `(ZMod n)ˣ` is a Galois group over `ℚ`. Verified with **0 added axioms**
(`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`).

## Why this matters

The inverse Galois problem is open in general; for finite **solvable** groups it is
Shafarevich's theorem (class field theory), axiomatized in the sibling entry
`abel-ruffini-galois-extensions-oq-05`. For finite **abelian** groups it is a
*theorem*. The classical proof:

1. Write the target finite abelian group `A` as a product of cyclic groups
   `∏ ℤ/mᵢℤ`.
2. By **Dirichlet's theorem**, pick distinct primes `pᵢ ≡ 1 (mod mᵢ)`. Then
   `Gal(ℚ(ζ_{pᵢ})/ℚ) ≅ (ZMod pᵢ)ˣ` is cyclic of order `pᵢ − 1`, which surjects onto
   `ℤ/mᵢℤ`.
3. Pass to the fixed field of the relevant subgroup (Galois correspondence), and
   take the compositum, to realize `A` as `Gal(L/ℚ)`.

The single arithmetic engine of this argument is the structure of the cyclotomic
Galois group, `Gal(ℚ(ζₙ)/ℚ) ≅ (ZMod n)ˣ`. **That is exactly what this entry
verifies**, leaving Dirichlet and the Galois descent as named, out-of-scope inputs.

## Lean / Mathlib specifics

- The cyclotomic field is `CyclotomicField n ℚ` with the instance
  `IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)` (needs `[NeZero n]`).
- `IsCyclotomicExtension.isGalois` gives `IsGalois ℚ (CyclotomicField n ℚ)`. It is a
  **theorem, not an instance** — must be applied explicitly with named arguments
  `(S := {n}) (K := ℚ) (L := …)`.
- `IsCyclotomicExtension.autEquivPow L h : Gal(L/K) ≃* (ZMod n)ˣ` requires
  `h : Irreducible (cyclotomic n K)`. Over `ℚ` use
  `Polynomial.cyclotomic.irreducible_rat (hpos : 0 < n)`
  (`Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean`); supply `hpos` as
  `NeZero.pos n`.
- `Gal(E/F)` is notation for `E ≃ₐ[F] E`.
- Abelianness is obtained by **transport**: `(ZMod n)ˣ` is a `CommGroup`, so
  `e.injective` together with `map_mul`/`mul_comm` (where `e := autEquivPow …`)
  proves any two automorphisms commute. Finiteness transports the same way via
  `Finite.of_equiv _ e.symm.toEquiv`.

## Gotcha: bundling realizability

To state "`G` is `Gal(L/ℚ)` for some Galois `L/ℚ`" as a reusable object, the carrier
field's `Field` and `Algebra ℚ` instances must be available when forming the
Galois-group type `L ≃ₐ[ℚ] L`. A plain existential `∃ (_ : Field L) (_ : Algebra ℚ L), …`
does **not** register those binders as instances, so `L ≃ₐ[ℚ] L` fails to elaborate.
The fix used here is a `structure RealizationOverRat` with the `Field`/`Algebra`
fields declared as **instance-implicit** (`[field : …]`, `[algebra : …]`), which Lean
makes available for instance resolution in the later field types
(`attribute [instance]` is also added for downstream use).

## Verification

Docker build infra was down; verified offline from the main `proofs/` checkout with
`LAKE_UNSAFE=1 lake env lean Proofs/AbelRuffiniOQ03.lean` (exit 0, no errors), and
axioms confirmed via inline `#print axioms` on all five public results.
