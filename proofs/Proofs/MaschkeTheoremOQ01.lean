import Mathlib

/-!
# Maschke's Theorem and complete reducibility of group representations

For a finite group `G` and a field `k` whose characteristic does not divide `|G|`
(equivalently `(Fintype.card G : k)` is a unit, i.e. `NeZero (Fintype.card G : k)`),
every representation of `G` over `k` is **completely reducible**: every `k[G]`-submodule
is a direct summand, every short exact sequence of `k[G]`-modules splits, and the group
algebra `k[G]` is a semisimple ring.  This is Heinrich Maschke's 1899 theorem, the
cornerstone of ordinary representation theory and the gateway to character theory and the
Artin–Wedderburn structure of `k[G]`.

The technical heart is the **averaging projection**.  Given an injective `k[G]`-linear map
`f`, one first splits it merely `k`-linearly (vector spaces are always semisimple) and then
averages the splitting over the group, `π ↦ (1/|G|) ∑_{g} g · π · g⁻¹`, to make it
`k[G]`-equivariant.  This is exactly where the hypothesis `char k ∤ |G|` is used: dividing by
`|G|` requires `(Fintype.card G : k)` to be invertible.

## What this file packages

* `MaschkeTheorem.card_isUnit` — the classical hypothesis form: `(Fintype.card G : k)` is a
  unit (the bridge between "`char k ∤ |G|`" and Mathlib's `NeZero` instance).
* `MaschkeTheorem.splitting` — **the heart**: an injective `k[G]`-linear map admits an
  equivariant left inverse (the averaging projection).
* `MaschkeTheorem.exists_isCompl` — **classical Maschke**: every `k[G]`-submodule has a
  complement.
* `MaschkeTheorem.exists_complement` — the same, unfolded as `p ⊓ q = ⊥ ∧ p ⊔ q = ⊤`.
* `MaschkeTheorem.isSemisimpleModule` / `isSemisimpleRing` — every representation is
  semisimple and `k[G]` is a semisimple ring.
* `MaschkeTheorem.surjection_splits` — every surjection of `k[G]`-modules splits
  (projectivity / the lifting form of complete reducibility).
* `MaschkeTheorem.injection_splits` — every injection of `k[G]`-modules splits (the
  extension / injective form), recovering `splitting` as a special case.
* `MaschkeTheorem.quotient_iso_submodule` — every quotient representation is isomorphic to a
  subrepresentation (a hallmark of complete reducibility).

## Sharpness (the modular case)

The hypothesis `char k ∤ |G|` is essential.  Over `k = 𝔽_p` with `G = ℤ/p`, the regular
representation `𝔽_p[ℤ/p]` has the augmentation submodule (kernel of `∑ a_g g ↦ ∑ a_g`) with
**no** complement: the short exact sequence `0 → aug → 𝔽_p[ℤ/p] → 𝔽_p → 0` does not split,
so complete reducibility fails and `𝔽_p[ℤ/p]` is not semisimple.  This modular boundary is
recorded here as framing; the formal content below is the non-modular theorem and its
corollaries.

## References

* Maschke, *Beweis des Satzes, dass diejenigen endlichen linearen Substitutionsgruppen …*,
  Math. Ann. 50 (1898).
* Mathlib: `Mathlib/RepresentationTheory/Maschke.lean`,
  `Mathlib/RingTheory/SimpleModule/Basic.lean`.
-/

open scoped MonoidAlgebra

namespace MaschkeTheorem

universe u

variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G]
  [NeZero (Fintype.card G : k)]
variable {V : Type u} [AddCommGroup V] [Module k[G] V]
variable {W : Type u} [AddCommGroup W] [Module k[G] W]

/-- **Classical hypothesis form.** Over a field, `NeZero (Fintype.card G : k)` says exactly
that the group order is invertible: `(Fintype.card G : k)` is a unit.  This is the precise
sense in which "the characteristic of `k` does not divide `|G|`" enters Maschke's theorem —
it is what lets us divide by `|G|` when averaging over the group. -/
omit [Group G] in
theorem card_isUnit : IsUnit (Fintype.card G : k) :=
  (isUnit_iff_ne_zero).2 (NeZero.ne _)

/-- **The heart of Maschke's theorem — the averaging projection.**
An injective `k[G]`-linear map `f : V → W` admits a `k[G]`-linear left inverse `g`
(so `g ∘ f = id`).  Concretely `g` is obtained by taking any `k`-linear splitting and
averaging it over `G`, which is `k[G]`-equivariant precisely because `(Fintype.card G : k)`
is invertible. -/
theorem splitting (f : V →ₗ[k[G]] W) (hf : LinearMap.ker f = ⊥) :
    ∃ g : W →ₗ[k[G]] V, g.comp f = LinearMap.id :=
  MonoidAlgebra.exists_leftInverse_of_injective f hf

/-- **Maschke's theorem (classical statement).** Every `k[G]`-submodule of a representation
`V` is a direct summand: it has a complementary subrepresentation. -/
theorem exists_isCompl (p : Submodule k[G] V) : ∃ q : Submodule k[G] V, IsCompl p q :=
  MonoidAlgebra.Submodule.exists_isCompl p

/-- Maschke's theorem unpacked: every subrepresentation `p` has a complement `q` meeting it
trivially (`p ⊓ q = ⊥`) and spanning everything together (`p ⊔ q = ⊤`).  This is the explicit
"`V = p ⊕ q` as representations" statement. -/
theorem exists_complement (p : Submodule k[G] V) :
    ∃ q : Submodule k[G] V, p ⊓ q = ⊥ ∧ p ⊔ q = ⊤ := by
  obtain ⟨q, hq⟩ := exists_isCompl p
  exact ⟨q, hq.inf_eq_bot, hq.sup_eq_top⟩

/-- **Complete reducibility.** Every representation of `G` over `k` (with `char k ∤ |G|`) is a
semisimple `k[G]`-module: a (possibly infinite) direct sum of irreducible subrepresentations. -/
theorem isSemisimpleModule : IsSemisimpleModule k[G] V := inferInstance

/-- **The group algebra is semisimple.** `k[G]` is a semisimple ring; combined with
Artin–Wedderburn this makes it a finite product of matrix algebras over division rings, the
structural backbone of representation theory. -/
theorem isSemisimpleRing : IsSemisimpleRing k[G] := inferInstance

/-- **Every short exact sequence splits (lifting form).** Any surjective `k[G]`-linear map
`f : V → W` admits a `k[G]`-linear section `s` with `f ∘ s = id`.  Equivalently, every
`k[G]`-module is projective: complete reducibility lets us lift along quotients. -/
theorem surjection_splits (f : V →ₗ[k[G]] W) (hf : Function.Surjective f) :
    ∃ s : W →ₗ[k[G]] V, f.comp s = LinearMap.id :=
  IsSemisimpleModule.lifting_property f hf LinearMap.id

/-- **Every short exact sequence splits (extension form).** Any injective `k[G]`-linear map
`f : V → W` admits a `k[G]`-linear retraction `r` with `r ∘ f = id`.  This is the injective /
extension counterpart of `surjection_splits` and re-proves `splitting` through the
semisimplicity API. -/
theorem injection_splits (f : V →ₗ[k[G]] W) (hf : Function.Injective f) :
    ∃ r : W →ₗ[k[G]] V, r.comp f = LinearMap.id :=
  IsSemisimpleModule.extension_property f hf LinearMap.id

/-- **Quotients are subrepresentations.** For every subrepresentation `N`, the quotient
`V ⧸ N` is `k[G]`-linearly isomorphic to some subrepresentation of `V`.  In a completely
reducible module quotients never produce anything new — they are realized inside `V` itself. -/
theorem quotient_iso_submodule (N : Submodule k[G] V) :
    ∃ P : Submodule k[G] V, Nonempty (P ≃ₗ[k[G]] V ⧸ N) :=
  IsSemisimpleModule.exists_submodule_linearEquiv_quotient N

end MaschkeTheorem
