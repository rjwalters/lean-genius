import Mathlib

/-
# The Artin Realizability Direction: the verifiable half of the inverse Galois problem

## Open Question (abel-ruffini-galois-extensions-oq-05-oq-02)

A companion to `abel-ruffini-galois-extensions-oq-05`, where Shafarevich's theorem
("every finite solvable group is `Gal(L/ℚ)` for some `L`") is recorded as an
**axiom** because its proof needs class field theory, embedding problems and the
cohomology of number fields.

This file isolates and **proves, with zero axioms**, the genuinely elementary part
of the inverse Galois story: *Artin's theorem*. For any finite group `G` acting on a
field `F`, the extension `F / F^G` over the fixed field is Galois, and when the
action is faithful the group `G` is isomorphic to its Galois group, with field
degree equal to `|G|`.

## Why this is the "easy direction" — and why ℚ is the whole difficulty

Artin's theorem shows that **every finite group is the Galois group of some field
extension**: embed `G ↪ Sym(G)` (Cayley) and let it permute the variables of a
rational function field `K(x_g : g ∈ G)`; the action is faithful, so by the theorem
below `G ≃* Gal(K(x_g) / K(x_g)^G)`. Realizability *per se* is therefore
unconditional and elementary.

The entire content of the inverse Galois problem — Shafarevich's theorem and the
still-open general case — is the demand that the **base field be `ℚ`** (a fixed,
arithmetically rigid field) rather than an auxiliary field `F^G` that we are free to
build from `G` itself. This entry makes that dividing line precise: everything below
is machine-checked from `Mathlib`'s development of Artin's theorem with no
assumptions, whereas the `ℚ`-version remains the axiom in the parent file.

## What is proved (all 0-sorry, 0-axiom)

- `extension_isGalois`     : `F / F^G` is Galois for any finite group action.
- `galoisGroupEquiv`       : faithful finite `G ≃* Gal(F / F^G)` (the realization).
- `degree_eq_card`         : `[F : F^G] = |G|`.
- `artin_realizability`    : the three facts bundled for a faithful finite action.
- `realizable_over_some_subfield` : existence form — `G` is the Galois group over
                              *some* subfield of `F`, with the expected degree.

`#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for every
result; the Shafarevich `ℚ`-realizability statement is **not** used.
-/

namespace AbelRuffiniArtinRealizability

open scoped Classical
open MulSemiringAction

variable (G : Type*) [Group G] (F : Type*) [Field F]

/-- **Artin, normality half.** For *any* finite group `G` acting on a field `F`, the
extension `F` over the fixed field `F^G` is Galois. No faithfulness is needed: this is
`Mathlib`'s `IsGalois.of_fixed_field`, packaged here as the structural backbone of the
realizability theorem. -/
theorem extension_isGalois [Finite G] [MulSemiringAction G F] :
    IsGalois (FixedPoints.subfield G F) F :=
  inferInstance

/-- **Artin, realization half.** A finite group acting *faithfully* on a field `F` is
isomorphic to the Galois group of `F` over its fixed field. This is the precise sense
in which every (faithfully acting) finite group is realized as a Galois group — over
an auxiliary base field built from the action, not over `ℚ`. -/
noncomputable def galoisGroupEquiv [Finite G] [MulSemiringAction G F] [FaithfulSMul G F] :
    G ≃* (F ≃ₐ[FixedPoints.subfield G F] F) :=
  FixedPoints.toAlgAutMulEquiv G F

/-- **Degree formula.** The fixed-field extension has degree exactly `|G|`. Together
with `galoisGroupEquiv` this records that the realization is tight: the Galois group
has order `|G|` and the extension has the matching degree. -/
theorem degree_eq_card [Fintype G] [MulSemiringAction G F] [FaithfulSMul G F] :
    Module.finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  FixedPoints.finrank_eq_card G F

/-- **Artin realizability, bundled.** For a finite group acting faithfully on a field
`F`: the extension `F / F^G` is Galois, `G` is its Galois group, and the degree equals
`|G|`. This is the verified, axiom-free counterpart of the Shafarevich axiom in the
parent file — with the base field taken to be `F^G` rather than `ℚ`. -/
theorem artin_realizability [Fintype G] [MulSemiringAction G F] [FaithfulSMul G F] :
    IsGalois (FixedPoints.subfield G F) F ∧
      Nonempty (G ≃* (F ≃ₐ[FixedPoints.subfield G F] F)) ∧
      Module.finrank (FixedPoints.subfield G F) F = Fintype.card G :=
  ⟨extension_isGalois G F, ⟨galoisGroupEquiv G F⟩, degree_eq_card G F⟩

/-- **Existence form of realizability.** A finite group acting faithfully on `F` is the
Galois group of `F` over *some* subfield `k ⊆ F`, with `[F : k] = |G|`. This is the
shape that mirrors the inverse Galois statement "`G` is a Galois group over the base"
— here the base is an auxiliary subfield rather than `ℚ`. -/
theorem realizable_over_some_subfield
    [Fintype G] [MulSemiringAction G F] [FaithfulSMul G F] :
    ∃ k : Subfield F, IsGalois k F ∧ Nonempty (G ≃* (F ≃ₐ[k] F)) ∧
      Module.finrank k F = Fintype.card G :=
  ⟨FixedPoints.subfield G F, extension_isGalois G F, ⟨galoisGroupEquiv G F⟩, degree_eq_card G F⟩

end AbelRuffiniArtinRealizability
