/-
# Erdős Problem #90 — Class Field Tower Axiomatization

Sub-issue (c) of parent tracker #20576 (Lean formalization of OpenAI 2026
unit-distance lower-bound construction).

This file provides the **axiomatized Hilbert class field** plus the
**explicit `Nat`-indexed class field tower definition**, providing the
structural target that Golod–Shafarevich (sub-issue b) discharges.

## Status

`status: "axiomatized"` (Strategy B of `research/MATHLIB-PREREQS-UNIT-DISTANCE.md`).

The audit doc classifies item 3 (class field theory: Hilbert class field,
idele class group, Artin reciprocity) and item 4 (class field towers) as
**missing** in Mathlib v4.26.0. Full formalization is a 6–11 person-month
program (dominated by global Artin reciprocity); the *axiomatized variant*
captured here is the Strategy B path of 2–4 person-weeks for the full
unit-distance application.

## Design choices

To stay within Lean 4's typeclass-resolution capabilities, the file uses
two complementary axiomatization layers:

1. **Per-extension axioms.** `HilbertClassFieldAxioms K H` is a `Prop`
   asserting that a *pre-supplied* candidate Hilbert class field `H`
   (with externally given `[Field H] [Algebra K H]` instances) satisfies
   the defining properties of the Hilbert class field of `K`. This keeps
   the typeclass infrastructure explicit and lets users supply `H` and
   the instances at the call-site.

2. **Tower iteration.** `classFieldTowerLevels K nextType : ℕ → Type*` is
   the explicit `Nat.rec` iteration of an externally-supplied
   `nextType : Type* → Type*` choice. `ClassFieldTowerWitness` is a
   structure bundling a level family with the per-level field instances,
   suitable for clients who need an indexed family.

3. **Infinitude predicates.** `HasInfiniteClassFieldTower K` and its
   ℓ-analogue are `Prop`-level abstractions, *not* tied to a particular
   tower witness. The Golod–Shafarevich axioms in sub-issue (b) will
   discharge these from explicit ℓ-rank bounds.

## Axiom Integrity Policy

Per `CLAUDE.md`, every structure field carrying a mathematical assumption
is counted in `meta.json` `axiomCount`. The enumeration is at the bottom
of this file (see `## Axiom Enumeration`).

This file contains **0 `axiom` declarations** and **0 sorries**.

## References

- Parent: #20576
- Audit: `research/MATHLIB-PREREQS-UNIT-DISTANCE.md` (items 3 and 4)
- Cassels–Fröhlich, "Algebraic Number Theory", Chapters VI–VII
- Mathlib adelic foundations: `Mathlib/NumberTheory/NumberField/AdeleRing.lean`,
  `Mathlib/RingTheory/DedekindDomain/FiniteAdeleRing.lean`,
  `Mathlib/NumberTheory/LocalField/Basic.lean`
- FLT project (`https://github.com/ImperialCollegeLondon/FLT`) may upstream
  relevant idele / Galois cohomology before formalization start.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.ClassGroup
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic

namespace Erdos90.ClassFieldTower

open NumberField

/-! ## Hilbert Class Field Axioms

The Hilbert class field `H` of a number field `K` is the maximal unramified
abelian extension of `K`. By global class field theory (the Artin reciprocity
isomorphism specialised to the unramified abelian case), there is a canonical
isomorphism `(H ≃ₐ[K] H) ≃* ClassGroup (𝓞_K)`.

Mathlib v4.26.0 does not yet contain a `HilbertClassField` construction, so
we package the existence and key properties as a `Prop`-valued `structure`
parameterised on a *pre-supplied* candidate `H`.
-/

/-- Axiomatic statement that the field extension `H / K` realises the
    Hilbert class field of the number field `K`.

    The candidate `H` is supplied externally together with its `Field` and
    `Algebra K H` instances; this `Prop`-valued structure carries only the
    propositional axioms that single out the Hilbert class field among all
    extensions of `K`:

    * `isGalois` : `H / K` is a Galois extension.
    * `artinIsoNonempty` : non-empty witness of the Artin reciprocity
      isomorphism `(H ≃ₐ[K] H) ≃* ClassGroup (𝓞_K)`.
    * `unramified` : `H / K` is unramified at every finite prime of `K`
      (placeholder; refinement awaits Mathlib's class field theory
      infrastructure).
    * `maximalAbelianUnramified` : universal property — any unramified
      abelian extension of `K` admits a `K`-algebra embedding into `H`
      (placeholder).

    By the axiom integrity policy in `CLAUDE.md`, the count of
    assumption-carrying fields here equals the number of new axioms
    contributed (see enumeration at end of file). -/
structure HilbertClassFieldAxioms
    (K : Type*) [Field K] [NumberField K]
    (H : Type*) [Field H] [Algebra K H] : Prop where
  /-- `H / K` is a Galois extension. -/
  isGalois : IsGalois K H
  /-- **Artin reciprocity (unramified abelian case)**: the Galois group of
      `H / K` is canonically isomorphic to the ideal class group of `𝓞_K`.
      Wrapped in `Nonempty` so the structure lands in `Prop`. -/
  artinIsoNonempty : Nonempty ((H ≃ₐ[K] H) ≃* ClassGroup (RingOfIntegers K))
  /-- `H / K` is unramified at every finite prime of `K`. The precise
      ramification statement awaits Mathlib's class field theory
      infrastructure; here we expose only the bare proposition. -/
  unramified : True
  /-- Universal property: any unramified abelian extension `L / K` admits
      a `K`-algebra embedding into `H`. The precise formulation of
      "unramified abelian extension" awaits Mathlib's infrastructure. -/
  maximalAbelianUnramified : True

/-! ## Class Field Tower (Nat-indexed iteration)

The class field tower of a number field `K` is the sequence
`K = K_0 ⊆ K_1 ⊆ K_2 ⊆ ...` where each `K_{n+1}` is the Hilbert class field
of `K_n`. The tower is *infinite* if all inclusions are strict.

We use a clean two-step axiomatization:

* `classFieldTowerLevels K nextType` is the explicit `Nat.rec` iteration of
  a supplied per-step "next field" choice `nextType : Type* → Type*`.
* `ClassFieldTowerWitness` bundles a level family together with per-level
  field instances; this is the structure consumed by sub-issue (b).

The per-step Hilbert-class-field property (`HilbertClassFieldAxioms`) is
*not* baked into `ClassFieldTowerWitness`, because doing so requires
typeclass instances that propagate through `Nat.rec` (currently impractical
in Lean 4). Instead, a witness that each step *is* a Hilbert class field
is supplied externally via `HilbertClassFieldAxioms K (nextType K)` and
its iterates.
-/

/-- Explicit `Nat.rec` iteration of a "next field" choice. Given a base
    field `K` and a function `nextType : Type u → Type u` that produces the
    next level from the current level, returns the `Nat`-indexed family of
    level types: level `0` is `K`, level `n + 1` is `nextType (level n)`.

    This is the iterator that satisfies the acceptance criterion "Class
    field tower constructed via `Nat.rec` (or equivalent)". The universe
    `u` is shared between `K` and `nextType` so that the recursion type-
    checks without requiring universe lifts. -/
def classFieldTowerLevels.{u} (K : Type u) (nextType : Type u → Type u) :
    Nat → Type u :=
  fun n => Nat.rec (motive := fun _ => Type u) K (fun _ T => nextType T) n

/-- Base case of the explicit `Nat.rec` construction: level `0` is `K`. -/
theorem classFieldTowerLevels_zero.{u}
    (K : Type u) (nextType : Type u → Type u) :
    classFieldTowerLevels K nextType 0 = K := rfl

/-- Step case of the explicit `Nat.rec` construction: level `n + 1` is
    `nextType (level n)`. -/
theorem classFieldTowerLevels_succ.{u}
    (K : Type u) (nextType : Type u → Type u) (n : Nat) :
    classFieldTowerLevels K nextType (n + 1)
      = nextType (classFieldTowerLevels K nextType n) := rfl

/-- A class field tower *witness* over `K` is a `Nat`-indexed family of
    types each equipped with field and number-field instance witnesses.

    Per-level "this is the Hilbert class field of the previous level"
    propositions are supplied separately via `HilbertClassFieldAxioms`;
    here we only bundle the level family and instance witnesses.

    The level family lives in the same universe as `K`. -/
structure ClassFieldTowerWitness.{u} (K : Type u) [Field K] [NumberField K] where
  /-- The `n`-th step of the tower. -/
  levels : Nat → Type u
  /-- Per-level field instance witness. -/
  fieldLevel : ∀ n, Field (levels n)
  /-- Per-level number-field instance witness, relative to `fieldLevel n`. -/
  numberFieldLevel : ∀ n, @NumberField (levels n) (fieldLevel n)

/-! ## ℓ-Class Field Tower

The ℓ-class field tower is the analogous construction restricted to the
*maximal pro-ℓ unramified extension* at each level. For a prime `ℓ`, the
ℓ-Hilbert class field `Hℓ` is the subfield of `H` fixed by the
non-ℓ-part of `Gal(H/K) ≅ ClassGroup 𝓞_K`. Iterating gives the ℓ-class
field tower.
-/

/-- Axiomatic statement that the field extension `Hℓ / K` realises the
    ℓ-Hilbert class field of the number field `K` for a prime `ℓ`.
    The ℓ-Hilbert class field is the maximal unramified abelian *pro-ℓ*
    extension of `K`.

    As with `HilbertClassFieldAxioms`, the candidate `Hℓ` and its instances
    are supplied externally; the structure carries only propositional
    content. -/
structure LHilbertClassFieldAxioms
    (K : Type*) [Field K] [NumberField K]
    (Hℓ : Type*) [Field Hℓ] [Algebra K Hℓ]
    (ℓ : Nat) [Fact (Nat.Prime ℓ)] : Prop where
  /-- `Hℓ / K` is a Galois extension. -/
  isGaloisℓ : IsGalois K Hℓ
  /-- The Galois group `Gal(Hℓ / K)` is pro-ℓ. Stated as the bare
      proposition `True`; the formal definition of "pro-ℓ" depends on
      infrastructure not yet in Mathlib v4.26.0. -/
  isProL : True
  /-- `Hℓ` is unramified at every finite prime of `K`. -/
  unramifiedℓ : True

/-- A witness for the ℓ-class field tower over `K`. Symmetric to
    `ClassFieldTowerWitness`, with the prime `ℓ` and a `Fact (Nat.Prime ℓ)`
    instance. -/
structure LClassFieldTowerWitness.{u}
    (K : Type u) [Field K] [NumberField K] (ℓ : Nat) [Fact (Nat.Prime ℓ)] where
  /-- The `n`-th step of the ℓ-tower. -/
  levels : Nat → Type u
  /-- Per-level field instance witness. -/
  fieldLevel : ∀ n, Field (levels n)
  /-- Per-level number-field instance witness. -/
  numberFieldLevel : ∀ n, @NumberField (levels n) (fieldLevel n)

/-! ## Infinitude predicates

The (ℓ-)class field tower is *infinite* if every level is a proper extension
of the previous one. Golod–Shafarevich (sub-issue b) provides the sufficient
condition `d_ℓ(ClassGroup 𝓞_K) > 2 + 2·√(r₁ + r₂ + 1)`. We expose the bare
predicate here; the sufficient-condition implication will be added by the
Golod–Shafarevich axiomatization in sub-issue (b).

A "proper" extension is captured here by *non-equality of types* between
consecutive levels — a weak but type-theoretically clean approximation of
the intended "strict field extension" condition. -/

/-- The class field tower over `K` is *infinite*: there exists a tower
    witness whose consecutive levels are non-equal as types. -/
def HasInfiniteClassFieldTower (K : Type*) [Field K] [NumberField K] : Prop :=
  ∃ T : ClassFieldTowerWitness K, ∀ n : Nat, T.levels n ≠ T.levels (n + 1)

/-- The ℓ-class field tower over `K` is *infinite* for the prime `ℓ`. -/
def HasInfiniteLClassFieldTower
    (K : Type*) [Field K] [NumberField K] (ℓ : Nat) [Fact (Nat.Prime ℓ)] : Prop :=
  ∃ T : LClassFieldTowerWitness K ℓ, ∀ n : Nat, T.levels n ≠ T.levels (n + 1)

/-! ## Small worked example: trivial level family

To exhibit the `Nat`-indexed iteration concretely (as required by the
acceptance criteria), we instantiate `classFieldTowerLevels` with the
*identity* `nextType`, yielding the constant level family stuck at `K`.

This is a degenerate witness — its purpose is to compile-check the shape
of `classFieldTowerLevels`, not to model an actually infinite tower. The
non-degenerate witness arrives via sub-issue (b)'s Golod–Shafarevich
construction. -/

/-- Identity `nextType` choice yields the constant level family. -/
theorem classFieldTowerLevels_id_eq.{u} (K : Type u) (n : Nat) :
    classFieldTowerLevels K (fun T => T) n = K := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [classFieldTowerLevels_succ]
    exact ih

/-! ## Axiom Enumeration

The following enumerates every assumption-carrying field in this file, per
the axiom integrity policy in `CLAUDE.md`. `meta.json` `axiomCount` must
equal the sum across all `structure`s introduced here, plus 0 `axiom`
declarations.

### `HilbertClassFieldAxioms` (4 assumption-carrying fields)

  1. `isGalois` — `H / K` is Galois.
  2. `artinIsoNonempty` — Artin reciprocity isomorphism
     `(H ≃ₐ[K] H) ≃* ClassGroup (𝓞_K)`.
  3. `unramified` — unramifiedness at all finite primes (placeholder `True`).
  4. `maximalAbelianUnramified` — universal property (placeholder `True`).

  Total: **4 fields**. The two placeholder `True` fields nonetheless count
  as axioms because the structure publicly *names* these assumptions, and
  a future de-axiomatization must replace each placeholder with the genuine
  proposition once Mathlib's class field theory lands.

### `LHilbertClassFieldAxioms` (3 assumption-carrying fields)

  1. `isGaloisℓ` — `Hℓ / K` is Galois.
  2. `isProL` — pro-ℓ property of the Galois group (placeholder `True`).
  3. `unramifiedℓ` — unramifiedness at all finite primes (placeholder `True`).

  Total: **3 fields**.

### `ClassFieldTowerWitness` (3 fields)

  1. `levels` — `Nat`-indexed family of types.
  2. `fieldLevel` — per-level field instance witness.
  3. `numberFieldLevel` — per-level number-field instance witness.

  Total: **3 fields**.

### `LClassFieldTowerWitness` (3 fields)

  Symmetric to `ClassFieldTowerWitness`. **3 fields**.

### Total axiom count for this file

  Sum: **4 + 3 + 3 + 3 = 13 assumption-carrying structure fields**.

  Plus **0** `axiom` declarations and **0** `sorry` occurrences.

  Notes for `meta.json`:
  - `axiomCount` contribution from this file: **13**.
  - `status` must be `"axiomatized"` (per `CLAUDE.md` axiom integrity policy).
  - `badge` should be `"axiom"`.

-/

end Erdos90.ClassFieldTower
