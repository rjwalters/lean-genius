# Problem: Lawvere Fixed-Point Theorem — Setoid Generalization

**Slug**: `cantor-diagonalization-oq-04-oq-01`
**Parent**: `cantor-diagonalization-oq-04` (Lawvere FPT, Type-level retraction version)
**Tier**: B (significance 5, tractability 4)
**Status**: COMPLETED — verified-final (S1 SOLVED 2026-05-07; gallery PR #16393)

## Statement

### Open Question (verbatim from Seeker brief)

> "Can the retraction version of Lawvere's Fixed-Point Theorem be
> formalized in a general topos or CCC in Lean, beyond the Type
> category?"

### Mathematical statement (post-S1 resolution)

A first step toward CCC generality, working internally to Lean's type
theory:

Let `Y` be a type, `≈ : Y → Y → Prop` a setoid equivalence relation
(bundled as `Setoid Y` in Mathlib). A `CodesEndomorphismsSetoid Y s`
structure consists of:

- An "indexing" object `Y` with setoid `s`;
- An encode/decode pair `encode : (Y → Y) → Y`, `decode : Y → (Y → Y)`;
- A retraction condition: `∀ f y, decode(encode(f))(y) ≈ f(y)`
  (pointwise equivalence, NOT strict equality).

**Theorem** (`lawvere_fixpoint_setoid`):

> Given a `CodesEndomorphismsSetoid Y s` structure, every function
> `f : Y → Y` has a **setoid fixed point** — an element `p : Y` with
> `f(p) ≈ p`. (Note: `f` need NOT preserve `≈`.)

## Why this matters

1. **Strict generalization of the parent**: the Type-level Lawvere FPT
   (parent slug `cantor-diagonalization-oq-04`) requires strict
   equality `decode(encode f) = f`. The setoid version only requires
   pointwise `≈`. Discrete setoid (where `≈ ⟺ =`) recovers the parent
   theorem exactly.

2. **CCC bridge**: in a cartesian closed category (or topos), equality
   is typically replaced by isomorphism or coherent equivalence.
   Setoids internalize "equivalence relation as data" inside Lean's
   type theory, which is the foundational step before lifting to
   Mathlib's `CartesianClosed` typeclass machinery.

3. **No morphism requirement on `f`**: a striking feature of the
   setoid version is that `f` need not be a setoid morphism (need not
   preserve `≈`). The fixed point exists nonetheless, which exposes
   that Lawvere's argument is at heart about the encode/decode
   retraction's coherence, not about `f`'s structural properties.

## Known results

### Proven (S1, this slug)

1. `lawvere_fixpoint_setoid` — setoid fixed point exists for arbitrary
   `f : Y → Y`.
2. `no_coding_setoid_if_fixpoint_free` — contrapositive: if `f` is
   fixpoint-free up to `≈`, no `CodesEndomorphismsSetoid` structure
   exists.
3. `typeToSetoidCoding` — a Type-level coding induces a discrete-setoid
   coding.
4. `lawvere_type_from_setoid` — recovers the parent Type-level theorem
   as the special case where `s = discreteSetoid` (i.e., `≈ ⟺ =`).
5. `cannot_code_endomorphisms_bool_setoid` — `Bool` cannot code its
   own 4 endomorphisms because `Bool.not` is fixpoint-free (up to
   discrete `=`).
6. `cantor_setoid_no_surjection` — classical Cantor's theorem (no
   surjection `Y → (Y → Bool)`) in the setoid setting.
7. `cannot_code_endomorphisms_nat_parity` — `ℕ` cannot code its
   endomorphisms even up to parity equivalence (≡ mod 2).

### Open (deferred to follow-up sub-OQs)

A. **Mathlib `CartesianClosed` lift**: formalize the abstract CCC
   version (Lawvere 1969) at the category level, using Mathlib's
   `CategoryTheory.CartesianClosed` typeclass + terminal object.
   Would not import via this slug's setoid layer; would be a parallel
   formalization.
B. **Admissible-setoid characterization**: which setoids `Y` admit a
   `CodesEndomorphismsSetoid` structure? The S1 impossibility results
   for `Bool` (discrete) and `ℕ` (parity) show specific obstructions;
   a positive characterization is open.

## Mathlib infrastructure

All bearers were available at the slug's Mathlib pin (no upstream gaps
required):

- `Setoid` bundle: `Mathlib.Data.Setoid.Basic`.
- `eq_equivalence`: `Init.Logic` (for the discrete-setoid recovery).
- `congr_fun`, `iff_of_eq`: `Init.Core`, `Init.Logic` (Cantor diagonal step).
- Russell-style diagonal argument: classical (no Mathlib bearer needed).

## Deliverable

- `proofs/Proofs/CantorDiagonalizationOQ04OQ01.lean` — 166 LOC, 8
  theorems, 3 defs + 1 structure (`CodesEndomorphismsSetoid`), 0
  sorries, 0 axioms.
- `src/data/proofs/cantor-diagonalization-oq-04-oq-01/`:
  - `meta.json` — `meta.status: "verified"`, `meta.badge: "original"`,
    `meta.axiomCount: 0`, `meta.theoremCount: 8`, `meta.lineCount: 166`.
  - `annotations.json` — sectioned annotations.
  - `index.ts` — gallery integration.
- PR #16393 (merged 2026-05-07).

## References

- F.W. Lawvere, "Diagonal arguments and cartesian closed categories"
  (1969) — original CCC-level result.
- Parent: `cantor-diagonalization-oq-04` (Type-level retraction
  version).
- `proofs/Proofs/CantorDiagonalization.lean` — root Cantor diagonal
  argument (sibling in the same family).
- Gallery entry: `src/data/proofs/cantor-diagonalization-oq-04-oq-01/`.

## Coordination

This problem is **research-complete**. No active researcher work is
anticipated. The follow-up directions A and B above could be opened as
NEW sub-OQ slugs by a future Seeker pass.
