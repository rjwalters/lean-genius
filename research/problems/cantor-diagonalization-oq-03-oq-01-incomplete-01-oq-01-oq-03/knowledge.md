# Knowledge: Quantitative Cantor — strict cardinality gap #A < #(A → Prop)

**Problem id**: `cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01-oq-03`
**Gallery entry / Lean file**: `cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01-oq-03` →
`proofs/Proofs/CantorDiagonalizationOQ03OQ01Incomplete01OQ01OQ03.lean`
**Status**: SOLVED — 0 sorry, 0 axiom (foundational only), gallery status `verified`.

## Summary

Answers **open question #3** of the parent `cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01`
("Reflexive Objects and the Fixed-Point Property"):

> Quantitative Cantor: extend `cantor_surjective_recovered` to a cardinality gap statement
> `|A| < |A → Prop|` rather than mere non-surjectivity.

Delivered three theorems:

- `cardinality_gap_set (A) : #A < #(Set A)` — `Cardinal.mk_set` + `Cardinal.cantor`.
- `cardinality_gap (A) : #A < #(A → Prop)` — the requested statement; `= cardinality_gap_set A`
  because `Set A` is definitionally `A → Prop`.
- `not_surjective_of_cardinality_gap (e : A → (A → Prop)) : ¬ Surjective e` — recovers the parent's
  qualitative result from the gap via `Cardinal.mk_le_of_surjective`, proving the gap is *strictly
  stronger* than non-surjectivity.

## Key insight

The open question is a one-line consequence of the standard cardinal Cantor theorem
(`Cardinal.cantor : a < 2 ^ a`) once `A → Prop` is identified with its power set `Set A`
(definitional). The parent's bespoke Lawvere / `EvalStructure` development produced Cantor only at
the level of maps (non-surjectivity) and never phrased it at the cardinal level; the cardinal
inequality is what pins the *direction* and *strictness* of the size difference, and it re-implies
the map-level statement.

## Mathlib facts used

- `Cardinal.cantor (a : Cardinal) : a < 2 ^ a` — `SetTheory/Cardinal/Order.lean`.
- `Cardinal.mk_set {α} : #(Set α) = 2 ^ #α` — same file.
- `Cardinal.mk_le_of_surjective {f : α → β} : Surjective f → #β ≤ #α`.

## Possible follow-ups (not pursued this session)

- **Iterated gap / beth hierarchy.** `#A < #(A → Prop) < #((A → Prop) → Prop) < …`; connect to
  Mathlib's `Cardinal.beth` and strict monotonicity of `2 ^ ·`.
- **Monotone version.** `#A ≤ #B → #(A → Prop) ≤ #(B → Prop)` and its strict form, i.e. the power
  operation is (strictly) monotone — a structural companion to the single gap.

These are modest; the primary open question is fully answered.

## Session log

### Session 2026-07-03 (Session 1) — ACT → COMPLETED

**Mode**: FRESH · **Outcome**: completed (0 sorry, 0 axiom)

**What I did**
- Read the parent entry; identified that `cantor_surjective_recovered` is only qualitative and that
  OQ #3 asks for the cardinal inequality.
- Verified Mathlib names in the local cache (`Cardinal.cantor`, `Cardinal.mk_set`,
  `Cardinal.mk_le_of_surjective`; `#` is `scoped prefix:max`).
- Wrote `CantorDiagonalizationOQ03OQ01Incomplete01OQ01OQ03.lean` (3 theorems + 1 defeq `example`).
- Built the module in the guarded Docker wrapper (8 GB): **build succeeded**, all three `#check`s
  print the expected signatures.
- Added the gallery entry (`meta.json`, `annotations.json`) and a reciprocal `extended-by`
  cross-reference on the parent.

**Key findings**
- The cardinal-level statement is immediate from `Cardinal.cantor` via the `Set A ≡ A → Prop`
  defeq; the interesting content is closing the loop (`not_surjective_of_cardinality_gap`) to show
  it subsumes the parent.

**Files modified**
- `proofs/Proofs/CantorDiagonalizationOQ03OQ01Incomplete01OQ01OQ03.lean` (new)
- `src/data/proofs/cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01-oq-03/{meta,annotations}.json` (new)
- `src/data/proofs/cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01/meta.json` (+reciprocal crossRef)

**Next steps**
- Optional: iterated/beth-hierarchy gap or the monotone power version (see above).
