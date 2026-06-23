# minpoly-charpoly-oq-01 — Jordan Normal Form via Minpoly/Charpoly Infrastructure

**Parent gallery entry**: [`minpoly-charpoly`](../../../src/data/proofs/minpoly-charpoly/meta.json) — Minimal Polynomial vs Characteristic Polynomial of Matrices.

**OQ index in parent**: `conclusion.openQuestions[0]`.

## Open Question

> **Can the Jordan normal form theorem be formalized in Lean 4 using this infrastructure?**

That is: starting from the parent file's 17 theorems on the
`minpoly | charpoly` relationship, can one extend the development to
include the full Jordan normal form theorem
> "Every square matrix over an algebraically closed field is similar to a
> block-diagonal matrix of Jordan blocks (`λ · I + N`)"

in Lean 4 / Mathlib `v4.26.0`?

## Why It Matters

* **Capstone of the parent gallery entry.** The parent file leaves three
  open questions; OQ-01 (this one) and OQ-03 (rational canonical form)
  are the two normal-form questions. Closing OQ-01 finalises the
  alg-closed half of the parent's canonical-form story.

* **Pedagogical centrepiece.** Jordan normal form is one of the most
  taught results in linear algebra; a clean Lean formalisation would
  serve as an anchor entry in the gallery's linear-algebra track.

* **Mathlib contribution potential.** A finished JNF proof — especially
  the nilpotent-canonical-form lemma — is upstreamable.
  `Mathlib.LinearAlgebra.JordanChevalley` already exists; a sibling
  `JordanNormalForm.lean` is a natural addition.

## Scope (S1 OBSERVE — affirmative resolution)

The S1 OBSERVE iteration resolves the OQ at the strategy level:
**affirmative**, with one identified Mathlib gap (the nilpotent
canonical form). The full assembly decomposes into four child OQs of
roughly equal size; together they constitute a ~930-line roadmap.

See `state.md` for the current phase and `knowledge.md` for the
Mathlib infrastructure survey.
