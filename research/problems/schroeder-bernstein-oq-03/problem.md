# Problem: Myhill's Isomorphism Theorem in Lean — Computable Bijections

**Slug**: schroeder-bernstein-oq-03
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-open-question

## Problem Statement

### Plain Language

Myhill's isomorphism theorem (1955): if sets A and B have computable injections into
each other, they are computably isomorphic (there exists a computable bijection between
them). This is the computable analogue of Schroeder-Bernstein. Formalize it in Lean 4
using Mathlib's `Computable` or `Primrec` typeclasses.

### Formal Statement

```lean
-- Target (sketch):
theorem myhill_isomorphism
    (f : α → β) (g : β → α)
    (hf : Computable f) (hg : Computable g)
    (hf_inj : Function.Injective f) (hg_inj : Function.Injective g) :
    ∃ (h : α ≃ β), Computable h ∧ Computable h.symm := by
  sorry
```

### Why This Matters

Extends the Schroeder-Bernstein gallery proof (Wiedijk #25) with computability content.
The classical Schroeder-Bernstein theorem has a well-known constructive proof via
back-and-forth; making it computable requires controlling which branch of the
construction is taken, yielding a computable bijection.

## Known Results

### What's Already Proven

- `SchroederBernstein.lean`: classical SB theorem (if f, g are injections, ∃ bijection)
- `SchroederBernsteinOQ02.lean`, `SchroederBernsteinOQ04.lean`: extensions
- Mathlib has `Computable`, `Primrec`, `Encodable` for computability theory
- Back-and-forth construction is already formalized in `SchroederBernstein.lean`

### Our Goal

Show the back-and-forth construction of the bijection is computable when f and g are
computable, using Lean's `Computable` typeclass.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| schroeder-bernstein | Base theorem | back-and-forth construction |

## Initial Thoughts

### Potential Approaches

1. **Trace the back-and-forth construction**: The existing SB proof computes a bijection
   via partition into A-sequences. Check if each step can be made decidable/computable.

2. **Search Mathlib for computability of back-and-forth**: `Nat.rec`, `Computable.ite`

### Key Difficulties

- Mathlib's computability hierarchy may not have all needed lemmas
- The partition in back-and-forth requires a decidable predicate (reachability)
- `Encodable` instance needed for the domain types

## Tractability Assessment

**Difficulty**: Medium — the math is known, but fitting into Lean's computability
typeclass hierarchy requires careful engineering.

## Metadata

```yaml
tags:
  - set-theory
  - computability
  - wiedijk-100
  - extension
  - computable-functions
related_proofs:
  - schroeder-bernstein
difficulty: medium
source: gallery-open-question
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 5/10
