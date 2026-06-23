# Problem: Gödel Incompleteness: Diagonal Lemma Formalization in Lean 4

**Slug**: godel-first-incompleteness-oq01-oq-04
**Created**: 2026-04-23T13:50:28+02:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\forall \phi(x),\ \exists \sigma,\ \vdash \sigma \leftrightarrow \phi(\ulcorner \sigma \urcorner)
$$

The Diagonal Lemma (Fixed-Point Lemma): for any formula $\phi(x)$ with one free variable, there exists a sentence $\sigma$ such that the system proves $\sigma \leftrightarrow \phi(\ulcorner \sigma \urcorner)$, where $\ulcorner \sigma \urcorner$ denotes the Gödel number of $\sigma$.

### Plain Language

The existing `godel-first-incompleteness-oq01` gallery proof formalizes Gödel's First
Incompleteness Theorem using axioms 1–5, of which axioms 2–4 encode the behavior of
the Gödel diagonal/substitution function. A complete formalization of the Diagonal Lemma
in Lean 4 (without additional axioms) would eliminate axioms 2–4, reducing the assumption
count to just the `Provable` axiom and D1.

The question is: what is the **minimal Lean 4 infrastructure** required to formalize
the Diagonal Lemma? Specifically, this requires:
1. A representation of formulas as terms (Gödelization / encoding)
2. A substitution function `sub(φ, x, n)` acting on formula representations
3. A provability predicate operating on Gödel numbers
4. A proof that the diagonal construction produces a fixed point

### Why This Matters

The Diagonal Lemma is the core technical engine behind both Gödel's incompleteness
theorems and Tarski's undefinability theorem. A clean Lean 4 formalization would:
- Reduce the existing gallery proof from 5 axioms to 2 (improving the `axiomCount`)
- Provide a reusable infrastructure for other self-referential results
- Serve as a benchmark for Lean 4's expressiveness for meta-mathematics

## Known Results

### What's Already Proven

- `godel-first-incompleteness-oq01` (gallery) — First Incompleteness Theorem axiomatized
- Mathlib has basic arithmetic and natural number encodings
- Flypitch project (lean-fopl) formalized first-order logic in Lean 4

### What's Still Open

- No complete Lean 4 formalization of the Diagonal Lemma without axioms
- Gödelization (encoding syntax as natural numbers) is not in Mathlib
- Substitution as a computable function on syntactic representations

### Our Goal

Formalize the Diagonal Lemma from first principles in Lean 4, specifically:
- Define a minimal syntax representation type for arithmetic formulas
- Define a `diag : Nat → Nat` function mirroring the diagonal function
- Prove the fixed-point property: `∃ n, prove n ↔ φ (diag n)`

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| godel-first-incompleteness-oq01 | Parent proof — axioms 2-4 to eliminate | Provability axioms, classical logic |
| godel-second-incompleteness-oq02 | Uses Diagonal Lemma for Löb's theorem | Similar self-reference |
| halting-problem | Diagonal argument — structural analogue | Diagonalization |

## Initial Thoughts

### Potential Approaches

1. **Syntactic encoding approach**: Define an inductive type `Formula` for arithmetic
   formulas, a `Godel : Formula → Nat` encoding, and a `subst` function. Prove the
   diagonal property by computation.
   - Why it might work: Type-theoretic representations of syntax are natural in Lean 4
   - Risk: Full syntactic encoding is large infrastructure investment

2. **Partial approach**: Axiomatize only the diagonal function behavior (as the current
   proof does for substitution), but prove more of it computably within Lean 4's kernel.
   - Why it might work: More targeted than full syntax formalization
   - Risk: May still require non-trivial axioms

3. **Lean 4 quotient type approach**: Use Lean 4's metaprogramming (`Expr`, `Syntax`)
   as the formula representation directly.
   - Why it might work: Lean 4 has native syntax representations
   - Risk: Meta-level/object-level separation is tricky

### Key Difficulties

- Gödelization requires encoding arbitrary formulas as natural numbers (complex)
- The substitution function must be provably total and computable
- Self-reference in the statement requires careful separation of levels

### What Would a Proof Need?

- Key lemma 1: Inductive type for arithmetic formulas (or reuse of existing)
- Key lemma 2: Injective encoding `Formula → Nat` with decidable decoding
- Key lemma 3: `subst(φ, x, ⌈φ⌉)` computed via the diagonal function
- Technical: Representability of recursive functions in the system

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The Diagonal Lemma proof is standard mathematics, but Lean 4 infrastructure for
  syntax encoding requires significant setup
- The Flypitch project shows this is feasible but non-trivial
- A targeted approach (just diagonal for Peano arithmetic) is more tractable than
  full first-order logic formalization

**Estimated Effort**:
- Exploration: 2-3 days (survey existing Lean syntax libs, Flypitch approach)
- If tractable: 1-2 weeks (minimal syntax + diagonal function)
- If hard: Partial reduction of axiom count (axiom 3 or 4) as partial success

## References

### Papers
- Gödel, K. (1931) — "Über formal unentscheidbare Sätze..." (original paper)
- Boolos, Burgess, Jeffrey — "Computability and Logic" (Ch. 17: Diagonal Lemma)

### Lean Projects
- Flypitch / lean-fopl — first-order logic formalization in Lean

### Mathlib
- `Mathlib.Logic.Godel` — Gödel encoding (if exists)
- `Mathlib.Data.Nat.Basic` — Natural number arithmetic

## Metadata

```yaml
tags:
  - logic
  - foundations
  - incompleteness
  - self-reference
  - lean4
  - wiedijk-100
related_proofs:
  - godel-first-incompleteness-oq01
  - godel-second-incompleteness-oq02
  - halting-problem
difficulty: medium
source: gallery-gap
created: 2026-04-23T13:50:28+02:00
```
