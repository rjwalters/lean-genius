# Problem: Rice's Theorem as Lawvere Instance

**Slug**: cantor-diagonalization-oq-03-oq-01-oq-02
**Created**: 2026-04-04T02:41:19-07:00
**Status**: Active
**Source**: cantor-diagonalization-oq-03-oq-01 <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

Derive Rice's theorem as a Lawvere instance: Val = {computable functions}, f = 'complement a non-trivial semantic property', yielding Rice's theorem (no non-trivial property of computable functions is decidable).

### Formal Statement

$$
\text{Rice's Theorem: For any non-trivial semantic property } P \text{ of computable functions,}
\text{ the set } \{e \mid P(\varphi_e)\} \text{ is undecidable.}
$$

### Plain Language

Rice's theorem says you cannot decide any non-trivial property of what a program computes (as opposed to how it runs). This is a consequence of Lawvere's Fixed-Point Theorem applied to the category of computable functions. We want to derive Rice's theorem explicitly as a special case of the Lawvere FPT gallery proof.

### Why This Matters

Rice's theorem is one of the most important results in computability theory. Deriving it as a Lawvere instance demonstrates the unifying power of the categorical framework and would create a fully machine-verified proof of Rice's theorem via this elegant route.

## Known Results

### What's Already Proven

- Lawvere Fixed-Point Theorem — gallery proof cantor-diagonalization-oq-03-oq-01
- Basic computability theory in Mathlib (partial)

### What's Still Open

- Formal derivation of Rice's theorem as a Lawvere instance in Lean 4
- Lean encoding of "computable functions" as the evaluation category

### Our Goal

Instantiate the Lawvere FPT gallery proof with Val = computable functions and f = semantic property complement to derive Rice's theorem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cantor-diagonalization-oq-03-oq-01 | Parent: Lawvere Fixed-Point Theorem | Category theory, fixed points |
| cantor-diagonalization-oq-03-oq-01-oq-01 | Sibling: Close 2 sorries in categorical bridge | Categorical eval |
| cantor-diagonalization-oq-03-oq-01-oq-03 | Sibling: Gödel as Lawvere instance | Logic |

## Initial Thoughts

### Potential Approaches

1. **Direct instantiation**: Apply the Lawvere FPT with the computable functions category
   - Why it might work: The theorem statement is abstract enough
   - Risk: Lean may not have a suitable computability formalization

2. **Classical Rice proof translated**: Prove Rice's theorem independently, then show it matches the Lawvere framework
   - Why it might work: Classical proof is well-known
   - Risk: May not cleanly instantiate the Lawvere FPT

### Key Difficulties

- Mathlib's computability theory coverage (Turing machines, computable functions)
- Encoding the point-surjectivity condition for the computable function case
- Formalizing "non-trivial semantic property" in Lean 4

### What Would a Proof Need?

- Key lemma 1: Computable functions form a suitable category for the Lawvere FPT
- Key lemma 2: The diagonal construction yields Rice's undecidability conclusion
- Technical requirements: Mathlib computability library access

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- Requires Mathlib computability theory which may have gaps
- The Lawvere instantiation is conceptually clear but technically involved
- Rice's theorem has independent proofs but the Lawvere route needs category-theoretic machinery

**Estimated Effort**:
- Exploration: 2-3 days
- If tractable: 2-3 weeks
- If hard: unknown

## References

### Papers
- Rice, H.G. (1953) — "Classes of recursively enumerable sets and their decision problems"
- Lawvere, F.W. — "Diagonal arguments and cartesian closed categories"

### Online Resources
- Mathlib computability module

### Mathlib
- `Mathlib.Computability` — Turing machines and computable functions
- `Mathlib.CategoryTheory` — category theory

## Metadata

```yaml
tags:
  - computability
  - rices-theorem
  - lawvere
  - category-theory
  - undecidability
related_proofs:
  - cantor-diagonalization-oq-03-oq-01
difficulty: challenging
source: cantor-diagonalization-oq-03-oq-01
category: extension
created: 2026-04-04T02:41:19-07:00
```

**Significance**: 8/10
**Tractability**: 6/10
