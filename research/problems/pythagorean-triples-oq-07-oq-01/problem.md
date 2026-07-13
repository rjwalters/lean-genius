# Problem: The Even Leg of a Primitive Pythagorean Triple is Divisible by 4

**Slug**: pythagorean-triples-oq-07-oq-01
**Created**: 2026-07-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a primitive Pythagorean triple $(a,b,c)$ with the standard parametrisation
$$
a = m^2 - n^2, \qquad b = 2mn, \qquad c = m^2 + n^2,
$$
where $\gcd(m,n) = 1$ and $m \not\equiv n \pmod 2$ (opposite parity), the even
leg satisfies
$$
4 \mid 2mn, \qquad\text{equivalently}\qquad 2 \mid mn .
$$

### Plain Language

The parent gallery entry establishes the parity dichotomy: exactly one leg of a
primitive Pythagorean triple is even. This problem proves the *next* structural
layer — that the even leg is not merely even but is in fact divisible by 4.
Because $m$ and $n$ have opposite parity, exactly one of them is even, so their
product $mn$ is even; hence the even leg $2mn$ is divisible by 4.

### Why This Matters

It sharpens the parity structure of primitive triples and is a standard stepping
stone toward finer results (e.g. Fermat's right-triangle theorem and the
enumeration of triples by hypotenuse). It sits directly on top of an existing
gallery entry and reuses its parametrisation, making it a clean, self-contained
extension.

## Known Results

### What's Already Proven

- Parent entry `pythagorean-triples-oq-07`: exactly one leg of a primitive
  triple is even (parity dichotomy).
- Mathlib `PythagoreanTriple` API: `PythagoreanTriple.isPrimitiveClassified`,
  the $(m^2-n^2,\,2mn,\,m^2+n^2)$ classification, and coprimality lemmas.

### What's Still Open

- The explicit `4 ∣` (even leg) statement as a standalone gallery theorem —
  currently the gallery only records that one leg is even, not that it is
  divisible by 4.

### Our Goal

State and prove, with 0 sorries / 0 axioms, that in a primitive Pythagorean
triple the even leg is divisible by 4 (equivalently `2 ∣ mn` in the
parametrisation), building on the parity-dichotomy entry.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pythagorean-triples-oq-07 | Parent parity dichotomy; supplies the parametrisation | parity, modular arithmetic |
| pythagorean-triples (family) | Classification and Gaussian-integer machinery | coprimality, PythagoreanTriple API |

## Initial Thoughts

### Potential Approaches

1. **Opposite-parity ⇒ mn even**: from $m \not\equiv n \pmod 2$ deduce that
   exactly one of $m, n$ is even, so `2 ∣ mn`, hence `4 ∣ 2mn`.
   - Why it might work: elementary `Nat`/`Int` parity + divisibility.
   - Risk: extracting the opposite-parity hypothesis from Mathlib's primitive
     classification in the exact form needed.

2. **Direct mod-8 / mod-4 case analysis on the classification**: reduce the even
   leg modulo 4 using `omega` / `decide` on residues of $m,n$.
   - Why it might work: fully mechanical once residues are fixed.
   - Risk: verbose; less reusable.

### Key Difficulties

- Landing Mathlib's `PythagoreanTriple.isPrimitiveClassified` output in the
  precise `(m,n)` opposite-parity form the divisibility argument consumes.
- Choosing ℤ vs ℕ to avoid subtraction/truncation pitfalls in `m² − n²`.

### What Would a Proof Need?

- Lemma: opposite parity of `m,n` ⇒ `2 ∣ m*n`.
- Lemma: `2 ∣ m*n` ⇒ `4 ∣ 2*m*n`.
- Bridge: primitive triple ⇒ classified parametrisation with opposite parity.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- Elementary parity/divisibility once the parametrisation is in hand.
- Mathlib already provides the primitive classification and coprimality facts.

**Estimated Effort**:
- Exploration: hours
- If tractable: 1–2 days

## References

### Mathlib
- `Mathlib.NumberTheory.PythagoreanTriples` — `PythagoreanTriple`,
  `isPrimitiveClassified`, coprimality and parity lemmas
- `Int.even_mul`, `Nat.even_mul`, `Int.emod` residue reasoning, `omega`

## Metadata

```yaml
tags:
  - number-theory
  - pythagorean-triples
  - parity
  - modular-arithmetic
  - diophantine
related_proofs:
  - pythagorean-triples-oq-07
difficulty: low
source: gallery-gap
created: 2026-07-05
```

**Significance**: 6/10
**Tractability**: 7/10
