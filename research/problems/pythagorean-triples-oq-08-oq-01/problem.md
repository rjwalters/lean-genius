# Problem: Per-leg divisibility in primitive Pythagorean triples

**Slug**: pythagorean-triples-oq-08-oq-01
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a primitive Pythagorean triple $(a, b, c)$ with $a^2 + b^2 = c^2$,
$\gcd(a,b) = 1$:

$$
\bigl(4 \mid a \ \veebar\ 4 \mid b\bigr) \quad\text{and}\quad
\bigl(3 \mid a \ \veebar\ 3 \mid b\bigr),
$$

i.e. **exactly one** leg is divisible by $4$ and **exactly one** leg is
divisible by $3$ (the stronger, per-leg form, not merely $12 \mid ab$).

### Plain Language

It is classical that in a primitive Pythagorean triple the product of the legs
is divisible by $12$ (indeed $60 \mid abc$). The sharper statement pins this down
to individual legs: one specific leg is a multiple of $4$ and one specific leg is
a multiple of $3$ (these may or may not be the same leg). The goal is a verified,
axiom-free Lean proof of this per-leg refinement.

### Why This Matters

The product divisibility ($12 \mid ab$, $60 \mid abc$) is already in the gallery;
this leaf upgrades it to the precise per-leg statement, which is what one actually
uses when reasoning about the $m, n$ parametrization
$a = m^2 - n^2,\; b = 2mn,\; c = m^2 + n^2$. It exercises Mathlib's
`PythagoreanTriple` API and `ZMod` case analysis.

## Known Results

### What's Already Proven

- Mathlib `PythagoreanTriple` with the primitive classification
  `PythagoreanTriple.isPrimitiveClassified` ($a = m^2-n^2$, $b = 2mn$ up to swap).
- Gallery parent `pythagorean-triples-oq-08` (and `-oq-06-*`) establishes the
  product-divisibility results ($12 \mid ab$, $60 \mid xyz$), verified, 0-axiom.

### What's Still Open

- The per-leg form: a registered statement that one **named** leg is divisible
  by $4$ and one **named** leg by $3$ (exclusive-or over the two legs).

### Our Goal

Using the primitive parametrization, prove:
- exactly one of $a, b$ is even and in fact divisible by $4$ (the $2mn$ leg,
  since one of $m, n$ is even);
- exactly one of $a, b$ is divisible by $3$ (case analysis on $m, n \bmod 3$).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| pythagorean-triples-oq-08 | Direct parent; product-divisibility base | parametrization |
| pythagorean-triples-oq-06-oq-01-oq-01 | $60 \mid xyz$ via ZMod case analysis | ZMod, decide |

## Initial Thoughts

### Potential Approaches

1. **Parametrize then ZMod case-split**: reduce to
   $a = m^2-n^2,\; b = 2mn$ with $\gcd(m,n)=1$, $m \not\equiv n \pmod 2$, then
   analyze residues mod $4$ and mod $3$.
   - Why it might work: Mathlib supplies the classification; residue analysis is
     `decide`/`omega`-friendly.
   - Risk: the swap ambiguity ($a \leftrightarrow b$) requires careful "exactly
     one leg" phrasing.

2. **Direct ZMod 4 / ZMod 3 argument** from $a^2 + b^2 = c^2$ and coprimality,
   without the full parametrization.
   - Why it might work: squares mod 4 are $\{0,1\}$, mod 3 are $\{0,1\}$.
   - Risk: extracting which specific leg carries the factor needs primitivity.

### Key Difficulties

- Phrasing "exactly one leg" (`Xor'` / exclusive-or) so the swap symmetry is
  respected.
- Bridging Mathlib's `PythagoreanTriple.isPrimitiveClassified` data to the
  divisibility conclusions.

### What Would a Proof Need?

- Key lemma 1: primitive classification of the triple ($m, n$ with parity and
  coprimality conditions).
- Key lemma 2: squares mod $4$ and mod $3$ lie in $\{0,1\}$ (via `ZMod`/`decide`).
- Technical requirements: `ZMod 4`, `ZMod 3`, `Int.emod`, `omega`.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The product-divisibility cousins are already verified in the gallery.
- Mathlib's `PythagoreanTriple` classification removes the hard number theory.
- Remaining work is finite residue case analysis amenable to `decide`/`omega`.

**Estimated Effort**:
- Exploration: half a day
- If tractable: 2–3 days

## References

### Mathlib
- `Mathlib.NumberTheory.Pythagoras` / `Mathlib.NumberTheory.PythagoreanTriples`
  — `PythagoreanTriple`, `isPrimitiveClassified`.
- `Mathlib.Data.ZMod.Basic` — residue case analysis.

## Metadata

```yaml
tags:
  - number-theory
  - pythagorean-triples
  - divisibility
  - modular-arithmetic
related_proofs:
  - pythagorean-triples-oq-08
  - pythagorean-triples-oq-06-oq-01-oq-01
difficulty: medium
source: gallery-gap
created: 2026-06-24
```
