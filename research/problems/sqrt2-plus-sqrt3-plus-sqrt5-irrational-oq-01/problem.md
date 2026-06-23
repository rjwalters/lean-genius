# Problem: Irrationality of √2 + √3 + √5 + √7

**Slug**: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `sqrt2-plus-sqrt3-plus-sqrt5-irrational`)

## Problem Statement

### Formal Statement

$$
\alpha = \sqrt{2} + \sqrt{3} + \sqrt{5} + \sqrt{7} \notin \mathbb{Q}.
$$

Equivalently, $\alpha$ is an algebraic number of degree $16$ over $\mathbb{Q}$. It is a
primitive element of $\mathbb{Q}(\sqrt 2,\sqrt 3,\sqrt 5,\sqrt 7)$, which has degree $16$
over $\mathbb{Q}$: the Galois group $(\mathbb{Z}/2)^4$ flips each radical's sign
independently, and by $\mathbb{Q}$-linear independence of $\sqrt2,\sqrt3,\sqrt5,\sqrt7$ the
$16$ sums $\pm\sqrt2\pm\sqrt3\pm\sqrt5\pm\sqrt7$ are pairwise distinct, so the stabilizer of
$\alpha$ is trivial and its minimal polynomial is the degree-$16$ product over these $16$
conjugates. (The elementary iterated-squaring route does **not** build this degree-$16$
minimal polynomial: it stops earlier at a lower-degree residual identity in $\alpha$ carrying
a single non-square surd, whose irrationality closes the argument.)

### Plain Language

The parent proof shows that a sum of three distinct square roots of squarefree integers is
irrational by squaring repeatedly until all radicals are eliminated, then checking that the
resulting rational equation has no solution. This problem extends the technique to **four**
summands: prove that adding $\sqrt 7$ keeps the sum irrational, which requires one more
squaring step and produces an identity of degree $8$ in $\alpha$.

### Why This Matters

The chain-of-squarings method is the elementary, Mathlib-friendly route to irrationality of
sums of radicals, avoiding heavy Galois machinery. Pushing it from three to four summands is
the natural stress test: it shows the method scales, and it forces a clean account of why the
intermediate fields stay distinct (linear disjointness of $\mathbb{Q}(\sqrt p)$ for distinct
primes). It is a concrete, tractable formalization target that strengthens the gallery's
coverage of elementary algebraic-number arguments.

## Known Results

### What's Already Proven

- `sqrt2-plus-sqrt3-plus-sqrt5-irrational` — irrationality of $\sqrt2+\sqrt3+\sqrt5$ by iterated squaring (parent gallery proof).
- Mathlib: `Nat.Prime.irrational_sqrt`, `irrational_nrt_of_notint_nrt`, and the `Irrational` API for $\sqrt p$.
- Linear independence of $\{1,\sqrt2,\sqrt3,\sqrt6,\dots\}$ over $\mathbb{Q}$ (folklore; reconstructible via minimal-polynomial degree arguments).

### What's Still Open

- A formalized irrationality proof for $\sqrt2+\sqrt3+\sqrt5+\sqrt7$ (via a residual surd identity, or the full degree-16 minimal polynomial).
- A reusable lemma schema: irrationality of $\sum_{i=1}^k \sqrt{p_i}$ for distinct primes $p_i$.

### Our Goal

Define `α := √2 + √3 + √5 + √7` in Lean and prove `Irrational α` using three squaring steps
(isolate $\sqrt7$ and square; isolate the surviving cross term and square; repeat), reducing
to a rational contradiction. As a by-product, produce the explicit residual identity in
$\alpha$ (degree 8 in $\alpha$, carrying a single surd); squaring once more yields the
degree-16 minimal polynomial of $\alpha$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sqrt2-plus-sqrt3-plus-sqrt5-irrational | Direct parent; same method with one fewer radical | iterated squaring, rational contradiction |
| sqrt2-plus-sqrt3-irrational | Two-summand base case | single squaring |
| nth-root-irrational | Irrationality of individual radicals | `irrational_nrt`, prime valuation |

## Initial Thoughts

### Potential Approaches

1. **Iterated squaring (recommended)**: Set $\beta = \alpha - \sqrt7$; square to push $\sqrt7$
   into a rational-plus-radical expression in $\sqrt2,\sqrt3,\sqrt5$, then reuse the parent
   proof's three-radical structure on the remainder.
   - Why it might work: mechanical, elementary, mirrors a proof already in the gallery.
   - Risk: bookkeeping of cross terms ($\sqrt{6},\sqrt{10},\sqrt{14},\dots$) is error-prone in Lean.

2. **Field-degree argument**: Show $[\mathbb{Q}(\sqrt2,\sqrt3,\sqrt5,\sqrt7):\mathbb{Q}]=16$ and
   that $\alpha$ is a primitive element (degree $16$), hence $\alpha\notin\mathbb{Q}$.
   - Why it might work: conceptually clean, leverages Mathlib `FiniteDimensional`/`IntermediateField`.
   - Risk: the degree-16 tower and primitivity claims are heavier than the elementary route.

### Key Difficulties

- Managing the growing set of mixed surd cross terms through each squaring without losing track of which are rational.
- Proving the surviving radical (e.g. $\sqrt2\sqrt3\sqrt5\sqrt7=\sqrt{210}$) is itself irrational to close the contradiction.

### What Would a Proof Need?

- Key lemma 1: $\mathbb{Q}$-linear independence of square roots of distinct squarefree integers.
- Key lemma 2: a "square once, isolate one radical" reduction lemma reusable across summand counts.
- Technical requirements: Mathlib `Irrational`, `Nat.Prime.irrational_sqrt`, `Polynomial.aeval`, `ring`/`nlinarith`.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**:
- The three-summand version already exists in the gallery; this is a bounded extension.
- All required Mathlib lemmas exist; the work is identity bookkeeping, not new theory.
- The residual identity (degree 8 in $\alpha$, with a single surd) is fully explicit and machine-verifiable via `ring`.

**Estimated Effort**:
- Exploration: hours
- If tractable: a few days
- If hard: 1–2 weeks (only if the elementary route balloons and the field-degree path is needed)

## References

### Papers
- Niven, *Irrational Numbers* (Carus Monograph 11, 1956) — classical sums-of-radicals irrationality.
- Besicovitch (1940), "On the linear independence of fractional powers of integers" — disjointness of radical extensions.

### Online Resources
- Parent gallery entry `sqrt2-plus-sqrt3-plus-sqrt5-irrational` and its Lean source.

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Pow` / `Mathlib.RingTheory.Int.Basic` — irrationality of roots.
- `Mathlib.FieldTheory.IntermediateField` — for the optional degree-tower route.

## Metadata

```yaml
tags:
  - number-theory
  - irrationality
  - algebraic-numbers
  - radicals
related_proofs:
  - sqrt2-plus-sqrt3-plus-sqrt5-irrational
  - sqrt2-plus-sqrt3-irrational
  - nth-root-irrational
difficulty: low
source: proof-suggestion
created: 2026-06-14
```
