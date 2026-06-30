# Problem: Quadratic Reciprocity via Zolotarev / Algorithmic Well-Definedness

**Slug**: quadratic-reciprocity-algorithm-oq-03
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `quadratic-reciprocity-algorithm`)

## Problem Statement

### Formal Statement

The parent proof presents quadratic reciprocity as a *computation*: an algorithm that evaluates
the Jacobi symbol $\left(\frac{a}{n}\right)$ by repeated flipping and reduction. The open
question asks whether reciprocity can be **derived from the algorithm itself** — by proving the
evaluation procedure is well-defined (returns the same value no matter the order of reduction
steps) — most cleanly via **Zolotarev's lemma**:

$$
\left(\frac{a}{p}\right) = \operatorname{sgn}(\pi_a), \qquad
\pi_a : x \mapsto a x \bmod p \ \text{a permutation of } \mathbb{Z}/p\mathbb{Z},
$$

so that the Legendre symbol equals the sign of the multiplication-by-$a$ permutation, and
reciprocity becomes a statement about composing permutation signs.

### Plain Language

The gallery has an *algorithm* that computes Legendre/Jacobi symbols by a flip-and-reduce loop
(like the Euclidean algorithm). This problem asks for a proof of reciprocity that lives at the
same algorithmic level: show the symbol equals the sign of a permutation (Zolotarev), and then
reciprocity drops out from how those permutation signs interact — no Gauss sums, no lattice-point
counting.

### Why This Matters

Mathlib already has a quadratic-reciprocity proof (Gauss-sum / Eisenstein style). A
permutation-sign proof is independently valuable: it is the most "computational" of the 200+
known proofs, it connects directly to the gallery's algorithmic presentation, and Zolotarev's
lemma (`Legendre = sgn of multiplication permutation`) is a clean, reusable result not currently
isolated in the gallery.

## Known Results

### What's Already Proven

- `quadratic-reciprocity-algorithm` — the flip-and-reduce evaluation algorithm and its correctness (parent).
- Mathlib: `legendreSym`, `jacobiSym`, `ZMod.quadratic_reciprocity` (Gauss-sum proof), `Equiv.Perm.sign`.
- Zolotarev's lemma is classical and provable from `Equiv.Perm.sign` + cyclic-group structure of $(\mathbb{Z}/p)^\times$.

### What's Still Open (in this gallery)

- A formalized Zolotarev lemma: $\left(\frac{a}{p}\right) = \operatorname{sgn}(x \mapsto ax)$.
- Reciprocity rederived from Zolotarev via the sign of a transposition / shuffle permutation.

### Our Goal

Formalize Zolotarev's lemma in Lean and use it to prove $\left(\frac{p}{q}\right)\left(\frac{q}{p}\right) = (-1)^{\frac{p-1}{2}\frac{q-1}{2}}$
for odd primes $p\neq q$, reusing Mathlib's `Equiv.Perm.sign` rather than Gauss sums.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| quadratic-reciprocity-algorithm | Direct parent; the algorithmic presentation | flip-and-reduce, Jacobi symbol |
| quadratic-reciprocity (gallery) | Alternative proof to cross-check the statement | Gauss sums / Eisenstein |
| primitive-roots | Cyclic structure of $(\mathbb{Z}/p)^\times$ used by Zolotarev | generators, orders |

## Initial Thoughts

### Potential Approaches

1. **Zolotarev permutation-sign proof (recommended)**: prove `legendreSym p a = Perm.sign (mulPerm a)`,
   then compute the sign of the $(p,q)$-shuffle permutation via lattice-point parity.
   - Why it might work: `Equiv.Perm.sign` is well developed in Mathlib; the lemma is short once the cyclic structure is invoked.
   - Risk: the final shuffle-sign computation reproduces the same parity count as Eisenstein's proof — care needed to keep it genuinely permutation-theoretic.

2. **Algorithm-confluence proof**: prove the flip-and-reduce evaluator is confluent (order-independent), and read reciprocity off the rewrite rules.
   - Why it might work: matches the literal wording of the open question.
   - Risk: confluence formalization can be heavier than just proving Zolotarev directly.

### Key Difficulties

- Tying `legendreSym` (a `ZMod`-valued symbol) to `Equiv.Perm.sign` (a unit of $\{\pm1\}$) with the right coercions.
- The shuffle-permutation sign computation for the reciprocity step.

### What Would a Proof Need?

- Key lemma 1: Zolotarev — Legendre symbol = sign of multiplication permutation.
- Key lemma 2: sign of the row/column shuffle on $\mathbb{Z}/p \times \mathbb{Z}/q$ equals $(-1)^{\frac{p-1}{2}\frac{q-1}{2}}$.
- Technical requirements: `Equiv.Perm.sign`, `ZMod.legendreSym`, cyclic-group generators.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Zolotarev is a well-known, finite, elementary lemma and Mathlib has strong permutation-sign support.
- Reciprocity already exists in Mathlib, so the statement is fixed and cross-checkable.
- The main work is the sign-of-shuffle computation, which is concrete.

**Estimated Effort**:
- Exploration: days
- If tractable: 1–3 weeks
- If hard: 1 month (if confluence route is pursued instead)

## References

### Papers
- Zolotarev (1872), "Nouvelle démonstration de la loi de réciprocité de Legendre".
- Rousseau (1994) and others — modern permutation-sign expositions.

### Online Resources
- Parent gallery entry `quadratic-reciprocity-algorithm`.

### Mathlib
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` — existing proof + statement.
- `Mathlib.GroupTheory.Perm.Sign` — permutation signs.

## Metadata

```yaml
tags:
  - number-theory
  - quadratic-reciprocity
  - permutations
  - zolotarev
related_proofs:
  - quadratic-reciprocity-algorithm
  - primitive-roots
difficulty: medium
source: proof-suggestion
created: 2026-06-14
```
