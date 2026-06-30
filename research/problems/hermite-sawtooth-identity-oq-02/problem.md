# Problem: Sawtooth Identity → Lattice-Point / Eisenstein Count

**Slug**: hermite-sawtooth-identity-oq-02
**Created**: 2026-06-28T08:59:20-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

For coprime positive integers $p, q$, derive from the sawtooth identity a closed form
for the fractional-part sum

$$
\sum_{k=1}^{q-1} \left\{ \frac{kp}{q} \right\} \;=\; \frac{q-1}{2},
$$

and, more generally, a lattice-point / Eisenstein count for $\sum_{k<n} \{kp/q\}$ that
exhibits the $\tfrac{n-1}{2}$ term as the diagonal contribution. This is the
Gauss-sum / quadratic-reciprocity "lattice-point counting" input (Eisenstein's
proof of reciprocity).

### Plain Language

The fractional parts $\{kp/q\}$ for $k = 1,\dots,q-1$ are, when $\gcd(p,q)=1$, just a
permutation of $\{1/q, 2/q, \dots, (q-1)/q\}$, so they sum to $(q-1)/2$. The task is to
formalize this via the sawtooth function $((x)) = \{x\} - \tfrac12$ and connect it to
the lattice-point counting underlying Eisenstein's proof of quadratic reciprocity.

### Why This Matters

This fractional-part sum is the combinatorial heart of Eisenstein's lattice-point
proof of quadratic reciprocity and of Dedekind-sum theory. A formal version turns the
gallery's sawtooth identity into a reusable number-theoretic lemma and is a stepping
stone toward formalizing reciprocity via lattice-point counting.

## Known Results

### What's Already Proven

- The sawtooth identity $((x)) = \{x\} - 1/2$ (off integers) — `hermite-sawtooth-identity` (parent).
- `Int.fract`, `Int.floor` API and `Nat.Coprime` — Mathlib.
- Quadratic reciprocity (Gauss/Eisenstein) — Mathlib `Mathlib.NumberTheory.LegendreSymbol.*`.

### What's Still Open

- A formal statement and proof of $\sum_{k=1}^{q-1}\{kp/q\} = (q-1)/2$ for coprime $p,q$.
- The lattice-point interpretation $\sum_{k<n}\{kp/q\}$ with the diagonal $(n-1)/2$ term isolated.

### Our Goal

Prove the clean coprime identity $\sum_{k=1}^{q-1}\{kp/q\} = (q-1)/2$ first (via the
permutation/bijection argument on residues), then state the general lattice-point form
linking to Eisenstein's count.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| hermite-sawtooth-identity | Parent; sawtooth / fractional-part identity | `Int.fract`, casework |
| (quadratic reciprocity, if present) | Target application | lattice-point counting |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Residue permutation bijection**: When $\gcd(p,q)=1$, multiplication
   by $p$ is a bijection of $(ℤ/qℤ)^\ast \cup \{0\}$, so $\{kp \bmod q : k=1,\dots,q-1\}
   = \{1,\dots,q-1\}$; hence $\sum \{kp/q\} = \sum_{j=1}^{q-1} j/q = (q-1)/2$.
   - Why it might work: `ZMod q` bijection + `Finset.sum` reindexing are well supported.
   - Risk: moving between `ZMod q` representatives and `Int.fract` of rationals.

2. **Approach B — Sawtooth pairing $((x)) + ((-x)) = 0$**: Use antisymmetry of the
   sawtooth to pair $k \leftrightarrow q-k$ and collapse the sum.
   - Why it might work: directly uses the parent identity.
   - Risk: handling the fixed point / endpoints carefully.

### Key Difficulties

- Translating between `ZMod q` residue arithmetic and `Int.fract (k*p/q : ℚ)`.
- Endpoint/diagonal bookkeeping in the general $\sum_{k<n}$ version.

### What Would a Proof Need?

- Key lemma 1: for coprime $p,q$, $k \mapsto kp \bmod q$ is a bijection on $\{1,\dots,q-1\}$.
- Key lemma 2: $\{kp/q\} = (kp \bmod q)/q$.
- Technical requirements: `ZMod`, `Finset.sum_bij`, `Int.fract` lemmas.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The coprime identity is a clean, well-known result with a short bijective proof.
- Mathlib has strong `ZMod`/`Finset.sum_bij`/`Int.fract` support.
- The general lattice-point form is a modest extension once the core identity lands.

**Estimated Effort**:
- Exploration: 1 day
- If tractable (coprime identity): a few days
- If hard (full Eisenstein lattice count): 1–2 weeks

## References

### Papers
- Eisenstein (1844) — lattice-point proof of quadratic reciprocity.
- Rademacher & Grosswald, *Dedekind Sums* — sawtooth-sum identities.

### Online Resources
- Wikipedia, "Dedekind sum", "Proofs of quadratic reciprocity (Eisenstein)".

### Mathlib
- `Mathlib.Algebra.Order.Floor` / `Int.fract` — fractional part API.
- `Mathlib.Data.ZMod.Basic` — residue arithmetic and bijections.
- `Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity` — target application.

## Metadata

```yaml
tags:
  - number-theory
  - floor-function
  - fractional-part
  - quadratic-reciprocity
  - dedekind-sums
related_proofs:
  - hermite-sawtooth-identity
difficulty: medium
source: gallery-gap
created: 2026-06-28T08:59:20-07:00
```
