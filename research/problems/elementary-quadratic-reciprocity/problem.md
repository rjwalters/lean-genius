# Problem: Zolotarev's Permutation-Based Proof of Quadratic Reciprocity

**Slug**: elementary-quadratic-reciprocity-oq-01
**Created**: 2026-03-11
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Formal Statement

**Zolotarev's Lemma**: For an odd prime p and integer a coprime to p:
(a/p) = sgn(sigma_a)

where sigma_a : Z/pZ -> Z/pZ is the permutation x -> ax and sgn is the permutation sign.

**QR via Zolotarev**: For distinct odd primes p, q, the transposition map on Z/pZ x Z/qZ has sign (-1)^((p-1)(q-1)/4), giving QR by combining with Zolotarev's lemma applied to the CRT isomorphism.

### Plain Language

The existing gallery proof uses Eisenstein's approach. Can we formalize Zolotarev's alternative proof, which derives quadratic reciprocity purely from permutation signs?

### Why This Matters

Zolotarev's proof (1872) is one of the most elegant approaches to QR, reducing number theory to group theory. It would provide a second independent formalization and showcase Lean's permutation infrastructure.

## Known Results

### What's Already Proven

- QR via Eisenstein — `proofs/Proofs/QuadraticReciprocity.lean` (fully proved via Mathlib)
- Gauss's Lemma — `ZMod.gauss_lemma` in Mathlib
- Permutation sign — `Equiv.Perm.sign` in Mathlib
- Legendre symbol computation — Mathlib's `legendreSym`

### What's Still Open

- Zolotarev's lemma (Legendre symbol = permutation sign) — not in Mathlib
- CRT-based sign computation for QR — not formalized

### Our Goal

Formalize Zolotarev's lemma and derive quadratic reciprocity from it, providing an alternative proof alongside the existing Eisenstein approach.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| elementary-quadratic-reciprocity | Direct source — Eisenstein proof to complement | Gauss/Eisenstein lemmas, lattice points |

## Initial Thoughts

### Potential Approaches

1. **Direct Zolotarev approach**: Define multiplication permutation on ZMod p, compute its sign, connect to Legendre symbol
   - Why it might work: Mathlib has `Equiv.Perm.sign`, `ZMod`, and `legendreSym`
   - Risk: CRT isomorphism interaction with permutation signs may be complex

2. **Hybrid approach**: Use Mathlib's existing QR and prove Zolotarev's lemma as a consequence
   - Why it might work: Easier since QR is already available
   - Risk: Less interesting — the point is to derive QR from Zolotarev

### Key Difficulties

- Computing the sign of the multiplication permutation on ZMod p
- The CRT isomorphism as a permutation and its sign

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- Mathlib has all building blocks (permutations, ZMod, CRT, Legendre symbol)
- The proof is conceptually clean but technically involves multiple equivalences

## Metadata

```yaml
tags:
  - number-theory
  - primes
  - modular-arithmetic
  - permutation
related_proofs:
  - elementary-quadratic-reciprocity
difficulty: challenging
source: gallery-extension
created: 2026-03-11
```

**Significance**: 7/10
**Tractability**: 7/10
