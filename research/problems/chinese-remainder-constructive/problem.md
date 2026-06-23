# Problem: Chinese Remainder Theorem (Constructive)

**Slug**: chinese-remainder-constructive
**Created**: 2025-12-31
**Status**: Graduated (Completed)
**Tier**: C

## Problem Statement

### Formal Statement

$$
x \equiv a_1 \pmod{m_1}, \ldots, x \equiv a_k \pmod{m_k}
$$

For pairwise coprime moduli, there exists a unique solution modulo the product.

### Plain Language

Given congruence conditions with pairwise coprime moduli, construct the explicit solution using Bézout coefficients. The classic example is Sunzi's problem: x ≡ 2 (mod 3), x ≡ 3 (mod 5), x ≡ 2 (mod 7), which has solution x = 23.

### Why This Matters

1. **Algorithmic number theory** — CRT is fundamental for modular arithmetic
2. **Constructive proof** — Explicit Bézout-based formula
3. **Residue number systems** — Applications in computer arithmetic

## Known Results

### What's Already Proven

- **Existence/uniqueness** — Standard CRT statement
- **Bézout coefficients** — Used in explicit construction
- **Explicit solution formula** — Given coprime moduli
- **Sunzi problem** — x = 23 (mod 105) verified
- **3-moduli extension** — General case demonstrated
- **RNS application** — Residue number system connection

### Our Goal

✅ Complete — Constructive CRT with explicit formulas.

## Tractability Assessment

**Significance**: 5/10
**Tractability**: 9/10

## Metadata

```yaml
tags:
  - number-theory
  - algorithms
  - classical
  - crt
significance: 5
tractability: 9
tier: C
```
