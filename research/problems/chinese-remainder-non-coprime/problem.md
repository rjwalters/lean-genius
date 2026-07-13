# Problem: CRT Extension to Polynomial Rings and PIDs

**Slug**: chinese-remainder-non-coprime
**Created**: 2026-03-06
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{In a PID } R, \text{ the system } x \equiv a_1 \pmod{m_1}, \; x \equiv a_2 \pmod{m_2}
$$
$$
\text{has a solution iff } \gcd(m_1, m_2) \mid (a_1 - a_2)
$$
$$
\text{with solution unique modulo } \text{lcm}(m_1, m_2)
$$

### Plain Language

The Chinese Remainder Theorem for non-coprime moduli extends from integers to any principal ideal domain: polynomial rings k[x], Gaussian integers, etc. The solvability condition (gcd divides the difference) and uniqueness (modulo lcm) carry over perfectly.

### Why This Matters

This algebraic generalization unifies CRT across number theory (ℤ), algebraic geometry (k[x] = polynomial interpolation), and algebraic number theory (rings of integers). The fiber product decomposition R/lcm → R/m1 ×_{R/gcd} R/m2 is a key structural result.

## Known Results

### What's Already Proven

- Non-coprime CRT over ℤ — `proofs/Proofs/ChineseRemainderNonCoprime*.lean`
- Mathlib has `ZMod.chineseRemainder`, `Ideal.quotientInfEquivQuotientProd`, `IsPrincipalIdealRing`

### What's Still Open

- CRT for general PIDs with non-coprime ideals
- Specialization to k[x]
- Fiber product decomposition

### Our Goal

Formalize non-coprime CRT for PIDs, specializing to k[x], and connect to the existing ℤ formalization.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| chinese-remainder-non-coprime | Source — ℤ case | Modular arithmetic, gcd/lcm |

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib has strong PID/Euclidean domain infrastructure
- The ℤ proof likely generalizes with minimal changes
- Ideal-theoretic CRT may already be partially in Mathlib

## Metadata

```yaml
tags:
  - algebra
  - number-theory
  - ring-theory
  - PID
  - chinese-remainder
related_proofs:
  - chinese-remainder-non-coprime
difficulty: medium
source: gallery-gap
created: 2026-03-06
```
