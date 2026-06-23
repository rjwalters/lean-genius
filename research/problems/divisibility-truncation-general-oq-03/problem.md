# Problem: Divisibility Truncation — Osculator and Continued Fraction Connection

**Slug**: divisibility-truncation-general-oq-03
**Created**: 2026-04-23
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

What is the relationship between the osculator of a divisor d (coprime to 10) and the
continued fraction expansion of 1/d? Can this connection be formalized in Lean 4?

The osculator of d is the integer c such that 10c ≡ ±1 (mod d), giving the truncation
divisibility criterion. The question asks whether c appears naturally in the continued
fraction expansion of 1/d — either as a partial quotient or as a convergent numerator.

### Plain Language

The truncation divisibility rule works because c = osculator(d) satisfies 10c ≡ ±1 (mod d).
The continued fraction expansion 1/d = [0; a₁, a₂, ...] describes how d relates to
powers of 10 via its decimal period. Both objects encode the same number-theoretic structure,
but from different perspectives. The question: is there a formal algebraic relationship
that can be proved in Lean?

### Why This Matters

Connecting the osculator (modular inverse of 10) to continued fractions would show why
divisibility rules "work" at a deeper level, unifying two algorithms for computing with d.

## Known Results

### What's Already Proven

- `divisibility-truncation-general`: Osculator-based divisibility rule formalized in Lean 4
- `divisibility-truncation-general-oq-01`: Unified positive/negative osculator theorem

### What's Still Open

- Formal relationship between osculator and continued fraction partial quotients
- Whether c = a_k for some k in [0; a₁, a₂, ..., a_n]
- Alternative: c relates to convergents p_k/q_k of the CF expansion

### Our Goal

Find and prove (or disprove) a direct algebraic connection between the osculator c of d
and the continued fraction expansion of 1/d (or equivalently d/1, or related fractions).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `divisibility-truncation-general` | Parent proof; osculator definition | Modular arithmetic, ZMod |
| `divisibility-truncation-general-oq-01` | Unified osculator theorem | Modular inverse |
| `divisibility-truncation-general-oq-02` | Extension to non-coprime divisors | Mixed base arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Direct partial quotient matching**: Show that the Euclidean algorithm step for 10 (mod d)
   produces the osculator as a partial quotient in the CF of d/10 or 10/d.
   - Why it might work: Euclidean algorithm = CF algorithm; osculator is related to the first step
   - Risk: May only give c for specific d values, not in general

2. **Convergents approach**: Show that some convergent p_k/q_k of CF(1/d) satisfies 10q_k ≡ ±p_k (mod d).
   - Why it might work: Convergents are best rational approximations and satisfy Bezout-type identities
   - Risk: The exact relationship may be complex

### Key Difficulties

- Mathlib's continued fraction API may not expose partial quotients in a form amenable to modular arithmetic
- The relationship may be approximate (osculator is close to a CF quotient) rather than exact

### What Would a Proof Need?

- Key lemma 1: CF partial quotients of d/10 relate to modular inverse of 10 (mod d) via Euclidean algorithm
- Key lemma 2: Bezout identity linking CF convergents to modular inverses
- Technical: `Nat.Coprime.modularInverse`, `GeneralizedContinuedFraction`, Euclidean algorithm lemmas

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The algebra is concrete: both osculators and CFs use the Euclidean algorithm
- Mathlib has `GeneralizedContinuedFraction` and `Nat.gcd`/modular arithmetic
- Main risk: the exact statement of the connection is unclear (exploration needed)

## Metadata

```yaml
tags:
  - number-theory
  - continued-fractions
  - osculator
  - divisibility
  - truncation
related_proofs:
  - divisibility-truncation-general
  - divisibility-truncation-general-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-23
```

**Significance**: 6/10
**Tractability**: 5/10
