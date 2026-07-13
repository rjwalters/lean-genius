# Problem: Base-b Divisibility Rule for Moduli Coprime to the Base

**Slug**: divisibility-rules-oq-01-oq-01-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\text{Let } b\ge 2,\ d\ge 1,\ \gcd(d,b)=1,\ k=\operatorname{ord}_d(b).\ \text{Then } d\mid N \iff d\mid \sum_{i} c_i\,(b^{\,i\bmod k})\ \text{for the base-}b\text{ digits } c_i \text{ of } N,\ \text{i.e. } N\equiv\textstyle\sum_i c_i\,b^{\,i\bmod k}\pmod d.
$$

### Plain Language

The familiar 'casting out nines' and the cyclic divisibility rules for 7, 11, 13 in base 10 all come from one fact: if gcd(d, b) = 1, then b has a multiplicative order k = ord_d(b) modulo d, so the powers bⁱ cycle with period k. Hence a base-b number N ≡ Σ cᵢ·bⁱ ≡ Σ cᵢ·b^(i mod k) (mod d), reducing the divisibility test to a finite weighted digit sum. The parent entry establishes the base-10 / power-of-10 form; this open question generalizes it to an arbitrary base b with any modulus d coprime to b, with the period given by ord_d(b).

### Why This Matters

- Unifies every classical digit-based divisibility rule (mod 3, 9, 7, 11, 13, …) into a single base-b theorem, parameterized only by ord_d(b).
- Cleanly exhibits the role of the multiplicative order and Euler's theorem in elementary number theory, with a fully constructive period.
- Mathlib has ZMod, orderOf, and Nat.ModEq machinery; the digit expansion N = Σ cᵢ bⁱ is Nat.ofDigits, so the statement is directly expressible.

## Known Results

### What's Already Proven

- Parent divisibility-rules-oq-01-oq-01 (verified, 0-axiom): power-of-10 / base-10 divisibility rule for moduli coprime to 10.
- Mathlib: Nat.ofDigits, Nat.ofDigits_modEq and friends relating ofDigits b to ofDigits (b % d) mod d.
- Mathlib: orderOf in ZMod d, ZMod.pow_card / Euler totient bound, Nat.ModEq.pow.

### What's Still Open

- Q1: Formalize b^(i) ≡ b^(i mod k) (mod d) where k = orderOf (b : (ZMod d)ˣ) (or orderOf of the ZMod d unit), for gcd(d,b)=1.
- Q2: Conclude N ≡ Σ cᵢ b^(i mod k) (mod d) from the base-b digit expansion N = Nat.ofDigits b c, and hence the divisibility biconditional d ∣ N ↔ d ∣ (folded digit sum).
- Q3 (stretch): recover concrete rules — base 10, d=9,11 (k=1,2), d=7,13 (k=6) — as one-line specializations.

### Our Goal

Prove the base-b cyclic divisibility rule N ≡ Σ cᵢ b^(i mod ord_d(b)) (mod d) for gcd(d,b)=1, generalizing the parent's base-10 result, verified/0-axiom.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| divisibility-rules-oq-01-oq-01 | parent open question | source of this extension |
| divisibility-rules | ancestor in the same family | shared definitions and lemmas |
| divisibility-rules-oq-01 | ancestor in the same family | shared definitions and lemmas |

## Initial Thoughts

### Potential Approaches

1. **Order-of-b period folding**: Set k=orderOf of the unit b in (ZMod d)ˣ; prove bⁱ≡b^(i mod k) (mod d) via Nat.ModEq.pow and the order property b^k≡1; lift to the ofDigits sum.
   - Risk: Constructing the unit (b : (ZMod d)ˣ) requires the coprimality witness; handle d=1 trivially.
2. **ofDigits mod reduction**: Use Nat.ofDigits_mod / Nat.ofDigits_modEq to push the modulus inside the digit sum, then apply the period-folding lemma.
   - Risk: Matching Mathlib's exact ofDigits congruence lemma names and the direction of the ModEq.

### Key Difficulties

- Promoting b to a unit of ZMod d from gcd(d,b)=1 to access orderOf.
- Bridging Nat.ofDigits (a Nat-level sum) with ZMod d arithmetic and the period reduction i ↦ i mod k.

### What Would a Proof Need?

- orderOf b in (ZMod d)ˣ and b^k = 1.
- bⁱ ≡ b^(i mod k) (mod d).
- Nat.ofDigits congruence to fold the digit weights mod d.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The parent base-10 result is verified/0-axiom; this is a parameterization of the same argument over a general base.
- Mathlib's ofDigits and orderOf/ZMod APIs cover all the moving parts.
- The main work is API plumbing between Nat.ofDigits and ZMod d, plus the order extraction.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Papers
- G. H. Hardy, E. M. Wright, An Introduction to the Theory of Numbers (1938) §IX — divisibility tests.
- O. Ore, Number Theory and Its History (1948) — cyclic divisibility rules.

### Online Resources
- https://en.wikipedia.org/wiki/Divisibility_rule
- https://en.wikipedia.org/wiki/Multiplicative_order

### Mathlib
- Mathlib.Data.Nat.Digits — Nat.ofDigits, Nat.ofDigits_modEq
- Mathlib.Data.ZMod.Basic — ZMod d, units, orderOf
- Mathlib.GroupTheory.OrderOfElement — orderOf, pow_orderOf_eq_one

## Metadata

```yaml
tags:
  - seeker-selected
  - number-theory
  - divisibility
  - modular-arithmetic
  - multiplicative-order
  - euler-theorem
  - generalization
related_proofs:
  - divisibility-rules
  - divisibility-rules-oq-01
  - divisibility-rules-oq-01-oq-01
difficulty: medium
source: proof-suggestion
created: 2026-06-24
```
