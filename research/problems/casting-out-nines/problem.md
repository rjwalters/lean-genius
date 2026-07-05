# Problem: Casting Out Nines — n Is Congruent to Its Digit Sum mod 9

**Slug**: casting-out-nines
**Created**: 2026-07-05T00:06:20-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\forall n \in \mathbb{N}, \quad n \equiv \sum_{d \in \text{digits}_{10}(n)} d \pmod 9
$$

In Lean:

```lean
theorem casting_out_nines (n : ℕ) : n ≡ (Nat.digits 10 n).sum [MOD 9]
```

### Plain Language

The base-10 digit sum of any natural number leaves the same remainder mod 9 as
the number itself. This is the arithmetic basis for the classical "casting out
nines" checksum used to verify hand computations: a sum or product is congruent
mod 9 to the corresponding operation on the digit sums.

### Why This Matters

- Foundational divisibility rule ("a number is divisible by 9 iff its digit sum
  is") and the intuition behind digital roots.
- A clean, self-contained entry in the number-theory / positional-notation
  corner of the gallery, which currently has no digit-representation congruence
  result.
- Generalizes cleanly: the same argument gives the mod-3 rule, and the
  base/`b' % b = 1` framing yields the alternating-sum rule mod 11.

## Known Results

### What's Already Proven

- `Nat.modEq_digits_sum (b b' : ℕ) (h : b' % b = 1) (n : ℕ) : n ≡ (Nat.digits b' n).sum [MOD b]`
  — the general Mathlib lemma; specialize `b = 9`, `b' = 10`, `h : 10 % 9 = 1`.
- `Nat.modEq_nine_digits_sum` / `Nat.modEq_three_digits_sum` — Mathlib's
  pre-specialized corollaries for 9 and 3.
- `Nat.modEq_eleven_digits_sum` — alternating-sum variant mod 11.

### What's Still Open

- Nothing mathematically open; the goal is a clean formalized gallery entry that
  states the theorem, derives the divisibility corollary, and packages the mod-3
  and mod-11 companions.

### Our Goal

Produce a verified, sorry-free, axiom-free Lean file proving the mod-9 congruence
plus the `9 ∣ n ↔ 9 ∣ digitSum n` corollary, with the mod-3 and mod-11 variants
as bonus lemmas.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| divisibility-rules | Digit-based divisibility tests | `Nat.digits`, `Nat.ModEq` |
| infinitude-of-primes | Elementary number theory neighbor | modular arithmetic |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib specialization**: apply `Nat.modEq_digits_sum 9 10 (by norm_num)`.
   - Why it might work: the exact lemma exists; the proof is one line.
   - Risk: essentially none; main effort is packaging corollaries cleanly.

2. **From-scratch induction on `Nat.digits`**: `Nat.digits_add_two_add_one` recursion,
   using `10 ≡ 1 [MOD 9]` so each positional weight collapses to 1.
   - Why it might work: illustrative, avoids depending on the packaged lemma.
   - Risk: more bookkeeping over the digit recursion; unnecessary if the direct
     route is accepted.

### Key Difficulties

- None substantial. Care is only needed in the base case `n = 0`
  (`Nat.digits 10 0 = []`, empty sum) and lining up `Nat.ModEq` orientation.

### What Would a Proof Need?

- `Nat.modEq_digits_sum` (or a hand induction using `10 % 9 = 1`).
- `Nat.modEq_iff_dvd'` to extract the divisibility corollary.

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- The core statement is a direct specialization of an existing Mathlib lemma.
- Companion rules (mod 3, mod 11) are equally direct specializations.
- Comparable "cite-and-package" entries are routinely verified.

**Estimated Effort**:
- Exploration: < 1 hour
- If tractable: a few hours to package corollaries and write annotations

## References

### Mathlib
- `Mathlib.Data.Nat.Digits` — `Nat.digits`, `Nat.modEq_digits_sum`,
  `Nat.modEq_nine_digits_sum`, `Nat.modEq_three_digits_sum`,
  `Nat.modEq_eleven_digits_sum`.

## Metadata

```yaml
tags:
  - number-theory
  - digit-representations
  - modular-arithmetic
related_proofs:
  - divisibility-rules
difficulty: low
source: gallery-gap
created: 2026-07-05T00:06:20-07:00
```

**Significance**: 4/10
**Tractability**: 8/10
