# Problem: Wilson's Primality Criterion over ℕ and the Composite Factorial Congruence

**Slug**: wilsons-theorem-oq-08
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: wilsons-theorem

## Problem Statement

### Formal Statement

$$
\text{For } n \ge 2:\quad n \text{ is prime} \iff n \mid (n-1)! + 1,
\qquad\text{and}\qquad
n > 4 \text{ composite} \implies n \mid (n-1)!.
$$

### Plain Language

The parent entry `wilsons-theorem` proves Wilson's congruence in the ring `ZMod n`:
`((n-1)! : ZMod n) = -1` exactly when `n` is prime. This child pulls that statement back
to a **decision criterion stated entirely over ℕ** — `n` is prime iff `n` divides
`(n-1)! + 1` — and proves the complementary **composite** fact that Mathlib does *not*
package: for every composite `n > 4`, `n` already divides `(n-1)!` (so `(n-1)! ≡ 0`, not
`-1`). Together these give a clean, self-contained primality test and a sharp contrast
between the prime case (`≡ -1`) and the composite case (`≡ 0`).

### Why This Matters

Mathlib's `Nat.prime_iff_fac_equiv_neg_one` lives in `ZMod n` and says nothing about the
composite residue. The elementary composite statement `n ∣ (n-1)!` for composite `n > 4` is
a classic exercise (the only exception is `n = 4`, where `3! = 6 ≡ 2`), yet there is **no
named Mathlib lemma** for it, and no ℕ-level `n ∣ (n-1)! + 1 ↔ n.Prime` criterion. This
child fills both gaps with short reductions.

## Known Results

### What's Already Proven

- Parent `wilsons-theorem` is verified (0-axiom).
- Mathlib: `Nat.prime_iff_fac_equiv_neg_one (h : n ≠ 1) : Prime n ↔ ((n-1)! : ZMod n) = -1`
  and `ZMod.wilsons_lemma [Fact p.Prime] : ((p-1)! : ZMod p) = -1`, plus
  `Nat.prime_of_fac_equiv_neg_one`.

### What's Still Open

- The target theorems below (currently `sorry`). Mathlib has **no** composite factorial
  congruence lemma and **no** ℕ-level `n ∣ (n-1)!+1` primality criterion.

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**characterization / completion**.

## Target Lean Sketch

```lean
open Nat

/-- ℕ-level Wilson primality criterion: `n` is prime iff `n ∣ (n-1)! + 1`. -/
theorem prime_iff_dvd_factorial_succ {n : ℕ} (hn : 2 ≤ n) :
    n.Prime ↔ n ∣ (n - 1)! + 1 := by
  sorry
  -- Bridge to ZMod n: `(↑((n-1)! + 1) : ZMod n) = 0 ↔ n ∣ (n-1)!+1`
  -- (ZMod.natCast_zmod_eq_zero_iff_dvd), and `(↑((n-1)!+1)) = 0 ↔ ((n-1)! : ZMod n) = -1`
  -- (push_cast + `eq_neg_iff_add_eq_zero`), then `Nat.prime_iff_fac_equiv_neg_one`.

/-- The complementary composite congruence: a composite `n > 4` divides `(n-1)!`. -/
theorem composite_dvd_factorial {n : ℕ} (h4 : 4 < n) (hc : ¬ n.Prime) :
    n ∣ (n - 1)! := by
  sorry
  -- Write n = a * b with 1 < a ≤ b < n (n composite). If a ≠ b, both a and b are distinct
  -- factors ≤ n-1, so a*b ∣ (n-1)! via `Nat.dvd_factorial`-style product. If a = b (n = a²),
  -- then a and 2a are distinct and ≤ n-1 for a ≥ 3 (uses 4 < n), giving a² ∣ a*(2a) ∣ (n-1)!.
```

Add worked `example`s: `n = 5, 7, 11` prime (`n ∣ (n-1)!+1`); `n = 4` the lone exception
(`3! = 6`, `4 ∤ 6`, `4 ∤ 7`); `n = 6, 8, 9` composite with `n ∣ (n-1)!`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `wilsons-theorem` | Parent: Wilson's congruence in `ZMod n` | finite fields, `ZMod` |
| `wilsons-theorem-oq-04` | Sibling on Wilson variants | number theory |
| `infinitude-primes` | Uses factorial divisibility arguments | elementary number theory |

## Tractability Assessment

**Difficulty**: Low-Medium

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The forward criterion is a `ZMod`/cast reduction onto an existing iff. The
composite congruence is a short factor-pairing argument (`Nat.dvd_factorial`, case split on
whether `n` is a perfect square). No deep machinery.

### Suggested First Steps

1. Prove `prime_iff_dvd_factorial_succ` by rewriting `n ∣ (n-1)!+1` as
   `(↑((n-1)!+1) : ZMod n) = 0`, simplifying to `((n-1)! : ZMod n) = -1`, and applying
   `Nat.prime_iff_fac_equiv_neg_one`.
2. For `composite_dvd_factorial`, obtain a nontrivial factorization of `n`; split on
   `a = b` vs `a ≠ b`; use `Nat.dvd_factorial` for each distinct factor `≤ n-1`.
3. Add the `n = 4` exception and `decide`/`norm_num` worked examples.

## References

### Mathlib

- `Nat.prime_iff_fac_equiv_neg_one` — NumberTheory/Wilson.lean
- `ZMod.wilsons_lemma`, `Nat.prime_of_fac_equiv_neg_one` — NumberTheory/Wilson.lean
- `ZMod.natCast_zmod_eq_zero_iff_dvd` — Data/ZMod/Basic.lean
- `Nat.dvd_factorial` — Data/Nat/Factorial/Basic.lean

### Literature

- Wilson's theorem and its converse; the composite factorial congruence with the single
  exception `n = 4` is a standard elementary-number-theory result.

## Metadata

```yaml
tags:
  - number-theory
  - wilsons-theorem
  - primality
  - factorials
related_proofs:
  - wilsons-theorem
  - wilsons-theorem-oq-04
  - infinitude-primes
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
