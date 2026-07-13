# Problem: Kummer's Digit-Sum Divisibility Criterion for Binomial Coefficients

**Slug**: kummer-theorem-oq-05
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: kummer-theorem

## Problem Statement

### Formal Statement

$$
(p-1)\cdot \nu_p\!\binom{n}{k} = S_p(k) + S_p(n-k) - S_p(n),\qquad
p \nmid \binom{n}{k} \iff S_p(k) + S_p(n-k) = S_p(n)
$$

where $S_p(\cdot)$ is the base-$p$ digit sum and $k \le n$.

### Plain Language

Complete the binomial (as opposed to factorial) side of the Legendre/Kummer digit-sum
theory. For a prime $p$ and $k \le n$, the $p$-adic valuation of $\binom{n}{k}$ is
$(S_p(k) + S_p(n-k) - S_p(n))/(p-1)$. Consequently $p \nmid \binom{n}{k}$ exactly when
the base-$p$ digits of $k$ and $n-k$ add with no digit loss (equivalently, no carries
occur when adding $k$ and $n-k$ in base $p$) — the criterion form of Kummer's theorem.

### Why This Matters

The parent Lean file states the identity $(p-1)\nu_p\binom{n}{k} = S_p(k)+S_p(n-k)-S_p(n)$
in prose but only proves the **factorial** Legendre case. This child completes the
binomial identity and derives the clean "no digit loss ⟺ not divisible" criterion —
a form no sibling covers (oq-01 does multinomial carry counts, oq-03 characterizes
divisibility mod $p^m$ via carry counts, the oq-04 branch specializes to the 2-adic
valuation of the central binomial / Catalan via popcount).

## Known Results

### What's Already Proven

- Parent entry `kummer-theorem` is verified (0-axiom) and supplies the base theory.
- Mathlib already contains the master identity `padicValNat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits`.

### What's Still Open

- The target theorems below (currently `sorry`).

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child of `kummer-theorem`.
Category: **completion**.

## Target Lean Sketch

```lean
open Nat

/-- Kummer's identity for the binomial `p`-adic valuation. -/
theorem kummer_choose_digit_sum {p n k : ℕ} [hp : Fact p.Prime] (h : k ≤ n) :
    (p - 1) * padicValNat p (Nat.choose n k)
      = (p.digits k).sum + (p.digits (n - k)).sum - (p.digits n).sum := by
  sorry -- wrapper of padicValNat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits

/-- Divisibility criterion: no digit loss ⟺ `p ∤ C(n,k)`. -/
theorem kummer_digit_sum_dvd_iff {p n k : ℕ} [hp : Fact p.Prime] (h : k ≤ n) :
    ¬ p ∣ Nat.choose n k ↔
      (p.digits k).sum + (p.digits (n - k)).sum = (p.digits n).sum := by
  sorry -- via dvd_iff_padicValNat_ne_zero + the identity + Nat.sub_eq_zero_iff_le
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `kummer-theorem` | Parent: Kummer's theorem (carries) | p-adic valuation, base-p digits |
| `kummer-theorem-oq-03` | Sibling: divisibility mod p^m via carry counts | carry counting |
| `kummer-theorem-oq-01` | Sibling: multinomial carry counts | multinomial coefficients |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 6/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The core identity is a direct Mathlib lemma; the criterion follows by
rewriting the valuation-nonzero condition and using `Nat.sub_eq_zero_iff_le` with the
digit-sum bound. Mostly assembly of named lemmas.

### Suggested First Steps

1. Prove `kummer_choose_digit_sum` as a thin wrapper of
   `padicValNat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits` (convert
   multiplicity/factorization to `padicValNat` as the parent does).
2. Prove `kummer_digit_sum_dvd_iff`: rewrite via `dvd_iff_padicValNat_ne_zero`
   (using `Nat.choose_ne_zero` from `k ≤ n`), reduce `(p-1)*v = 0 ↔ v = 0`
   (`p-1 > 0`), substitute the identity, and close with `Nat.sub_eq_zero_iff_le`
   plus `Nat.digit_sum_le`.
3. Add the explicit valuation corollary and `native_decide` worked examples
   (e.g. `C(10,4)`, `C(6,3)`) cross-checking digit sums against the parent's
   carry-count examples.

## References

### Mathlib

- `padicValNat.sub_one_mul_padicValNat_choose_eq_sub_sum_digits` — NumberTheory/Padics/PadicVal/Basic.lean (the master identity)
- `padicValNat.dvd_iff_padicValNat_ne_zero` — NumberTheory/Padics/PadicVal/Basic.lean
- `padicValNat_choose` — NumberTheory/Padics/PadicVal/Basic.lean (Kummer carry-count form)
- `Nat.digit_sum_le` — Data/Nat/Digits/Defs.lean
- `Nat.sub_one_mul_factorization_factorial` — Data/Nat/Choose/Factorization.lean (parent's proven factorial case, for cross-checking)
- `Nat.choose_pos`, `Nat.choose_ne_zero` — Data/Nat/Choose/Basic.lean

## Metadata

```yaml
tags:
  - number-theory
  - p-adic-valuation
  - binomial-coefficients
  - kummers-theorem
  - digit-sum
related_proofs:
  - kummer-theorem
  - kummer-theorem-oq-03
  - kummer-theorem-oq-01
difficulty: low
source: proof-suggestion
created: 2026-07-01
```
