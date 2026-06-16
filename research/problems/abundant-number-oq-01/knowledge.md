# Abundant Numbers: Closure Under Multiplication (abundant-number-oq-01)

## Problem Summary

A natural number `n` is **abundant** if the sum of its proper divisors exceeds `n`
(equivalently `σ₁(n) > 2n`, where `σ₁(n) = ∑_{d ∣ n} d`). Mathlib
(`Mathlib.NumberTheory.FactorisationProperties`) defines `Nat.Abundant`, proves
`abundant_twelve` and `weird_seventy`, and establishes that there are infinitely many
**deficient** numbers — but it does **not** record how abundance interacts with
multiplication, nor that the abundant numbers are themselves infinite.

**Results proved** (file `proofs/Proofs/AbundantNumberOQ01.lean`, 0 sorries, 0 axioms):

1. `Nat.Abundant.mul_left` — every positive multiple of an abundant number is abundant.
2. `Nat.Perfect.mul_left_abundant` — every *proper* multiple (`2 ≤ k`) of a perfect number
   is abundant.
3. `Nat.infinite_abundant` — there are infinitely many abundant numbers.
4. `Nat.infinite_even_abundant` — there are infinitely many even abundant numbers.

**Status**: COMPLETE — fully elementary, no enumeration, 0 axioms, 0 sorries
(build-pending confirmation under Docker contention).

## Approach

The whole development rests on one monotonicity bound on the divisor sum, obtained by a
divisor injection — there is no need to compute any σ values beyond the seed
`Abundant 12` already in Mathlib.

### Engine: `mul_sumDivisors_le` (`0 < k ⟹ k·σ₁(n) ≤ σ₁(k·n)`)

The map `d ↦ k·d` sends each divisor `d ∣ n` to a divisor `k·d ∣ k·n`
(`mul_dvd_mul_left`), is injective for `k ≠ 0` (`Nat.eq_of_mul_eq_mul_left`), and so
`{k·d : d ∣ n}` is a subset of `(k·n).divisors`. Summing:
`k·σ₁(n) = ∑_{d∣n} k·d = ∑_{x ∈ image} x ≤ σ₁(k·n)` (`Finset.sum_image` +
`Finset.sum_le_sum_of_subset`, the latter valid in ℕ since all terms are nonnegative).

### Sharpened engine: `mul_sumDivisors_lt` (`2 ≤ k ⟹ k·σ₁(n) < σ₁(k·n)`)

For the perfect-number case the `≤` must be strict. The divisor `1` of `k·n` is **never**
of the form `k·d` when `1 < k` (that would force `k ∣ 1`), so inserting `1` into the image
set gives a strictly larger subset sum: `k·σ₁(n) < 1 + k·σ₁(n) ≤ σ₁(k·n)`.

### From the engine to the theorems

- **Abundant ⟹ multiples abundant**: `σ₁(n) > 2n` gives
  `σ₁(k·n) ≥ k·σ₁(n) > k·2n = 2(k·n)`, i.e. `k·n` abundant (`mul_lt_mul_of_pos_left`).
- **Perfect ⟹ proper multiples abundant**: `σ₁(n) = 2n`
  (`Nat.perfect_iff_sum_divisors_eq_two_mul`), so the *strict* bound gives
  `σ₁(k·n) > k·σ₁(n) = 2(k·n)`.
- **Infinitude**: `k ↦ (k+1)·12` is injective and each value is `12·(k+1)`, abundant by
  applying `Abundant.mul_left` to `abundant_twelve`; `Set.infinite_of_injective_forall_mem`.
  The even version notes `(k+1)·12 = 2·((k+1)·6)`.

### Definition bridge

`abundant_iff_two_mul_lt_sumDivisors`: `Abundant n ↔ 2n < σ₁(n)`. Mathlib defines abundance
with proper divisors; `Nat.sum_divisors_eq_sum_properDivisors_add_self` plus `omega` moves
between the proper-divisor and full-divisor forms.

## Why this is not enumeration

Each theorem quantifies over infinitely many `n` (or `k`). The proof is a single structural
injection argument, uniform in the parameters — `decide`/`native_decide` are not used and
could not establish any of these statements.

## Mathlib gaps filled

- No `Nat.Abundant.mul_left` (multiplicative closure of abundance).
- No `Nat.Perfect.mul_left_abundant` (perfect ⟹ proper multiples abundant).
- No `Nat.infinite_abundant` (Mathlib has `infinite_deficient` but not the abundant analogue).

## Next Steps / Open Questions

- gcd/lcm-style sharpening, or the density statement (abundant numbers have natural density
  ≈ 0.2476…) — the latter is a genuine analytic result, out of scope here.
- Smallest **odd** abundant number is 945; an `infinite_odd_abundant` analogue would need an
  odd abundant seed (e.g. 945 = 27·35) plus the same `mul_left` closure restricted to odd `k`.

## Sessions

### 2026-06-16 (Session 1) — FRESH, Outcome: progress (build-pending)

- Selected from the available pool (EMPTY knowledge tier); chose abundance closure over
  enumeration-style targets because it admits a uniform structural proof.
- Confirmed Mathlib has `Nat.Abundant` but lacks all four target results.
- Wrote `proofs/Proofs/AbundantNumberOQ01.lean` (orphan, unregistered) with the divisor-
  injection engine and the four theorems; 0 sorries, 0 axioms.
- Verified every supporting lemma name against the offline Mathlib v4.26 checkout.
- Build queued under heavy Docker contention; gallery data staged in `gallery-draft/` to
  avoid a false-green gallery entry before the build confirms.
