# Problem: Complete Method of Types: Alternative Proof of Source Coding Theorem

**Slug**: shannon-source-coding-oq-04-incomplete-01
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-incomplete

## Problem Statement

### Formal Statement

`shannon-source-coding-oq-04` (`Proofs/ShannonSourceCodingOQ04.lean`) has 4 sorries:

1. **`type_class_size_eq_multinomial`** (line ~67): Prove `|T_f| = n! / ∏(f_i)!` via a bijection between the type class and multinomial arrangements.

2. **`type_class_size_le_entropy_pow`** (line ~172): Prove `|T_f| ≤ exp(n H(Q))` using the identity that every `x ∈ T_f` has `Q^n(x) = exp(-n H(Q))` and probabilities sum to 1.

3. **`dominant_type_lower_bound`** (line ~205): Prove the dominant type class has `≥ k^n / (n+1)^k` elements via `Finset.card_le_sum` pigeonhole.

4. **`source_coding_achievability_mot`** (line ~225): Formal achievability at rate H(p) using the dominant type bound and convergence.

### Plain Language

The method of types proof of Shannon's source coding theorem exists in the gallery with good infrastructure (entropy definitions proved, log-probability identity proved, type class partition proved) but 4 key lemmas remain as sorries. The goal is to close all 4 sorries using Mathlib's combinatorics and measure theory APIs.

### Why This Matters

- Completes an otherwise solid formalization of the Csiszár-Körner method of types (1981)
- Closes the gap between the probabilistic AEP proof and the combinatorial proof
- The type class size bound is foundational for channel coding exponents and large deviations (Sanov's theorem)

## Known Results

### What's Already Proven (0-sorry in the file)

- `empDist_sum`: empirical distribution sums to block length n
- `type_class_partition`: every sequence belongs to exactly one type class
- `count_types_le`: at most `(n+1)^k` distinct empirical distributions
- `total_sequences_eq`: `k^n` total sequences over `Fin k` alphabet
- `empEntropy_eq_shannonEntropy`: empirical entropy matches Shannon entropy of normalized type
- `log_typeProb_eq`: log-probability of any x ∈ T_f equals `-n * H(Q)` where Q = f/n

### What's Still Open (the 4 sorries)

- `type_class_size_eq_multinomial`: bijection proof (~60 lines) — explicit counting argument
- `type_class_size_le_entropy_pow`: sum-of-products identity via ENNReal/NNReal lifting
- `dominant_type_lower_bound`: pigeonhole on `Finset` with polynomial denominator
- `source_coding_achievability_mot`: convergence argument for rate achievability

### Our Goal

Close all 4 sorries in `Proofs/ShannonSourceCodingOQ04.lean`, producing a complete Lean 4 formalization of the method of types source coding proof.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| shannon-source-coding | Parent proof (AEP-based) | MeasureTheory, probabilistic arguments |
| shannon-source-coding-oq-04 | The incomplete proof we're completing | Method of types, combinatorics |
| shannon-source-coding-oq-02 | Huffman coding optimality | Optimal codes, entropy bounds |
| shannon-entropy | Core entropy formalism | Real.log, Finset.sum |

## Initial Thoughts

### Approach to Each Sorry

1. **`type_class_size_eq_multinomial`**:
   - Build an explicit bijection `Fin (n! / ∏ f_i!) ≃ typeClass f`
   - Or use `Fintype.card_perm` and `Fintype.card_subtype` to count permutations
   - Mathlib: `Nat.multinomial`, `Finset.card_pi`, `Equiv.Perm`

2. **`type_class_size_le_entropy_pow`**:
   - Key: `∑_{x ∈ T_f} Q^n(x) ≤ 1` (sub-probability bound)
   - Since each term equals `exp(-n H(Q))` (proved by `log_typeProb_eq`), we get `|T_f| * exp(-n H(Q)) ≤ 1`
   - Mathlib: `Finset.sum_le_one`, `NNReal.sum_le_one`, ENNReal lifting
   - This is likely the most direct sorry via `mul_le_one`

3. **`dominant_type_lower_bound`**:
   - Pigeonhole: total `k^n` sequences split among `≤ (n+1)^k` type classes
   - The largest class has `≥ k^n / (n+1)^k` elements
   - Mathlib: `Finset.exists_lt_card_fiber_of_nsmul_lt_card` or direct pigeonhole

4. **`source_coding_achievability_mot`**:
   - Formal rate: encode dominant type class in `⌈log |dominant_class|⌉` bits
   - From sorry 3: this is `≤ n H(p) + k log(n+1)` bits, achieving rate H(p) as n → ∞
   - May need a `Filter.Tendsto` argument or just an explicit bound

### Key Difficulties

- ENNReal vs NNReal vs Real arithmetic for the probability sum
- The multinomial bijection requires careful counting infrastructure
- `source_coding_achievability_mot` may be the hardest if it needs formal limit arguments

### What Would a Proof Need?

- `Finset.sum_congr` to leverage the equal-probability property
- `div_le_iff` and `Nat.cast_le` for the pigeonhole argument
- `Real.rpow_le_rpow` for the exponential bounds

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Infrastructure is in place (the hard mathematical definitions are done)
- The 4 sorries have clear mathematical statements and known proof paths
- Sorries 2 and 3 (entropy bound + pigeonhole) are likely tractable
- Sorry 1 (multinomial bijection) and sorry 4 (achievability) are more involved but doable
- Good candidates for Aristotle after human-assisted setup

## References

### Mathlib
- `Mathlib.Data.Nat.Choose.Multinomial` — `Nat.multinomial`
- `Mathlib.Analysis.SpecialFunctions.Log.Basic` — `Real.log_pow`, `Real.log_prod`
- `Mathlib.Data.Fintype.Card` — `Fintype.card_pi`, `Finset.card_le_sum`
- `Mathlib.MeasureTheory.Probability.Basic` — probability sum constraints

### Literature
- Csiszár, I., Körner, J. (1981): "Information Theory: Coding Theorems for Discrete Memoryless Systems" — Chapter 2
- Cover, T.M., Thomas, J.A. (2006): "Elements of Information Theory" — Chapter 11

## Metadata

```yaml
tags:
  - information-theory
  - combinatorics
  - method-of-types
  - entropy
  - source-coding
  - completion
  - sorries
related_proofs:
  - shannon-source-coding
  - shannon-source-coding-oq-04
difficulty: medium
source: gallery-incomplete
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 6/10
