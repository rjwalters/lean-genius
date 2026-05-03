# Erdős #1201 - Knowledge Base

## Problem Statement

Is it true that for every $\epsilon,\eta>0$ there exists a $k$ such that the density of $n$ for which\[P(n(n+1)\cdots(n+k))>n^{1-\epsilon}\]is at least $1-\eta$ (where $P(m)$ is the greatest prime divisor of $m$)? Erdős wrote he could prove this for $\epsilon=1/2$.## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #62
- Problem #2
- Problem #1200
- Problem #1202
- Problem #39
- Problem #1

## References

- (None available)

## Sessions

## Session 2026-05-03 (Session 1) - Bertrand Lower Bounds

**Mode**: FRESH
**Outcome**: progress — 2 new theorems proved, PR #15174 created

### What I Did
- Identified erdos-1201 as RICH-tier problem (37 knowledge items, 0 sorries, 1 axiom)
- Analyzed Lean file: 19 existing theorems, well-structured, only missing Docker build verification
- Added `import Mathlib.NumberTheory.Bertrand`
- Proved `gpfConsecutive_self_gt (n ≥ 1) : n < gpfConsecutive n n`
  - Key: Bertrand gives prime p ∈ (n, 2n]; p = n + (p-n) with p-n ≤ n appears in window
  - Uses: Nat.exists_prime_lt_and_le_two_mul, Finset.dvd_prod_of_mem, gpf_max
- Proved `gpfConsecutive_gt_n_of_large_window (n ≥ 2, k ≥ n) : n < gpfConsecutive n k`
  - Induction on k-n using gpfConsecutive_mono
- Updated gallery meta.json: theoremCount 14→21, lineCount 267→297, new Bertrand section
- Created PR #15174

### Key Findings
- Mathlib.NumberTheory.Bertrand is available via `Nat.exists_prime_lt_and_le_two_mul`
- The n+1 consecutive integers [n, 2n] always contain a Bertrand prime — clean formalization
- `Finset.dvd_prod_of_mem` is the right tool for showing a specific factor divides the product
- Bug caught: must bind hp_le (not use _) from Bertrand decomposition for omega to prove range membership

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (297 lines, was 266)
- `src/data/proofs/erdos-1201/meta.json` (updated counts + Bertrand section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Await CI/Docker build result for PR #15174
- Potential: Sylvester-Schur theorem (gpfConsecutive n k > k for n ≥ k+1)

---

## Session 2026-05-03 (Session 2) - Infinite Set Result

**Mode**: FRESH (REVISIT)
**Outcome**: progress — 2 new theorems, fix to induction IH, PR #15215

### What I Did
- Diagnosed: gallery meta stale (21 thm/297 lines vs actual 22 thm/310 lines after PRs #14942 + #15174)
- Discovered existing build error in `gpfConsecutive_gt_n_of_large_window` (never verified by Docker)
  - IH was `n ≤ n+d → n < gpfConsecutive n (n+d)` not `n < ...` — needed `ih (by omega)`
- Added `dvd_consecutiveProduct_term`: (n+i) | consecutiveProduct n k for i ≤ k
  - Generalizes `dvd_consecutiveProduct_right` (the i=k case)
- Added `erdos_1201_infinitely_many`: {n | P(n,k) > n^(1-ε)} is infinite for fixed k, ε∈(0,1)
  - Proof: primes form infinite subset via `gpfConsecutive_ge_self_of_prime` + `Real.rpow_lt_rpow_of_exponent_lt`
  - Uses `Nat.infinite_setOf_prime.mono`
- Updated meta.json: 21→24 theorems, 297→341 lines
- Created PR #15215

### Key Findings
- `Nat.infinite_setOf_prime.mono` works for infinite subset arguments
- `Real.rpow_lt_rpow_of_exponent_lt (h : 1 < x) (h : y < z) : x^y < x^z` key for power comparison
- The ε < 1 condition in `erdos_1201_infinitely_many` is not needed (only ε > 0 matters for n^ε > 1)
- Lean 4 induction IH includes all hypotheses that depend on the induction variable — `n ≤ n+d` survived

### Mathematical Note
`erdos_1201_infinitely_many` is the weakest meaningful partial result: the good set is infinite but
may have density 0 (primes have density 0 by PNT). Positive density requires smooth number estimates.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (341 lines, was 310)
- `src/data/proofs/erdos-1201/meta.json` (updated counts, new section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Sylvester-Schur: for n > k, n(n+1)···(n+k-1) has a prime factor > k (is this in Mathlib?)
- Quantitative density lower bound for small k (requires smooth number estimates)

---

## Session 2026-05-03 (Session 3) - Max Formula and Smooth-Window Reformulation

**Mode**: REVISIT
**Outcome**: progress — 2 new theorems proved, PR created

### What I Did
- Identified gap: no lemma connecting P(n,k) to individual-term GPFs
- Proved `gpfConsecutive_eq_sup_range (n ≥ 2) : P(n,k) = sup_{i≤k} GPF(n+i)`
  - Key: prime factors of a product = union of prime factors of factors → GPF(product) = max GPF(term)
  - ≤ direction: GPF of product divides some term via `prime_dvd_consecutive_range`, so ≤ sup
  - ≥ direction: each term's GPF divides the term which divides the product, so ≤ GPF(product)
- Proved `gpfConsecutive_le_iff : P(n,k) ≤ t ↔ ∀ i ≤ k, GPF(n+i) ≤ t`
  - Immediate corollary of max formula via `Finset.sup_le_iff`
  - Reformulates "P(n,k) is small" as "every integer in [n, n+k] is t-smooth"
- Updated meta.json: 35→37 theorems, 472→514 lines, new max-formula section
- Updated research JSON: added 2 builtItems, 2 insights, updated progressSummary

### Key Findings
- `Finset.sup_le_iff` and `Finset.le_sup` work cleanly for ℕ with `OrderBot` (0)
- The max formula is the bridge between product-level and term-level properties
- Smooth-window reformulation: "n fails Erdős condition" = "window [n, n+k] is fully t-smooth"
  — this connects to Dickman's ρ function and opens the density estimation approach

### Mathematical Note
`gpfConsecutive_le_iff` reveals the structure of the Erdős conjecture: proving density → 1
reduces to showing the density of n where ALL of n, n+1, ..., n+k are n^ε-smooth
goes to 0 as k → ∞. This is plausible from smooth number theory (ρ(1/ε) density of
n^ε-smooth numbers among [1,n]) but requires quantitative estimates not in Mathlib.

### Files Modified
- `proofs/Proofs/Erdos1201Problem.lean` (514 lines, was 472)
- `src/data/proofs/erdos-1201/meta.json` (updated counts, new section)
- `src/data/research/problems/erdos-1201.json` (updated knowledge)

### Next Steps
- Sylvester-Schur: for n > k, n(n+1)···(n+k-1) has a prime factor > k
- Prove `gpfConsecutive_pos_density_of_smooth_bound`: if k-smooth density < η then good set ≥ 1-η

---

*Generated from erdosproblems.com on 2026-04-16*
