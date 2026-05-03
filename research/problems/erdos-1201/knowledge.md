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

*Generated from erdosproblems.com on 2026-04-16*
