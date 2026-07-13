# Erdős #472 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

Given some initial finite sequence of primes $q_1<\cdots<q_m$ extend it so that $q_{n+1}$ is the smallest prime of the form $q_n+q_i-1$ for $n\geq m$. Is there an initial starting sequence so that the resulting sequence is infinite?



A problem due to Ulam. For example if we begin with $3,5$ then the sequence continues $3,5,7,11,13,17,\ldots$. It is possible that this sequence is infinite.


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #1998
- Problem #471
- Problem #473
- Problem #2
- Problem #39
- Problem #1

## References

- ErGr80

## Sessions

## Session 2026-05-03 (Session 1) — Twin/Cousin Prime Stepping Structure

**Mode**: FRESH
**Outcome**: progress — 7 new theorems, 23→30 total

### What I Did
- Read full Lean file (263 lines, 23 theorems, 1 axiom, 0 sorries)
- Identified gap: seed elements 3 and 5 always appear in candidate lists — structural observation not yet formalized
- Proved `ulam35_f0_eq_three` (f(0) = 3) and `ulam35_f1_eq_five` (f(1) = 5)
- Proved `ulam35_gap_ge_two`: consecutive terms always differ by ≥ 2 (specializes existing gap theorem, eliminates f(n)=2 case)
- Proved `ulam35_three_in_ofFn` and `ulam35_five_in_ofFn`: seed elements appear in candidate lists
- Proved `ulam35_twin_prime_step`: **f(n)+2 prime → f(n+1) = f(n)+2** (main result)
- Proved `ulam35_cousin_prime_upper`: f(n)+4 prime → f(n+1) ≤ f(n)+4

### Key Findings
- Twin prime step is tight: minimality gives ≤, gap bound gives ≥, so equality when f(n)+2 is prime
- Both 3 and 5 are always available as "donors" in the extension rule — unique to the {3,5} seed
- The pattern 3,5,7,11,13,17,19,23 matches all odd primes through 23; twin prime pairs explain advances by 2

### Files Modified
- `proofs/Proofs/Erdos472Problem.lean` (327 lines, was 263)
- `src/data/proofs/erdos-472/meta.json` (theoremCount 23→30, lineCount, new section)
- `src/data/research/problems/erdos-472.json` (knowledge updated)

### Next Steps
- Prove complement: f(n)+2 NOT prime → f(n+1) ≥ f(n)+4
- Formalize cousin prime exact step when both conditions hold
- Upper bound from full sequence: f(n+1) ≤ 2f(n)-1 when 2f(n)-1 is prime

---

*Generated from erdosproblems.com on 2026-01-13*
