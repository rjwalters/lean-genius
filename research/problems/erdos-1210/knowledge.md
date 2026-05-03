# Erdős #1210 - Knowledge Base

## Problem Statement

Let $A \subseteq [1,n)$ be a set of integers such that $(a,b)=1$ for all distinct $a,b \in A$ (pairwise coprime). Is it true that
$$\sum_{a \in A} \frac{1}{n-a} \leq \sum_{\substack{p < n \\ p \text{ prime}}} \frac{1}{n-p}$$
i.e., does the set of primes below $n$ maximize this weighted harmonic sum over all pairwise coprime subsets?

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 5/10
**Aristotle Suitable**: No

## Tags

- erdos
- number-theory
- coprime
- primes
- harmonic-sums
- extremal-combinatorics

## Related Problems

- Problem #337, #2000, #60, #460, #950, #1209, #1211, #2, #39, #1

## References

- Er80 (Erdős 1980)
- Er77c (Erdős 1977)

## Sessions

### Session 2026-05-03 (Session 1) — researcher-10 + researcher-11

**Mode**: FRESH
**Outcome**: axiomatized — 11 theorems proved, 1 axiom (main conjecture), 0 sorries

#### What Was Done
- Formalized the problem in `proofs/Proofs/Erdos1210Problem.lean` (178 lines)
- Definitions: `primesBelow`, `PairwiseCoprime`, `ValidSubset`
- Key lemmas: `primes_coprime`, `pairwiseCoprime_at_most_one_even`, `primesBelow_sum_pos`
- Main `erdos_1210` axiom + 4 consequence theorems
- Gallery entry: `meta.json`, `index.ts` (8 annotations)
- PR #15117 open

#### Key Findings
- Full statement: primes below n maximize ∑ 1/(n-a) over pairwise coprime A ⊆ {1,...,n-1}
- Structural constraint: pairwise coprime sets have ≤1 even element
- The conjecture is tight: A = {primes < n} achieves equality
- No elementary proof known; likely needs Mertens-type analytic estimates

#### Next Steps
- Verify Lean file builds (Docker)
- Investigate exchange argument: swapping non-prime for nearby prime
- Explore computational verification for small n ≤ 20
- Asymptotic: ∑_{p<n} 1/(n-p) ~ ? as n → ∞

---

*Generated from erdosproblems.com on 2026-04-16*
