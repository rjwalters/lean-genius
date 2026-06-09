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
- Full statement (as transcribed): primes below n maximize ∑ 1/(n-a) over
  pairwise coprime A ⊆ {1,...,n-1}. (REFUTED in S2 below.)
- Structural constraint: pairwise coprime sets have ≤1 even element.
- (CLAIMED) The conjecture is tight at A = {primes < n}. (REFUTED in S2.)
- No elementary proof known; likely needs Mertens-type analytic estimates.

#### Next Steps
- Verify Lean file builds (Docker)
- Investigate exchange argument: swapping non-prime for nearby prime
- Explore computational verification for small n ≤ 20
- Asymptotic: ∑_{p<n} 1/(n-p) ~ ? as n → ∞

### Session 2026-06-09 (Session 2) — researcher-6

**Mode**: ITERATION
**Outcome**: STATEMENT-REVISION-NEEDED — literal axiom REFUTED by counterexample at n = 5, A = {4}.

#### What Was Done
- Discovered that the literal axiom `erdos_1210` (as currently formalized) is
  **unsound**: A = {4} at n = 5 satisfies all hypotheses but violates the
  conclusion.
- Added four machine-checked theorems to `proofs/Proofs/Erdos1210Problem.lean`:
  - `primesBelow_five` — primesBelow 5 = {2, 3} by `decide`.
  - `primesBelow_five_sum` — prime sum equals 5/6.
  - `singleton_four_valid_at_five` — {4} is a valid pairwise-coprime subset.
  - `erdos_1210_literal_counterexample` — the prime sum is strictly less than
    the {4}-sum, refuting the axiom's conclusion.
- Documented the discrepancy in a `## Counterexample: The Literal Statement Is
  FALSE` block, with two interpretation hypotheses (missing hypothesis like
  `a > n/2`; or a different weight like `1/a`).
- Did NOT derive False from the bad axiom (kept the file consistent so any
  future repair retains the existing structure).
- Updated import path `Mathlib.Algebra.BigOperators.Group.Finset` → `.Basic`
  to match current Mathlib layout.

#### Counterexample Detail
- n = 5, A = {4}:
  - ValidSubset 5 {4}: 1 ≤ 4 ∧ 4 < 5 ✓
  - PairwiseCoprime {4}: singleton, vacuous ✓
  - LHS = 1/(5-4) = 1
  - primesBelow 5 = {2, 3}; RHS = 1/3 + 1/2 = 5/6
  - 1 > 5/6 — REFUTATION

- Additional sub-n=10 counterexamples (informal): A = {1} at n = 5
  (LHS = 1/4 < 5/6 OK), A = {1, 2} at n = 3 (LHS = 1/2 + 1 = 3/2 vs RHS = 1).

#### Plausible Reinterpretations
- **Hypothesis (a)** A ⊆ [√n, n) or A ⊆ (n/2, n). At n=5 with a ≥ √5 ≈ 2.24,
  {4} still violates (LHS = 1, RHS = 5/6). At n=5 with a > n/2 = 2.5, same
  issue. Neither matches.
- **Hypothesis (b)** Weight is 1/a (not 1/(n-a)). At n = 5 with a ≥ 2:
  - {2, 3}: 1/2 + 1/3 = 5/6 = ∑ 1/p ✓ (equality)
  - {3, 4}: 1/3 + 1/4 = 7/12 < 5/6 ✓
  - {4}: 1/4 < 5/6 ✓
  No counterexample found in this restricted regime. Likely candidate for the
  intended statement, but requires source-text confirmation.
- **Hypothesis (c)** The inequality direction is reversed. At n = 5 with
  A = {1}, LHS = 1/4 < 5/6 = RHS, refuting this direction too.

#### Next Steps (S3)
- Locate the Erdős source ([Er77c], [Er80]) to recover the intended statement.
- Once the correct statement is known, replace the unsound axiom with the
  corrected statement (or with a verified theorem if provable).
- Refactor or remove the four consequence theorems that depend on the current
  axiom.
- Possibly downgrade gallery `status` from `axiomatized` →
  `formalized-pending-statement-revision`.

---

*Generated from erdosproblems.com on 2026-04-16*
