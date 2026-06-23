# Erdős #1210 - Knowledge Base

## Problem Statement

Let $A \subseteq [1,n)$ be a set of integers such that $(a,b)=1$ for all distinct $a,b \in A$ (pairwise coprime). Is it true that
$$\sum_{a \in A} \frac{1}{n-a} \leq \sum_{\substack{p < n \\ p \text{ prime}}} \frac{1}{p} + O(1)?$$
i.e., is the proximity-weighted harmonic sum over any pairwise coprime set bounded by the Mertens sum $\sum_{p<n} 1/p \sim \log\log n$ up to an absolute additive constant?

> **Correction note (S3, verified against the source 2026-06-13).** The RHS is
> $\sum_{p<n} 1/p$ (prime reciprocals), **not** $\sum_{p<n} 1/(n-p)$, and there is
> an essential $+O(1)$ term. Earlier sessions transcribed both incorrectly,
> which is why S2 found a (spurious) "counterexample". In [Er80] Erdős notes he
> "did not state [this] quite correctly" in [Er77c]; the [Er80] reformulation
> concerns primes $q_i$ in an interval $(n,m]$:
> $\sum 1/(q_i - n) < \sum_{p<m-n} 1/p + O(1)$.

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

### Session 2026-06-13 (Session 3) — researcher-2

**Mode**: ITERATION (resolving S2's source-access blocker)
**Outcome**: STATEMENT CORRECTED — re-axiomatized with the true Erdős statement; Docker-verified.

#### What Was Done
- Recovered the verbatim problem statement from erdosproblems.com/1210 using
  `curl` (WebFetch returned HTTP 403). The true statement is
  $\sum_{a\in A} 1/(n-a) \le \sum_{p<n} 1/p + O(1)$ — RHS uses prime reciprocals
  $1/p$ (NOT $1/(n-p)$) and carries an essential additive $O(1)$ term.
- Diagnosed S2's "unsoundness" as a double transcription error (wrong RHS +
  dropped $O(1)$), not a flaw in the conjecture. The n=5, A={4} discrepancy of
  1/6 is absorbed by the constant.
- Rewrote `proofs/Proofs/Erdos1210Problem.lean`:
  - Added `primeReciprocalSum n := ∑_{p<n} 1/p` (corrected RHS).
  - Replaced the unsound exact axiom with the honest existential-constant form:
    `∃ C, ∀ n≥3, ∀ pairwise-coprime A ⊆ [1,n), ∑ 1/(n-a) ≤ primeReciprocalSum n + C`.
  - Kept all verified structural lemmas; added `primeReciprocalSum_nonneg/pos`.
  - Reframed the n=5 facts as `naive_statement_fails_at_five` (C=0 is false) and
    `corrected_statement_consistent_at_five` (any C ≥ 1/6 works) — a
    machine-checked proof that the $O(1)$ term is essential.
- Docker build succeeded (3058 jobs). Updated gallery `meta.json` to the
  corrected statement; final tally: 14 theorems, 4 defs, 1 axiom, 230 lines.

#### Key Findings
- The conjecture is a Mertens-type ($\log\log n$) upper bound, uniform over all
  pairwise coprime sets, for the proximity-weighted sum — not an "primes are
  extremal" exact equality as previously framed.
- Erdős's [Er80] interval reformulation (primes in $(n,m]$) is the form he
  considered correctly stated; relates to #460, #950.

#### Next Steps (S4)
- Attempt an unconditional partial bound $\sum_{a\in A} 1/(n-a) \le f(n)$ for
  pairwise coprime A (e.g. via the ≤1-even-element structure + a sieve/Mertens
  estimate), which would be genuine progress toward the open problem.

### Session 2026-06-13 (Session 4) — researcher-1

**Mode**: ITERATION (SURVEY only — Docker unreliable [`docker ps` hangs], Aristotle backend 404; no verification route, so no Lean changes shipped this session).
**Outcome**: Tractability-boundary survey for the S4 partial-bound goal, plus a canonical-JSON state correction (the research JSON `progressSummary`/`nextSteps` still described the Session-1 mis-transcribed `1/(n-p)` form; brought into line with S3's corrected statement).

#### The achievable-bounds landscape (what S4 should and should not target)

The conjecture's target is a **`log log n`** (Mertens-order) bound, uniform in
`n` and `A`. Two very different difficulty regimes:

1. **Trivial `log n` baseline (no coprimality needed, elementary, provable).**
   For *any* `A ⊆ [1,n)` with distinct elements, the values `{n − a : a ∈ A}`
   are distinct integers in `[1, n−1]`, so
   `∑_{a∈A} 1/(n−a) = ∑_{m ∈ {n−a : a∈A}} 1/m ≤ ∑_{m=1}^{n−1} 1/m = H_{n−1} ~ log n`.
   This uses none of the pairwise-coprimality hypothesis. In Lean it is a
   "sum over an injective image ≤ sum over the full range" argument
   (`Finset.sum_le_sum_of_subset_of_nonneg` after mapping `a ↦ n − a`, with
   injectivity of `a ↦ n − a` on `A ⊆ [1,n)`). **This is the right next ACT
   deliverable** — a genuine *unconditional* `theorem` bounding the LHS by the
   harmonic number, instantiating the conjecture's `C`-free shape with `f(n) =
   H_{n−1}`. It is honest partial progress (a verified upper bound), but it is
   **NOT** the conjecture: `log n ≫ log log n`.

2. **The conjecture's `log log n` is the hard part — and it is the
   coprimality that must close the `log n → log log n` gap.** Getting from the
   trivial harmonic bound down to Mertens order is exactly where the
   pairwise-coprime structure (≤ 1 element divisible by each prime `p`) does the
   work, via a sieve/Mertens comparison. **Blocked by a Mathlib gap**: base
   Mathlib `v4.26.0` does **not** contain Mertens' second theorem
   (`∑_{p<n} 1/p = log log n + O(1)`) — see this repo's own assessment in
   `research/problems/bertrands-postulate-oq-01/state.md` ("Mertens' theorems …
   not present in base Mathlib v4.26.0"). So even *stating* the RHS asymptotic,
   let alone proving the comparison, requires analytic number theory that would
   be a substantial upstream contribution. The full conjecture should be treated
   as **long-horizon / BLOCKED-on-infra**, not a near-term ACT.

#### Recommendation
- **S5 ACT (when build infra is reliable)**: ship the trivial `H_{n−1}`
  unconditional bound from regime (1). Small, fully elementary, no new axioms,
  Mathlib-reachable. Do **not** attempt the `log log n` conjecture directly.
- Do not blind-ship the regime-(1) proof while Docker is down — the
  injective-image reindex is exactly the kind of step that fails silently
  without a compiler.

---

*Generated from erdosproblems.com on 2026-04-16; statement corrected from source 2026-06-13.*
