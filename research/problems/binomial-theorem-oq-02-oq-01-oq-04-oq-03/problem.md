# Problem: All Factorial Moments of Binomial Marginals via Iterated Fiber Grouping

**Slug**: `binomial-theorem-oq-02-oq-01-oq-04-oq-03`
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap (open-question child of `binomial-theorem-oq-02-oq-01-oq-04`)

## Problem Statement

The parent proof `BinomialTheoremOQ02OQ01OQ04` computes the **second** moment /
variance of a multinomial marginal `Xᵢ ~ Binomial(n, pᵢ)` by *fiber grouping*
over the value `j = k(i₀)`, reducing to the binomial second factorial moment
`E[X(X−1)] = n(n−1)p²` already proved in `BinomialTheoremOQ03`. This child asks
to lift that reduction to **arbitrary order `r`**, recovering *all* factorial
moments — and hence all ordinary moments — of a binomial marginal uniformly.

### Formal Statement

Let `X ~ Binomial(n, p)`, represented (as in the parent chain) by the mass
function

```
binomPMF n p k = (Nat.choose n k : ℝ) * p ^ k * (1 - p) ^ (n - k).
```

Write the **falling factorial** (Pochhammer descending) as
`n^{(r)} = n·(n−1)⋯(n−r+1) = Nat.descFactorial n r`, with the convention
`n^{(0)} = 1`. The `r`-th **factorial moment** of `X` is

```
  E[X^{(r)}]  =  E[ X (X−1) ⋯ (X−r+1) ]  =  ∑_{k=0}^{n} k^{(r)} · binomPMF n p k.
```

**Claim 1 (falling-factorial moment).** For all `n, r : ℕ` and `p : ℝ`,

```
  ∑_{k=0}^{n} (Nat.descFactorial k r : ℝ) · binomPMF n p k
        =  (Nat.descFactorial n r : ℝ) · p ^ r.
```

Equivalently `E[X^{(r)}] = n^{(r)} p^r`. Note this holds for **every** `r`,
including `r > n` where both sides vanish (`descFactorial n r = 0` when `r > n`).

**Claim 2 (ordinary moment via Stirling).** Using Stirling numbers of the
second kind `S(r, j) = Nat.stirlingSecond r j` and the connection identity
`xʳ = ∑_{j=0}^{r} S(r, j) · x^{(j)}`, the ordinary moments follow uniformly:

```
  E[Xʳ]  =  ∑_{k=0}^{n} (k : ℝ) ^ r · binomPMF n p k
         =  ∑_{j=0}^{r} (Nat.stirlingSecond r j : ℝ) · (Nat.descFactorial n j : ℝ) · p ^ j.
```

**Claim 3 (multinomial marginal, the fiber-grouping payoff).** For
`(X₁,…,X_d) ~ Multinomial(n, p₁,…,p_d)` with `∑ pᵢ = 1`, represented as in the
parent by `multinomialProb s p n k` summed over `k ∈ s.piAntidiag n`, each
marginal statistic obeys

```
  ∑_{k ∈ s.piAntidiag n} (Nat.descFactorial (k i₀) r : ℝ) · multinomialProb s p n k
        =  (Nat.descFactorial n r : ℝ) · (p i₀) ^ r,
```

for any `i₀ ∈ s`. This is Claim 1 pulled back through the marginal-PMF identity
`multinomial_marginal_pmf` (from `BinomialTheoremOQ02OQ01OQ02`), exactly the
`r`-fold generalization of the parent's `multinomial_second_moment`.

### Plain Language

A *moment* of a random count `X` measures its spread: `E[X]` is the average,
`E[X²]` the average square, and so on. Ordinary powers `Xʳ` are awkward to sum
against binomial weights because the algebra does not telescope cleanly. The
trick — classical in probability — is to use **factorial moments**
`E[X(X−1)⋯(X−r+1)]` instead. These *do* telescope, because of the **absorption
identity**

```
  (k+1)·C(n+1, k+1) = (n+1)·C(n, k),
```

which lets a factor of `k` be "absorbed" into the binomial coefficient while
shifting `n → n−1` and `k → k−1`. Applying it `r` times turns
`k^{(r)}·C(n, k)` into `n^{(r)}·C(n−r, k−r)`; after reindexing `k ↦ k−r` and
factoring out `n^{(r)} pʳ`, the leftover sum is a *complete* binomial sum that
equals `1`. So `E[X^{(r)}] = n^{(r)} pʳ` drops out with almost no computation.

"Fiber grouping" is the multinomial packaging of the same move: to evaluate a
statistic that depends only on the `i₀`-th coordinate `k(i₀)`, group the
multinomial outcomes into fibers `{k | k(i₀) = j}`; each fiber's total
probability is exactly the binomial marginal `P(Xᵢ = j)`, so the multinomial
computation collapses onto the binomial one.

Ordinary moments are then recovered mechanically: since
`xʳ = ∑_j S(r, j) x^{(j)}` (Stirling numbers of the second kind count the ways
to expand a power into falling factorials), we get
`E[Xʳ] = ∑_j S(r, j) n^{(j)} pʲ`. For example `E[X²] = n^{(2)}p² + n^{(1)}p =
n(n−1)p² + np`, reproducing the parent's variance `np(1−p)`.

### Why This Matters

- **Uniformity.** The parent handles only `r = 2` (variance), with a bespoke
  `double_absorption` lemma. This problem replaces the ad-hoc `r = 1, 2` lemmas
  by a *single* statement covering all `r`, from which mean, variance,
  skewness, kurtosis, and every higher moment follow.
- **The falling-factorial abstraction is the "right" one.** The existing
  `binomial_mean` and `binomial_second_factorial_moment` proofs in
  `BinomialTheoremOQ03` are essentially the `r = 1` and `r = 2` special cases of
  one clean induction. Formalizing the general `r` clarifies that the entire
  family is a single absorption argument, not a growing pile of special cases.
- **Reusable Mathlib-style lemma.** `∑_k k^{(r)} C(n,k) pᵏ (1−p)^{n−k} =
  n^{(r)} pʳ` is a genuinely reusable fact about binomial factorial moments that
  Mathlib currently lacks; it is the discrete analogue of the derivative rule
  for the probability generating function `G(t) = (pt + 1 − p)ⁿ`, whose `r`-th
  derivative at `t = 1` is `n^{(r)} pʳ`.
- **Completes the multinomial moment story.** Combined with the parent's
  covariance matrix `Σᵢⱼ = n pᵢ(δᵢⱼ − pⱼ)`, higher factorial moments open the
  door to mixed factorial moments `E[Xᵢ^{(r)} Xⱼ^{(s)}]` and the full moment
  structure of the multinomial.

### Known Results

- **Parent (`BinomialTheoremOQ02OQ01OQ04`).** `multinomial_second_moment`
  (`E[Xᵢ²] = ∑ⱼ j²·binomPMF n pᵢ j` by fiber grouping) and `multinomial_variance`
  (`Var(Xᵢ) = n pᵢ(1 − pᵢ)`). These are the `r = 2` instance of this problem.
- **`BinomialTheoremOQ03`** already contains the `r = 1, 2` factorial moments and
  the two absorption lemmas this problem generalizes:
  - `absorption (n k : ℕ) : (k+1)·C(n+1, k+1) = (n+1)·C(n, k)` — proved from the
    Mathlib lemma `Nat.add_one_mul_choose_eq n k :
    (n+1)·choose n k = choose (n+1) (k+1)·(k+1)`. (Note: `Nat.succ_mul_choose_eq`
    is the same fact but is **deprecated since 2025-12-09** — use
    `Nat.add_one_mul_choose_eq`.)
  - `double_absorption (n k) : (k+2)(k+1)·C(n+2, k+2) = (n+2)(n+1)·C(n, k)` —
    two applications of `absorption`; this is the `r = 2` falling-factorial
    absorption.
  - `binomial_mean : ∑ₖ k·binomPMF n p k = n·p` (r = 1).
  - `binomial_second_factorial_moment : ∑ₖ k(k−1)·binomPMF n p k = n(n−1)p²`
    (r = 2). This is literally `E[X^{(2)}] = n^{(2)} p²`.
  - `binomial_variance : E[X²] − (E[X])² = np(1−p)` (via
    `E[X²] = E[X(X−1)] + E[X]`), and `binomial_expansion` / `binomPMF_sum_eq_one`
    for the normalization `∑ₖ C(n,k) pᵏ(1−p)^{n−k} = 1`.
- **Mathlib primitives** (verified present in this checkout):
  - `Nat.descFactorial : ℕ → ℕ → ℕ`, with `Nat.descFactorial_zero`,
    `Nat.descFactorial_one`, and the recurrence
    `Nat.descFactorial_succ n k : n.descFactorial (k+1) = (n − k) · n.descFactorial k`.
  - `Nat.descFactorial_eq_factorial_mul_choose (n k) :
    n.descFactorial k = k! · n.choose k` — the exact bridge relating falling
    factorial and binomial coefficient (and its inverse
    `Nat.choose_eq_descFactorial_div_factorial`).
  - `Nat.stirlingSecond : ℕ → ℕ → ℕ` (in
    `Mathlib/Combinatorics/Enumerative/Stirling.lean`) with recurrences
    `stirlingSecond_succ_succ`, `stirlingSecond_self`, `stirlingSecond_zero`,
    `stirlingSecond_eq_zero_of_lt`. **Caveat:** the connection identity
    `xʳ = ∑ⱼ S(r,j) x^{(j)}` does **not** appear to be in Mathlib as a named
    lemma; it may need to be proved from the recurrence, or Claim 2 may be
    stated directly in falling-factorial form and the Stirling expansion left as
    a corollary.

### Suggested Approach

Grounded Lean plan, matching the parent's representation:

1. **General falling-factorial absorption (the crux).** Prove, purely over `ℕ`,
   ```
   k.descFactorial r * Nat.choose n k = n.descFactorial r * Nat.choose (n − r) (k − r)
   ```
   or the more directly usable shifted form (with `k` reindexed as `k + r`):
   ```
   (k + r).descFactorial r * Nat.choose n (k + r)
       = n.descFactorial r * Nat.choose (n − r) k.
   ```
   Prove by induction on `r`: the base `r = 0` is `Nat.descFactorial_zero` +
   `Nat.sub_zero`; the step applies `absorption` (i.e.
   `Nat.add_one_mul_choose_eq`) once and unfolds one layer via
   `Nat.descFactorial_succ` on both `k^{(r+1)}` and `n^{(r+1)}`. This is the
   inductive replacement for the parent's hand-written `double_absorption`.
   *Alternative:* route through `Nat.descFactorial_eq_factorial_mul_choose` to
   turn every `descFactorial` into `r! · choose`, converting the identity into a
   pure `choose`/factorial statement provable by `Nat.choose_mul_choose`-type
   Vandermonde reasoning (`Mathlib/Data/Nat/Choose/Mul.lean`,
   `Vandermonde.lean`).

2. **Sum evaluation.** In the real sum
   `∑_{k ∈ range (n+1)} (k.descFactorial r) · binomPMF n p k`, drop the vanishing
   low terms `k < r` (there `k.descFactorial r = 0`), reindex `k ↦ k + r` with
   `Finset.sum_range_succ'` / a `Finset` shift, apply step 1 to rewrite each
   term, factor out the constant `n.descFactorial r · pʳ` with `Finset.mul_sum`,
   and recognize the residual sum
   `∑_{k} C(n−r, k) pᵏ (1−p)^{(n−r)−k}` as `1` via `binomial_expansion`
   (`= (p + (1−p))^{n−r} = 1`) — precisely the closing move in the existing
   `binomial_mean` / `binomial_second_factorial_moment` proofs.

3. **Multinomial marginal (Claim 3).** Re-run the parent's
   `multinomial_second_moment` skeleton verbatim with the statistic `k(i₀)²`
   replaced by `(k i₀).descFactorial r`:
   `Finset.sum_fiberwise_of_maps_to` over `j = k i₀` (the `hmaps_to` bound uses
   `Finset.single_le_sum` and `Finset.mem_piAntidiag`), on each fiber the
   constant `j.descFactorial r` factors out via `Finset.mul_sum`, and the fiber
   probability sum collapses to `binomPMF n (p i₀) j` by
   `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`. Then invoke Claim 1.

4. **Ordinary moments (Claim 2).** Either (a) prove
   `xʳ = ∑ⱼ S(r,j) x^{(j)}` over `ℝ` by induction on `r` using
   `stirlingSecond_succ_succ` and `x · x^{(j)} = x^{(j+1)} + j · x^{(j)}`
   (Pochhammer recurrence), then combine termwise with Claim 1 and
   `Finset.sum_comm`; or (b) state `E[Xʳ]` directly and derive the low cases
   (`r = 1, 2`) to confirm consistency with the parent. Given the Stirling
   connection identity is not prepackaged, expect the bulk of the effort here to
   be that `ℝ`-level expansion.

**Verified name check.** `binomPMF`, `absorption`, `double_absorption`,
`binomial_mean`, `binomial_second_factorial_moment`, `binomial_variance`,
`binomial_expansion` are from `Proofs/BinomialTheoremOQ03.lean`;
`multinomialProb`, `multinomial_mean`, `piAntidiag` usage and
`sum_fiberwise_of_maps_to` from the OQ03/OQ04 files;
`multinomial_marginal_pmf` from `BinomialTheoremOQ02OQ01OQ02`. Mathlib names
`Nat.descFactorial(_succ/_zero/_one)`, `Nat.descFactorial_eq_factorial_mul_choose`,
`Nat.add_one_mul_choose_eq`, `Nat.stirlingSecond` are confirmed present in the
checkout's mathlib (v4.26.0). The `xʳ = ∑ S(r,j) x^{(j)}` identity is the one
piece I could **not** find as a ready-made Mathlib lemma — treat it as
to-be-proved.

### Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - probability
  - multinomial-distribution
  - factorial-moment
  - binomial-marginal
  - fiber-grouping
  - combinatorics
  - descFactorial
  - stirling-numbers
```

Rationale: Claim 1 (the falling-factorial moment) is genuinely tractable — a
clean induction on `r` reusing the parent's absorption/normalization machinery,
so the core deliverable is well within reach (tractability 7). Claim 3 is a
mechanical re-skinning of the parent proof. The Stirling-based ordinary-moment
corollary (Claim 2) is the only part with real risk, because the connection
identity is not prepackaged in Mathlib; a solver may reasonably ship Claims 1
and 3 first and treat Claim 2 as a follow-on. Significance 6: uniform-in-`r`
result that subsumes several existing special-case lemmas and adds a reusable
binomial-factorial-moment fact.

### Related Gallery Proofs

- **`binomial-theorem-oq-02-oq-01-oq-04`** (parent) — second moment / variance of
  multinomial marginals via fiber grouping; the `r = 2` case of Claim 1/3.
- **`binomial-theorem-oq-03`** — binomial mean (`r = 1`), second factorial moment
  (`r = 2`), variance, and the `absorption` / `double_absorption` identities this
  problem generalizes to all `r`.
- **`binomial-theorem-oq-02-oq-01-oq-03`** — off-diagonal cross-moments /
  covariance `Cov(Xᵢ,Xⱼ) = −n pᵢ pⱼ`; the natural next target after single-index
  higher moments is mixed factorial moments `E[Xᵢ^{(r)} Xⱼ^{(s)}]`.
- **`binomial-theorem-oq-02-oq-01-oq-02`** — marginal PMF `P(Xᵢ = j) =
  binomPMF n pᵢ j`, the identity that collapses each fiber sum.
- **`binomial-theorem`** (root) — the binomial theorem `add_pow` /
  `binomial_expansion` underlying the normalization `∑ₖ C(n,k) pᵏ(1−p)^{n−k} = 1`.
```
