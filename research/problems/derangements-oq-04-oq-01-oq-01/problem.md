# Problem: Poisson(1) Limit of the Fixed-Point Distribution

**Slug**: derangements-oq-04-oq-01-oq-01
**Created**: 2026-06-30T22:49:26-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

Let $S(n,k)$ be the number of permutations of an $n$-element set with **exactly
$k$ fixed points** (the rencontres / partial-derangement numbers). The parent entry
proves the finite closed form, over any characteristic-zero field,
$$
\frac{S(n,k)}{n!} \;=\; \frac{1}{k!}\sum_{j=0}^{n-k}\frac{(-1)^j}{j!}.
$$
The goal is the $n \to \infty$ limit: for each fixed $k \in \mathbb{N}$,
$$
\lim_{n\to\infty}\frac{S(n,k)}{n!}
  \;=\; \frac{1}{k!}\sum_{j=0}^{\infty}\frac{(-1)^j}{j!}
  \;=\; \frac{e^{-1}}{k!}.
$$
In Lean, with the count realized as a cardinality over `Equiv.Perm (Fin n)`:
$$
\texttt{Filter.Tendsto}\Big(\lambda\, n \mapsto \tfrac{S(n,k)}{n!} : \mathbb{R}\Big)\ \texttt{atTop}\ \big(\mathcal{N}(\tfrac{e^{-1}}{k!})\big),
$$
i.e. the fixed-point-count distribution converges pointwise (in $k$) to the
**Poisson(1)** probability mass function $p(k) = e^{-1}/k!$.

### Plain Language

Pick a permutation of $\{1,\dots,n\}$ uniformly at random and count how many
elements it leaves fixed. The probability of seeing exactly $k$ fixed points is
$S(n,k)/n!$. As $n$ grows, this probability settles down to $e^{-1}/k!$ — the
probability of the value $k$ under a Poisson distribution with mean $1$. So the
number of fixed points of a large random permutation behaves like a Poisson(1)
random variable: on average one fixed point, with the classic $1/e \approx 0.3679$
chance of a full derangement ($k = 0$).

### Why This Matters

- **Completes the rencontres story.** The parent gives the *finite* identity; this
  entry gives its *asymptotic* payoff — the single most-quoted fact about the
  distribution of fixed points.
- **The canonical Poisson approximation.** Fixed points of a random permutation are
  the textbook example where a sum of weakly dependent indicators converges to a
  Poisson law; here it falls out of an exact closed form rather than a coupling or
  Chen–Stein argument.
- **Recovers $1/e$ at $k=0$.** The $k=0$ case is exactly the derangement limit
  $D_n/n! \to 1/e$, tying this child to `derangements-oq-03` (the sharp rate) and to
  the classical Montmort matching-problem answer.

## Known Results

### What's Already Proven

- **Finite closed form** (parent `derangements-oq-04-oq-01`,
  `card_perms_with_kfixed_closed_form`): over any characteristic-zero field
  $\mathbb{K}$,
  $S(n,k) = \dfrac{n!}{k!}\sum_{j=0}^{n-k}(-1)^j/j!$ for $k \le n$; with ℚ/ℝ
  specializations `card_perms_with_kfixed_closed_form_rat` / `_real`.
- **Truncated-exponential phrasing** (`card_perms_with_kfixed_eq_factorial_mul_trunc`):
  the bracket is `DerangementsOQ04.truncExpNegOne 𝕜 (n-k+1)`, the order-$(n-k)$
  truncation of the series for $e^{-1}$.
- **Combinatorial count** (sibling `derangements-oq-02`,
  `PartialDerangements.card_perms_with_kfixed`): $S(n,k) = \binom{n}{k}\,D_{n-k}$.
- **Derangement closed form** (`DerangementsOQ04.numDerangements_closed_form`):
  $(D_m : \mathbb{K}) = m!\sum_{j\le m}(-1)^j/j!$.
- **Exponential series in Mathlib**: `Real.exp_eq_exp_ℝ` / `NormedSpace.expSeries`
  and `Real.exp (-1) = ∑' j, (-1)^j / j!` give the target value of the infinite sum.

### What's Still Open

- The pointwise Poisson(1) limit stated above (this entry's goal).
- Uniform / total-variation convergence of the whole distribution to Poisson(1)
  (a strictly stronger, out-of-scope statement).
- The bivariate exponential generating function $e^{(x-1)t}/(1-t)$ (the sibling
  second open question, separate from this one).

### Our Goal

Prove, for each fixed $k$, that $\lambda\, n \mapsto S(n,k)/n! \to e^{-1}/k!$ as
$n \to \infty$ over $\mathbb{R}$. The finite identity is already in hand, so the
task is a **clean analytic limit**: show the truncated alternating sum
$\sum_{j=0}^{n-k}(-1)^j/j!$ converges to $e^{-1}$ and divide by the constant $k!$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| derangements-oq-04-oq-01 | Parent: supplies the finite closed form $S(n,k)=(n!/k!)\sum(-1)^j/j!$ being taken to the limit | choose/factorial bridge, `linear_combination` |
| derangements-oq-04 | Grandparent: field derangement closed form $D_m = m!\sum(-1)^j/j!$ and `truncExpNegOne` | induction, truncated exponential |
| derangements-oq-03 | Sibling: sharp rate $|D_n/n! - 1/e| \le 1/(n+1)!$ — the $k=0$ instance with an explicit tail bound | alternating-series tail estimate |
| derangements-oq-02 | Foundational: $S(n,k)=\binom{n}{k}D_{n-k}$ | support bijection to derangements |

## Initial Thoughts

### Potential Approaches

1. **Approach A — partial sums of `Real.exp (-1)`.**
   $e^{-1} = \sum_{j=0}^{\infty}(-1)^j/j!$ via `Real.exp_eq_tsum` / `NormedSpace.expSeries`
   at $x = -1$. The truncated sum $\sum_{j=0}^{n-k}(-1)^j/j!$ is exactly the
   $(n-k+1)$-th partial sum. Since the exponential series is summable, its partial
   sums tend to the tsum (`HasSum.tendsto_sum_nat`); reindex $n \mapsto n-k$ (a
   `Filter.Tendsto` on `atTop`, cofinal shift) to get the truncation $\to e^{-1}$.
   Then multiply by the constant $1/k!$ with `Filter.Tendsto.const_mul` /
   `Tendsto.div_const`.
   - Why it works: the hard combinatorics is already the finite identity; only a
     summable-series limit remains, and Mathlib has the exact building block.
   - Risk: index bookkeeping — the sum runs to $n-k$, the range is $n-k+1$, and the
     $k \le n$ hypothesis must be threaded so the closed form applies eventually.

2. **Approach B — explicit alternating-tail bound (reuse derangements-oq-03).**
   For an alternating series with decreasing terms, $\big|\sum_{j=0}^{m}(-1)^j/j! - e^{-1}\big| \le 1/(m+1)!$.
   The sibling `derangements-oq-03` already formalizes this tail estimate for the
   $k=0$ case; lift it to a `Tendsto` via `squeeze_zero` / `tendsto_of_tendsto_of_tendsto_of_le_of_le`
   using $1/(m+1)! \to 0$ (`Nat.factorial` grows, `tendsto_one_div_atTop` style).
   - Why it works: gives an effective rate, mirrors an existing entry, avoids
     `tsum` machinery.
   - Risk: re-deriving the tail bound if the sibling lemma is not directly reusable.

### Key Difficulties

- Threading the eventual hypothesis $k \le n$: the closed form holds only for
  $n \ge k$, so the limit must be argued on the cofinal tail (`Filter.eventually_atTop`).
- Reindexing the sum bound $n-k$ against Mathlib's partial-sum lemmas, which are
  phrased in terms of the summation range endpoint.
- Casting: cardinalities are `ℕ`; the limit lives in `ℝ`; keep `push_cast` /
  `Nat.cast` coercions clean.

### What Would a Proof Need?

- Key lemma 1: `Real.exp (-1) = ∑' j, (-1)^j / j!` (from `Real.exp_eq_tsum` or
  `NormedSpace.expSeries` summability) and `HasSum.tendsto_sum_nat`.
- Key lemma 2: the finite identity `card_perms_with_kfixed_closed_form_real` divided
  through by `n!`, valid eventually in `n`.
- Key lemma 3: partial-sum reindexing on `atTop` (`Filter.tendsto_atTop` cofinal
  shift by $k$) plus `Tendsto.const_mul` for the $1/k!$ factor.
- Technical requirement: `Filter.Tendsto`, `tsum`, `HasSum`, `Nat.factorial`,
  `Real.exp`, and eventual-equality of two sequences (`Filter.Tendsto.congr'`).

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The combinatorial and algebraic content is fully proven in the parent/siblings;
  what remains is a standard limit of a convergent alternating series.
- The exponential series, its summability, and partial-sum convergence are all in
  Mathlib (`Real.exp_eq_tsum`, `NormedSpace.expSeries`, `HasSum.tendsto_sum_nat`).
- The sibling `derangements-oq-03` already handles the $k=0$ tail bound, giving a
  proven template to generalize.
- The only real friction is index/eventual-hypothesis bookkeeping and casts, which
  is fiddly but routine.

**Estimated Effort**:
- Exploration: 0.5–1 day
- If tractable: 2–4 days
- If hard: 1 week (only if the reindexing/eventual-equality plumbing proves stubborn)

## References

### Papers
- Montmort, P. R., *Essay d'analyse sur les jeux de hasard*, 1708 — the problème des
  rencontres; the matching problem whose limiting probability is $1/e$.
- Euler, L., *Calcul de la probabilité dans le jeu de rencontre*, 1751 — establishes
  $D_n = n!\sum_{k=0}^n(-1)^k/k!$, the $k=0$ case.
- Riordan, J., *An Introduction to Combinatorial Analysis*, Wiley, 1958 — rencontres
  numbers $S(n,k) = \binom{n}{k}D_{n-k}$ and their asymptotics.
- Barbour, Holst, Janson, *Poisson Approximation*, Oxford, 1992 — fixed points of a
  random permutation as the canonical Poisson(1) limit.
- Feller, W., *An Introduction to Probability Theory and Its Applications, Vol. I*,
  Wiley — the matching problem and its Poisson limit in the standard probability text.

### Online Resources
- https://en.wikipedia.org/wiki/Rencontres_numbers — closed form and Poisson limit.
- https://en.wikipedia.org/wiki/Random_permutation_statistics — fixed-point count and
  its convergence to Poisson(1).

### Mathlib
- `Mathlib.Analysis.SpecialFunctions.Exp` — `Real.exp`, `Real.exp_eq_tsum`.
- `Mathlib.Analysis.SpecialFunctions.Exponential` / `NormedSpace.expSeries` — the
  exponential series and its summability.
- `Mathlib.Topology.Algebra.InfiniteSum.Basic` — `tsum`, `HasSum`,
  `HasSum.tendsto_sum_nat`.
- `Mathlib.Order.Filter.AtTopBot` / `Mathlib.Topology.Algebra.Order` —
  `Filter.Tendsto`, `Tendsto.const_mul`, cofinal shift and eventual equality.
- `Mathlib.Data.Nat.Factorial.Basic` — `Nat.factorial`, `Nat.factorial_ne_zero`.

## Metadata

```yaml
tags:
  - combinatorics
  - analysis
  - derangements
  - rencontres-numbers
  - poisson-distribution
  - limit
  - exponential-series
  - random-permutations
related_proofs:
  - derangements-oq-04-oq-01
  - derangements-oq-04
  - derangements-oq-03
  - derangements-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-06-30T22:49:26-07:00
```
