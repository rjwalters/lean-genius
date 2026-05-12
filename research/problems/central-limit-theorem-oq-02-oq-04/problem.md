# Problem: Mixing CLT with Ibragimov 1962 Polynomial Mixing Rates

## Statement

### Plain Language

The parent file `CentralLimitTheoremOQ02.lean` introduces an `AlphaMixingSequence`
structure and the long-run variance, but the actual mixing CLT (Ibragimov 1962)
is axiomatized with abstract decay assumptions.  This extension makes the
Ibragimov 1962 conditions **explicit and quantitative**:

> Let `{X_n}` be a strictly stationary, real, mean-zero sequence with
> `E[|X_1|^{2+δ}] < ∞` for some `δ > 0`, and α-mixing coefficient `α(n)`
> satisfying the **polynomial decay condition**
>
> ```
>   α(n) ≤ C · n^{-r}   for some  r > (2 + δ) / δ.
> ```
>
> Define the **long-run variance**
>
> ```
>   σ² := Var(X_1) + 2 ∑_{k≥1} Cov(X_1, X_{1+k}).
> ```
>
> Assume `σ² > 0`.  Then
>
> ```
>   S_n / √n  ⇒  N(0, σ²)   in distribution,
> ```
>
> where `S_n = X_1 + ⋯ + X_n`.

The novelty of OQ-02-OQ-04 versus the parent OQ-02 is:

1. **Explicit polynomial rate** `α(n) ≲ n^{-r}` (parent only assumes
   `α(n) → 0` plus the abstract Ibragimov summability `∑ α(n)^{δ/(2+δ)} < ∞`).
2. **Quantitative coupling** between `δ` and `r` — the threshold
   `r > (2+δ)/δ` is the *necessary* one for Ibragimov's covariance
   inequality to make the long-run variance series absolutely convergent.
3. **Constructive route** to the long-run variance formula: under the
   polynomial rate, `∑_{k≥1} |Cov(X_1, X_{1+k})|` is dominated by a
   convergent series, sharpening parent's `Tendsto α atTop (nhds 0)`.

### Formal Statement

$$
\frac{1}{\sqrt n}\,S_n \;\xRightarrow[n\to\infty]{d}\; \mathcal N(0,\sigma^2),
\qquad
\sigma^2 = \operatorname{Var}(X_1) + 2\sum_{k\ge 1}\operatorname{Cov}(X_1, X_{1+k}),
$$

under
$$
\mathbb E[X_1] = 0,\quad
\mathbb E[|X_1|^{2+\delta}] < \infty,\quad
\alpha(n) \le C\,n^{-r},\quad
r > \frac{2+\delta}{\delta}.
$$

## Classification

```yaml
tier: B
significance: 7
tractability: 4
tags:
  - probability
  - mixing
  - clt
  - ibragimov
  - polynomial-rate
  - extension
  - seeker-selected
```

**Significance**: 7/10 — quantitative dependent-CLT; standard in time-series
econometrics and ergodic-theory applications.
**Tractability**: 4/10 — the full proof needs Bernstein blocks + Lindeberg /
characteristic-function method; Mathlib has no α-mixing primitives.

## Why This Matters

1. **Quantitative dependent CLT.** Polynomial mixing rates appear in MCMC
   convergence, GARCH-type models, ergodic-theoretic shift sequences, and
   Birkhoff-sum CLTs for hyperbolic dynamical systems.  Knowing the explicit
   `r > (2+δ)/δ` threshold is what practitioners actually use.
2. **Bridge to Mathlib.** Mathlib currently has **no** α-mixing API.  Any
   serious formalization of dependent-CLT phenomena (ergodic averages, time
   series, dynamical systems) eventually needs `alphaMixingCoeff` and a
   covariance inequality.  This OQ-02-OQ-04 is the smallest *concrete*
   theorem statement that forces the right primitives.
3. **Closes a parent gap.** Parent `CentralLimitTheoremOQ02.lean` contains
   `axiom martingale_clt` plus a stated-but-unproved Ibragimov CLT in the
   docstring.  OQ-02-OQ-04 gives the **theorem-shaped** statement so the
   axiom can later be discharged or refined.

## Mathematical Background

### Davydov / Ibragimov covariance inequality

For random variables `X ∈ ℒ^p(ℱ)`, `Y ∈ ℒ^q(ℱ')` with `1/p + 1/q < 1`,
$$
|\operatorname{Cov}(X, Y)| \;\le\; 8\,\alpha(\mathcal F, \mathcal F')^{1 - 1/p - 1/q}\,\|X\|_p\,\|Y\|_q.
$$

Applied with `p = q = 2 + δ`, exponent `1 - 2/(2+δ) = δ/(2+δ)`:
$$
|\operatorname{Cov}(X_1, X_{1+k})| \;\le\; 8\,\alpha(k)^{\delta/(2+\delta)}\,\|X_1\|_{2+\delta}^2.
$$

So `∑_k α(k)^{δ/(2+δ)} < ∞` ⇒ `∑_k |Cov(X_1, X_{1+k})| < ∞`, and the
long-run variance series converges absolutely.

### Polynomial-rate threshold

`α(n) ≤ C n^{-r}` ⇒ `α(n)^{δ/(2+δ)} ≤ C^{δ/(2+δ)} n^{-r δ/(2+δ)}`,
which is summable iff `r δ/(2+δ) > 1`, i.e. `r > (2+δ)/δ`.

This is the **sharp** polynomial threshold for absolute convergence of
the long-run variance via Davydov's bound.  Sharper constants come from
Rio's inequality `|Cov(X,Y)| ≤ 2 π α^{1-2/p} ‖X‖_p ‖Y‖_p` but the
threshold rate is the same.

### Proof outline (Ibragimov 1962)

1. **Bernstein block decomposition.** Partition `{1, …, n}` into alternating
   **large blocks** of size `p_n` and **small blocks** of size `q_n` with
   `p_n + q_n ≪ n`, `q_n / p_n → 0`, `n · α(q_n) → 0`.
2. **Approximate independence.** By the α-mixing inequality, blocks
   separated by `q_n` are approximately independent up to a total error
   `O(n / (p_n + q_n) · α(q_n))`.
3. **Lindeberg for large-block sum.** The sum of large-block contributions
   is approximately a sum of i.i.d. variables; the `(2+δ)`-moment plus
   Bernstein block sizing gives the Lindeberg condition.
4. **Negligibility of small blocks.** Small-block contribution has variance
   `O(n · q_n / (p_n + q_n))`, which is `o(n)` under the right sizing.
5. **Convergence of normalization.** The variance of the rescaled large-
   block sum converges to `σ²` (long-run variance) via the covariance
   inequality.

The polynomial rate `r > (2+δ)/δ` is exactly what allows the choice
`p_n = ⌊n^{1 - 1/r}⌋`, `q_n = ⌊n^{1 - 1/r - ε}⌋` to satisfy all four
constraints simultaneously.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `central-limit-theorem` | Classical i.i.d. CLT (special case `α = 0`) |
| `central-limit-theorem-oq-02` | Parent — martingale + mixing CLT scaffold |
| `central-limit-theorem-oq-01-oq-01-oq-04` | Lyapunov-condition refinement (moment exponent) |
| `binomial-clt`, `birthday-problem-oq-01-oq-02` | Coupling/CLT under mild dependence |
| `laws-of-large-numbers-oq-04` | LLN under dependence; conceptual cousin |

## Open Questions

- **OQ-A: Sharp threshold.** Is `r > (2+δ)/δ` necessary, or can one push to
  `r = (2+δ)/δ + ε` for arbitrarily small `ε > 0` via slowly varying logs?
  Bradley 1981 constructs examples saturating the polynomial threshold.
- **OQ-B: Quantitative Berry-Esseen.** Under the same hypotheses, give an
  explicit rate `sup_x |F_n(x) - Φ(x)| ≤ C · n^{-γ(δ, r)}`.  Rio 1996,
  Tikhomirov 1980 give the canonical rates.
- **OQ-C: Long-run variance estimator.** Can `σ²` be estimated from a
  finite sample under polynomial mixing?  Connects to HAC variance
  estimators (Newey-West 1987, Andrews 1991).
