# Problem: Multi-Symbol AWGN Output Power — Second Moment of a Sum of Zero-Mean Pairwise-Independent Signals

**Slug**: shannon-channel-coding-awgn-oq-02-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $(\Omega, \mathcal{F}, \mu)$ be a probability space and let $X_1, \dots, X_n : \Omega \to \mathbb{R}$
(indexed by a `Finset s` over some index type $\iota$) be square-integrable, i.e. $X_i \in L^2(\mu)$ for
each $i \in s$. Assume the family is **pairwise independent**:
$$X_i \perp\!\!\!\perp X_j \quad \text{for all } i \neq j \in s.$$

Then the variance of the sum is the sum of the variances:
$$\operatorname{Var}\!\Big[\sum_{i \in s} X_i\Big] \;=\; \sum_{i \in s} \operatorname{Var}[X_i].$$

If in addition every contribution is **zero-mean**, $\mathbb{E}[X_i] = 0$ for all $i \in s$, then the sum is
itself zero-mean ($\mathbb{E}[\sum_i X_i] = \sum_i \mathbb{E}[X_i] = 0$ by linearity), and since for a zero-mean
variable the second moment equals the variance ($\mathbb{E}[W^2] = \operatorname{Var}[W]$ when $\mathbb{E}[W]=0$),
we obtain the **multi-symbol output-power identity**:
$$\mathbb{E}\!\Big[\Big(\sum_{i \in s} X_i\Big)^{\!2}\Big] \;=\; \sum_{i \in s} \mathbb{E}[X_i^2].$$

Naming the per-symbol powers $P_i = \mathbb{E}[X_i^2]$, the aggregate output power is $\sum_{i \in s} P_i$.

The substantive probability theorem is the variance-of-a-finite-sum law for pairwise-independent families,
`ProbabilityTheory.IndepFun.variance_sum`. The rest is the zero-mean reduction $\mathbb{E}[W^2]=\operatorname{Var}[W]$
already isolated by the parent entry.

### Plain Language

The parent entry proved that for a single additive channel $Y = X + Z$ (input plus noise), the output power
splits as $\mathbb{E}[Y^2] = \mathbb{E}[X^2] + \mathbb{E}[Z^2] = P + N$, because independence kills the covariance
cross-term. This child generalizes from two independent contributions to an arbitrary finite family of them:
when many independent zero-mean signals are summed at a receiver, their powers simply **add**. There are no cross-terms
because pairwise independence forces every covariance $\operatorname{Cov}[X_i, X_j]$ ($i \neq j$) to vanish.

### Why This Matters

This is the exact identity behind **multi-antenna (MIMO) and multi-symbol** AWGN reasoning. When $n$ independent
symbols or $n$ independent antenna/noise contributions superimpose at the output, the total average power is the
sum of the individual powers. Additivity of power across independent contributions is the workhorse assumption in
almost every capacity, SNR, and power-budget calculation for Gaussian channels — e.g. the per-subcarrier power split
in OFDM, the sum-power constraint in MIMO, and the aggregation of independent interference terms. Formalizing it in
full generality (finite family, only pairwise independence needed) turns a repeatedly-assumed engineering fact into a
reusable theorem, extending the parent's discharge of the converse hypothesis `hvar` from the 2-term case to the
$n$-term case.

## Known Results

### What's Already Proven

- **Parent entry `shannon-channel-coding-awgn-oq-02`** (verified, 0-axiom, `ShannonChannelCodingAWGNOQ02.lean`):
  - `second_moment_eq_variance`: for zero-mean $X \in L^2$, $\mathbb{E}[X^2] = \operatorname{Var}[X]$ (via `variance_eq_sub` + `ring`).
  - `awgn_output_variance`: for independent $X, Z \in L^2$, $\operatorname{Var}[X+Z] = \operatorname{Var}[X] + \operatorname{Var}[Z]$ (direct `IndepFun.variance_add`).
  - `awgn_second_moment`: $\mathbb{E}[(X+Z)^2] = \mathbb{E}[X^2] + \mathbb{E}[Z^2]$ for zero-mean independent $X, Z$.
  - `awgn_output_power`: $\mathbb{E}[(X+Z)^2] = P + N$ with $P = \mathbb{E}[X^2]$, $N = \mathbb{E}[Z^2]$.
- **Mathlib** (`Mathlib/Probability/Moments/Variance.lean`) already provides the finite-family generalization of the
  variance-of-a-sum law:
  - `ProbabilityTheory.IndepFun.variance_sum` — **the key lemma**. Verified signature:
    ```
    nonrec theorem IndepFun.variance_sum {ι : Type*} {X : ι → Ω → ℝ} {s : Finset ι}
        (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
        (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) :
        variance (∑ i ∈ s, X i) μ = ∑ i ∈ s, variance (X i) μ
    ```
    Note it requires only **pairwise** independence (`Set.Pairwise` over the Finset), not mutual independence, and its
    hypotheses are per-element `MemLp (X i) 2 μ`. (`⟂ᵢ[μ]` is notation for `IndepFun`.)
  - `ProbabilityTheory.variance_eq_sub`: $\operatorname{Var}[X] = \mathbb{E}[X^2] - (\mathbb{E}[X])^2$ for $X \in L^2$ on a probability measure.
  - `ProbabilityTheory.variance_sum'` / `variance_sum`: the general covariance expansion $\operatorname{Var}[\sum_i X_i] = \sum_{i,j} \operatorname{Cov}[X_i,X_j]$ (needs `[IsFiniteMeasure μ]`).

### What's Still Open

Nothing deep is open mathematically — this is an *assembly* task. The gap is that the gallery has no formalized
$n$-term version: the parent stops at the 2-term `awgn_second_moment`/`awgn_output_power`. We must:
1. Lift `second_moment_eq_variance` to the sum $\sum_i X_i$ (it is again zero-mean, so it applies verbatim).
2. Invoke `IndepFun.variance_sum` for the pairwise-independent family.
3. Rewrite each per-term variance back to a second moment via the zero-mean identity, obtaining $\mathbb{E}[(\sum_i X_i)^2] = \sum_i \mathbb{E}[X_i^2]$.

### Our Goal

Produce a verified, 0-axiom Lean file (child entry) stating and proving:
- `multi_output_variance`: $\operatorname{Var}[\sum_{i \in s} X_i] = \sum_{i \in s} \operatorname{Var}[X_i]$ (thin wrapper over `IndepFun.variance_sum`).
- `multi_second_moment`: for zero-mean pairwise-independent $X_i \in L^2$, $\mathbb{E}[(\sum_{i \in s} X_i)^2] = \sum_{i \in s} \mathbb{E}[X_i^2]$.
- `multi_output_power`: with $P_i = \mathbb{E}[X_i^2]$, the output power is $\sum_{i \in s} P_i$ — the multi-symbol restatement generalizing the parent's `hvar`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `shannon-channel-coding-awgn-oq-02` | Direct parent; the 2-term output-power identity this child generalizes | `IndepFun.variance_add`, `variance_eq_sub`, zero-mean reduction |
| `shannon-channel-coding-awgn` | Grandparent; AWGN capacity $C = \tfrac12\log(1+P/N)$ whose converse takes the output power as hypothesis `hvar` | differential entropy, converse bound |
| `shannon-channel-coding-oq-01` | Great-grandparent; capacities of concrete channels (BSC, BEC, AWGN) | channel capacity computations |

## Initial Thoughts

### Potential Approaches

1. **(Recommended) Invoke `IndepFun.variance_sum` directly, then reduce to second moments via zero mean.**
   - Prove a lemma `sum_mean_zero`: $\mathbb{E}[\sum_{i \in s} X_i] = 0$ from $\forall i \in s,\ \mathbb{E}[X_i]=0$ using
     `MeasureTheory.integral_finset_sum` (linearity over a Finset; needs per-term integrability from `MemLp.integrable one_le_two`).
   - `multi_output_variance` := `IndepFun.variance_sum hs hpair` verbatim.
   - `multi_second_moment`: chain
     $\mathbb{E}[(\sum_i X_i)^2] = \operatorname{Var}[\sum_i X_i]$ (zero-mean, parent's `second_moment_eq_variance` applied to the sum)
     $= \sum_i \operatorname{Var}[X_i]$ (`IndepFun.variance_sum`)
     $= \sum_i \mathbb{E}[X_i^2]$ (`Finset.sum_congr` + `second_moment_eq_variance` per term, using $\mathbb{E}[X_i]=0$).
   - Cleanest: reuse the parent's `second_moment_eq_variance` lemma both for the sum and termwise.

2. **Direct covariance expansion via `variance_sum'`.** Expand $\operatorname{Var}[\sum X_i] = \sum_{i,j}\operatorname{Cov}[X_i,X_j]$
   and kill off-diagonal terms with `IndepFun.covariance_eq_zero`. This re-derives `IndepFun.variance_sum` by hand — strictly
   more work; only worth it if the packaged lemma's hypotheses somehow don't match. Not recommended.

3. **Induction on the Finset** (`Finset.induction`) reducing to the parent's 2-term `awgn_output_variance` at each step.
   Conceptually appealing (shows the child *extends* the parent) but requires re-establishing independence of $X_i$ from the
   partial sum $\sum_{j \in t} X_j$ at each step, which is *not* free from pairwise independence alone (independence of a
   variable from a sum needs more than pairwise). This is exactly why Mathlib's `variance_sum` works at the covariance level
   instead. Avoid — approach 1 sidesteps this pitfall entirely.

### Key Difficulties

- **Pairwise vs mutual independence.** The identity holds under *pairwise* independence (covariances vanish pairwise), and
  `IndepFun.variance_sum` is stated with `Set.Pairwise`. Do **not** strengthen the hypothesis to mutual/`iIndepFun` — that
  would be a weaker, less general result. Note this is precisely why an inductive "peel one term off the sum" argument is
  awkward: independence of $X_i$ from the *partial sum* is a mutual-type statement, whereas the covariance-level proof
  needs only pairwise. Approach 1 inherits the correct pairwise hypothesis for free.
- **Hypotheses/typeclasses of the Mathlib lemma.** `IndepFun.variance_sum` needs `∀ i ∈ s, MemLp (X i) 2 μ` and lives in a
  context requiring a finite measure; `variance_eq_sub` (for the zero-mean reduction) requires `[IsProbabilityMeasure μ]`.
  Use `[IsProbabilityMeasure μ]` throughout (as the parent does) — it implies `IsFiniteMeasure` and matches `variance_eq_sub`.
- **Integrability side conditions for the mean.** Showing $\mathbb{E}[\sum_i X_i] = 0$ requires linearity of the integral
  over a Finset (`integral_finset_sum`), which needs each $X_i$ integrable. Get it from `MemLp.integrable one_le_two`
  ($1 \le 2$) on the (finite) probability measure. This is the finite-family analogue of the parent's `hmean` step.
- **Encoding pairwise independence.** Feeding `Set.Pairwise ↑s (fun i j => IndepFun (X i) (X j) μ)` correctly (symmetry over
  the coercion `↑s : Set ι`) is the one mildly fiddly spot; the parent only had a single `IndepFun X Z μ`.

### What Would a Proof Need?

- Index the family as `X : ι → Ω → ℝ` over a `Finset s` (mirroring Mathlib's `variance_sum` signature) — the most reusable form.
- Hypotheses: `[IsProbabilityMeasure μ]`, `hs : ∀ i ∈ s, MemLp (X i) 2 μ`, `hpair : Set.Pairwise ↑s (fun i j => IndepFun (X i) (X j) μ)`, and `hmean : ∀ i ∈ s, μ[X i] = 0`.
- Building blocks: `IndepFun.variance_sum`, `variance_eq_sub` (or the parent's `second_moment_eq_variance`), `integral_finset_sum`, `MemLp.integrable`, `Finset.sum_congr`.
- Optional: a `Fintype ι` corollary (`multi_output_power` over all of `ι`) for the "sum over all antennas/symbols" reading.

## Tractability Assessment

**Difficulty**: Low–Medium

**Justification**: The mathematically substantive step — variance of a finite sum of pairwise-independent variables —
is already a Mathlib theorem (`IndepFun.variance_sum`) with exactly the right hypotheses. The remaining work is the
zero-mean reduction (already isolated and reusable from the parent as `second_moment_eq_variance`) plus a Finset-linearity
argument for the mean of the sum. No new mathematics; the challenge is purely the Lean plumbing of Finset sums, the
`Set.Pairwise` hypothesis, and matching integrability/measure typeclasses. The parent provides a near-complete template.

**Estimated Effort**: 1 focused session; ~120–170 lines, ~3–5 theorems, targeting verified/0-axiom.

## References

### Papers

- C. E. Shannon, "A Mathematical Theory of Communication," *Bell System Technical Journal*, 1948 — origin of AWGN channel capacity and the power/variance framing.
- T. M. Cover and J. A. Thomas, *Elements of Information Theory*, 2nd ed., Wiley-Interscience, 2006 — AWGN capacity $C=\tfrac12\log(1+P/N)$ and additivity of power over independent contributions; MIMO/parallel-Gaussian channels.

### Online Resources

- Wikipedia: "Variance" (Bienaymé's identity: variance of a sum of uncorrelated variables is the sum of variances).
- Wikipedia: "Additive white Gaussian noise", "MIMO" — multi-antenna sum-power model.

### Mathlib

- `ProbabilityTheory.IndepFun.variance_sum` — variance of a finite sum of **pairwise-independent** variables equals the sum of variances (`Mathlib/Probability/Moments/Variance.lean`). **The key lemma.**
- `ProbabilityTheory.variance_eq_sub` — $\operatorname{Var}[X] = \mathbb{E}[X^2] - (\mathbb{E}[X])^2$ for $X \in L^2$ on a probability measure.
- `ProbabilityTheory.variance_sum'` / `ProbabilityTheory.variance_sum` — general expansion $\operatorname{Var}[\sum_i X_i] = \sum_{i,j}\operatorname{Cov}[X_i,X_j]$ (fallback for Approach 2; needs `[IsFiniteMeasure μ]`).
- `ProbabilityTheory.IndepFun` (notation `⟂ᵢ[μ]`) and `ProbabilityTheory.IndepFun.covariance_eq_zero` (verify) — covariance of independent variables vanishes.
- `MeasureTheory.integral_finset_sum` (verify exact name) — linearity of the integral over a `Finset`, for $\mathbb{E}[\sum_i X_i] = \sum_i \mathbb{E}[X_i]$.
- `MeasureTheory.MemLp.integrable` — $L^2 \Rightarrow L^1$ on a finite measure (`1 ≤ 2`), supplying integrability.
- `Finset.sum_congr` — rewrite the summand termwise (variance $\to$ second moment).

## Metadata
```yaml
tags:
  - probability
  - information-theory
  - variance
  - independence
related_proofs:
  - shannon-channel-coding-awgn-oq-02
difficulty: low
source: gallery-gap
created: 2026-06-30
```
