# Problem: Paley-Zygmund Inequality in Mathlib's Measure-Theoretic Framework

**Slug**: prob-method-second-moment-oq-01-oq-03
**Created**: 2026-06-30T22:49:26-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The Paley-Zygmund inequality. Let $Z$ be a non-negative random variable on a
probability space $(\Omega, \mathcal{F}, \mathbb{P})$ with finite variance
(equivalently $Z \in L^2$), and let $0 \le \theta \le 1$. Then

$$
\mathbb{P}\bigl(Z > \theta \, \mathbb{E}[Z]\bigr) \;\ge\; (1 - \theta)^2 \, \frac{\mathbb{E}[Z]^2}{\mathbb{E}[Z^2]}.
$$

Equivalently, in terms of the variance $\operatorname{Var}(Z) = \mathbb{E}[Z^2] - \mathbb{E}[Z]^2$,

$$
\mathbb{P}\bigl(Z > \theta \, \mathbb{E}[Z]\bigr) \;\ge\; \frac{(1-\theta)^2 \, \mathbb{E}[Z]^2}{\operatorname{Var}(Z) + \mathbb{E}[Z]^2}.
$$

The target of this research problem is a Lean 4 statement over Mathlib's
`MeasureTheory`/`ProbabilityTheory` API, roughly of the form:

```
theorem paley_zygmund
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Z : Ω → ℝ} (hZ : 0 ≤ᵐ[μ] Z) (hL2 : MemLp Z 2 μ) {θ : ℝ}
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    (1 - θ)^2 * (∫ ω, Z ω ∂μ)^2
      ≤ (μ {ω | θ * (∫ ω, Z ω ∂μ) < Z ω}).toReal * (∫ ω, (Z ω)^2 ∂μ)
```

with the classical ratio form recovered by dividing through by
$\mathbb{E}[Z^2]$ (assuming it is positive).

### Plain Language

If $Z$ is a non-negative quantity that is random, the Paley-Zygmund
inequality guarantees that $Z$ is not too concentrated near zero: with
probability at least $(1-\theta)^2 \mathbb{E}[Z]^2 / \mathbb{E}[Z^2]$, the value
of $Z$ exceeds the fraction $\theta$ of its average. Taking $\theta = 0$
recovers the qualitative statement that $\mathbb{P}(Z > 0) \ge \mathbb{E}[Z]^2/\mathbb{E}[Z^2] > 0$
whenever $\mathbb{E}[Z] > 0$ — a mean-square way of certifying that $Z$ is
sometimes strictly positive.

Where Markov's inequality bounds the *upper* tail ($\mathbb{P}(Z \ge a) \le
\mathbb{E}[Z]/a$) and Chebyshev bounds deviations from the mean, Paley-Zygmund
bounds the *lower* tail from below. It says that a random variable whose second
moment is comparable to the square of its first moment cannot spend all its mass
on being small.

### Why This Matters

Paley-Zygmund is the quantitative heart of the **second moment method** in
probabilistic combinatorics:

- **Lower-tail control.** It complements Chebyshev's inequality. Chebyshev
  (`ProbabilityTheory.meas_ge_le_variance_div_sq`) says $Z$ concentrates near
  its mean; Paley-Zygmund says $Z$ is bounded *away* from $0$ with definite
  probability. Together they are the standard toolkit for showing a counting
  random variable is positive with high probability.
- **Random graphs and thresholds.** In $G(n,p)$, one lets $Z$ count the number
  of copies of a fixed subgraph (or cliques, independent sets, perfect
  matchings, etc.). Showing $\mathbb{E}[Z^2] = (1+o(1))\mathbb{E}[Z]^2$ and applying
  Paley-Zygmund gives $\mathbb{P}(Z > 0) \to 1$, pinning down sharp threshold
  functions for appearance of substructures.
- **Ramsey lower bounds.** The probabilistic lower bounds on Ramsey numbers and
  on clique/independence numbers in random graphs (Alon-Spencer, Chapter 4)
  routinely invoke the second moment method / Paley-Zygmund.

A measure-theoretic version stated over Mathlib's probability API would make all
of these arguments expressible against the same infrastructure used for the
strong law, Chebyshev, and concentration inequalities already in Mathlib — and
it is a natural, self-contained candidate for an upstream mathlib4 contribution.

## Known Results

### What's Already Proven

- **Parent gallery entry `prob-method-second-moment-oq-01`
  (`Proofs/ProbMethodSecondMomentOQ01.lean`, verified, 0 axioms).** Proves the
  quantitative Paley-Zygmund inequality in a *finite, discrete* setting: for
  $f : \alpha \to \mathbb{Q}$ non-negative on a `Finset s` with positive sum and
  $0 \le \theta < 1$,
  $$(1-\theta)^2 \Bigl(\textstyle\sum_s f\Bigr)^2 \le \bigl|\{a \in s : f(a) > \theta \mu\}\bigr| \cdot \sum_s f^2,$$
  where $\mu = (\sum_s f)/|s|$. It includes a private Cauchy-Schwarz lemma
  `sq_sum_le` ($(\sum f)^2 \le |s| \sum f^2$, via $\sum_{i<j}(f_i-f_j)^2 \ge 0$),
  a probability/ratio form `paley_zygmund_probability`, and the $\theta = 0$
  recovery `paley_zygmund_at_zero`.
- **The classical proof is completely standard** (Paley-Zygmund 1932;
  Alon-Spencer). See "Our Goal" and "Initial Thoughts" below.
- **Mathlib already has the surrounding machinery**: expectation as
  `MeasureTheory.integral`, `ProbabilityTheory.variance` and
  `ProbabilityTheory.evariance`, Chebyshev
  (`ProbabilityTheory.meas_ge_le_variance_div_sq`), Markov/Chebyshev for the
  integral (`MeasureTheory.mul_meas_ge_le_lintegral`), Hölder/Cauchy-Schwarz for
  integrals (`MeasureTheory.integral_mul_le_Lp_mul_Lq` and the $L^2$
  `inner_mul_le_norm_mul_norm`), and the `MemLp`/`Lp` framework for $L^2$
  bookkeeping.

### What's Still Open

- No general **measure-theoretic** Paley-Zygmund inequality exists in Mathlib.
- No version stated for arbitrary `IsProbabilityMeasure` spaces with an $L^2$
  random variable exists in the gallery — only the finite `Finset`/`ℚ` version.
- The finite version does not directly imply the continuous version; the
  discrete counting argument must be re-cast in terms of integrals and measures
  of measurable sets.

### Our Goal

Recast the parent's finite Paley-Zygmund result in Mathlib's
measure-theoretic `ProbabilityTheory`/`MeasureTheory` framework, in a form
suitable for **upstream contribution to mathlib4**. Concretely:

1. State the inequality for a non-negative $L^2$ random variable $Z$ on a
   probability space (hypotheses: `IsProbabilityMeasure μ`, `0 ≤ᵐ[μ] Z`,
   `MemLp Z 2 μ`).
2. Prove the **integral split** as the concrete first step: writing
   $A = \{ \omega : Z(\omega) > \theta \, \mathbb{E}[Z]\}$ and its complement,
   $$\mathbb{E}[Z] = \mathbb{E}[Z \cdot \mathbf{1}_A] + \mathbb{E}[Z \cdot \mathbf{1}_{A^c}],$$
   and bound the second term by $\theta \, \mathbb{E}[Z]$ (since $Z \le \theta\mathbb{E}[Z]$
   on $A^c$ and $\mathbb{P}$ is a probability measure).
3. Apply Cauchy-Schwarz to the first term:
   $\mathbb{E}[Z \cdot \mathbf{1}_A] \le \sqrt{\mathbb{E}[Z^2] \cdot \mathbb{P}(A)}$, then combine
   with $\mathbb{E}[Z \cdot \mathbf{1}_A] \ge (1-\theta)\mathbb{E}[Z]$ and square.
4. Provide the ratio (probability) form by dividing by $\mathbb{E}[Z^2]$, and the
   variance form via $\mathbb{E}[Z^2] = \operatorname{Var}(Z) + \mathbb{E}[Z]^2$.

If the statement and proof are clean, package as a mathlib4 PR (likely under
`Mathlib/Probability/` alongside the moment inequalities).

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| prob-method-second-moment-oq-01 | Parent: finite/discrete Paley-Zygmund over `Finset`/`ℚ` — the result to lift | above/below split, Cauchy-Schwarz `sq_sum_le`, `sq_le_sq'` |
| prob-method-second-moment | Grandparent: qualitative second moment method ($\mathbb{P}(Z>0)>0$) | first/second moment comparison |
| cauchy-schwarz | Cauchy-Schwarz is the analytic bridge from first to second moment | inner-product / integral Hölder bound |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Indicator split + integral Cauchy-Schwarz (recommended).**
   Set $A = \{Z > \theta \mathbb{E}[Z]\}$ (measurable since $Z$ is `AEMeasurable`
   from `MemLp`). Write $Z = Z\mathbf{1}_A + Z\mathbf{1}_{A^c}$ and integrate.
   - Why it might work: this is the textbook proof; every step has a direct
     Mathlib counterpart (`integral_add`, `setIntegral`, `MeasureTheory.integral_mul_le_Lp_mul_Lq`
     with $p=q=2$, or `inner_mul_le_norm_mul_norm` in `L²`).
   - Risk: the friction is entirely in API/`MemLp` bookkeeping —
     integrability of $Z\mathbf{1}_A$, measurability of the level set, converting
     between `ENNReal` measures and `Real` integrals (`.toReal`,
     `ENNReal.toReal_le_toReal`), and matching the exact hypotheses Mathlib's
     Hölder lemma expects (`MemLp`, conjugate exponents).

2. **Approach B — Discretize / transfer from the finite version.**
   Approximate $Z$ by simple functions and pass the parent's `Finset` inequality
   to the limit.
   - Why it might work: reuses the already-verified finite result.
   - Risk: limiting arguments over measures of level sets are delicate
     (weak convergence, dominated convergence) and likely *more* work than
     proving the continuous version directly; not recommended.

### Key Difficulties

- **`MemLp`/integrability plumbing**: establishing that $Z$, $Z^2$, and the
  indicator-restricted products are integrable, and threading `MemLp Z 2 μ`
  through Cauchy-Schwarz.
- **`ENNReal` vs `Real`**: measures land in `ENNReal`; the inequality is stated
  in `Real`. Careful use of `.toReal`, finiteness of measures on a probability
  space, and monotonicity lemmas is required.
- **Degenerate cases**: $\mathbb{E}[Z^2] = 0$ (i.e. $Z = 0$ a.e.) and $\theta = 1$
  must be handled so the ratio form is well-defined.

### What Would a Proof Need?

- Key lemma 1: the additive split $\mathbb{E}[Z] = \mathbb{E}[Z\mathbf{1}_A] + \mathbb{E}[Z\mathbf{1}_{A^c}]$
  with $A^c$-term $\le \theta\mathbb{E}[Z]$ (the **concrete first step** of this
  problem).
- Key lemma 2: Cauchy-Schwarz $\mathbb{E}[Z\mathbf{1}_A] \le \sqrt{\mathbb{E}[Z^2]\,\mathbb{P}(A)}$
  via `MeasureTheory.integral_mul_le_Lp_mul_Lq` (or the $L^2$ inner-product
  bound) applied to $Z$ and $\mathbf{1}_A$.
- Technical requirements: measurability of the level set,
  `MemLp`/integrability of the pieces, `ENNReal.toReal` conversions, and the
  algebra to square $(1-\theta)\mathbb{E}[Z] \le \sqrt{\mathbb{E}[Z^2]\,\mathbb{P}(A)}$ into the
  stated inequality.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematics is short and classical — a two-line proof on paper — and the
  finite version is already fully verified in the parent gallery entry.
- The genuine work is engineering: fitting Mathlib's integration API,
  discharging `MemLp`/integrability side conditions, and converting between
  `ENNReal` and `Real`. This is well-trodden ground (Chebyshev, the moment
  inequalities, and Hölder already live in Mathlib).
- All required lemmas exist: `MeasureTheory.integral_mul_le_Lp_mul_Lq`,
  `ProbabilityTheory.variance`, `ProbabilityTheory.meas_ge_le_variance_div_sq`,
  `MemLp`/`Lp` API. No new deep theory is needed.
- A clean statement + proof is a plausible **mathlib4 PR** target, which raises
  the polish bar (naming, generality, docstrings) but not the mathematical
  difficulty.

**Estimated Effort**:
- Exploration: 1-2 days (locating the exact Hölder/`MemLp` lemmas and the right
  statement generality).
- If tractable: 3-7 days for a gallery-quality proof; add time for an
  upstream-ready mathlib4 PR (review iteration on naming and API fit).
- If hard: unknown, only if the `MemLp` bookkeeping proves unexpectedly
  stubborn.

## References

### Papers
- Paley, R.E.A.C. and Zygmund, A., "On some series of functions (1)",
  *Proceedings of the Cambridge Philosophical Society* 26 (1932), 337-357 —
  original source of the inequality, in the study of lacunary trigonometric
  series.
- Alon, N. and Spencer, J.H., *The Probabilistic Method*, 4th ed., Wiley, 2016 —
  Chapter 4, second moment method and Paley-Zygmund with random-graph and
  Ramsey applications.
- Kahane, J.-P., *Some Random Series of Functions*, 2nd ed., Cambridge
  University Press, 1985 — modern treatment of Paley-Zygmund in the context of
  random series.

### Online Resources
- https://en.wikipedia.org/wiki/Paley%E2%80%93Zygmund_inequality — statement,
  standard proof, and the variance form.
- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Probability/Variance.html —
  Mathlib's variance and Chebyshev API.

### Mathlib
- `MeasureTheory.MeasureSpace` / `IsProbabilityMeasure` — probability space and
  total-mass-one setting.
- `MeasureTheory.integral` — expectation $\mathbb{E}[Z] = \int Z \, d\mu$.
- `MeasureTheory.MemLp` / `MeasureTheory.Lp` — the $L^2$ hypothesis and
  integrability bookkeeping.
- `ProbabilityTheory.variance`, `ProbabilityTheory.evariance` — variance form.
- `ProbabilityTheory.meas_ge_le_variance_div_sq` — Chebyshev's inequality
  (the complementary upper/deviation bound).
- `MeasureTheory.integral_mul_le_Lp_mul_Lq` (Hölder, $p=q=2$) and
  `inner_mul_le_norm_mul_norm` ($L^2$ Cauchy-Schwarz) — the analytic core step.
- `ENNReal` / `ENNReal.toReal` — measure-to-real conversions for the probability
  of the level set.

## Metadata

```yaml
tags:
  - probability
  - measure-theory
  - second-moment-method
  - paley-zygmund
  - mathlib-contribution
related_proofs:
  - prob-method-second-moment-oq-01
  - prob-method-second-moment
  - cauchy-schwarz
difficulty: medium
source: gallery-gap
created: 2026-06-30T22:49:26-07:00
```
