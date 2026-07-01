# Problem: Iterated L'Hôpital via the n-th Taylor Coefficient

**Slug**: lhopital-oq-04-oq-01
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let `f, g : ℝ → ℝ` be `n`-times (continuously) differentiable at a point `a`, with

- `f^(k)(a) = 0` for all `k < n`,
- `g^(k)(a) = 0` for all `k < n`,
- `g^(n)(a) ≠ 0`.

Then

$$\lim_{x \to a} \frac{f(x)}{g(x)} \;=\; \frac{f^{(n)}(a)}{g^{(n)}(a)}.$$

The intended route is the **leading-order (n-th) Taylor coefficient limit**:

$$\lim_{x \to a} \frac{f(x)}{(x-a)^n} \;=\; \frac{f^{(n)}(a)}{n!},$$

which follows from Taylor's theorem with remainder (the remainder is `o((x-a)^n)`, and
under the vanishing hypotheses the Taylor polynomial collapses to its single top term
`f^(n)(a)/n! · (x-a)^n`). Dividing the numerator and denominator limits gives

$$\frac{f(x)}{g(x)} = \frac{f(x)/(x-a)^n}{g(x)/(x-a)^n} \;\longrightarrow\; \frac{f^{(n)}(a)/n!}{g^{(n)}(a)/n!} = \frac{f^{(n)}(a)}{g^{(n)}(a)}.$$

This generalizes the parent entry's order-1 result (`lhopital_zero_taylor`, the `n = 1`
case) to arbitrary order `n`.

### Plain Language

The parent gallery entry proves the simplest L'Hôpital case: if `f(a) = g(a) = 0`, then
`f(x)/g(x) → f'(a)/g'(a)`, because near `a` both functions look like their linear Taylor
terms. But what if the first derivatives also vanish — for example `(1 - cos x)/x²`, where
numerator and denominator both vanish to second order? Then you would ordinarily apply
L'Hôpital repeatedly. This problem asks for the Taylor-series explanation of that iterated
procedure: if `f` and `g` both vanish together with all their derivatives up to order
`n - 1`, then the ratio is governed by the first surviving Taylor coefficients, and the
limit is exactly `f^(n)(a)/g^(n)(a)`. The mechanism is that near `a` each function behaves
like `(coefficient) · (x-a)^n`, so the shared `(x-a)^n` factor cancels and only the
coefficients remain.

### Why This Matters

- It closes the loop on the parent entry's stated open question (OQ-04 → iterated case),
  giving a single clean statement in place of an inductive chain of single-step L'Hôpital
  applications.
- It makes explicit the deepest content of L'Hôpital's rule: the limit of an indeterminate
  `0/0` form is a ratio of Taylor coefficients, not an artifact of the Mean Value Theorem.
- The auxiliary lemma `f(x)/(x-a)^n → f^(n)(a)/n!` is independently reusable: it is the
  extraction of the `n`-th Taylor coefficient as a limit, useful in asymptotics and
  singularity analysis.

## Known Results

### What's Already Proven

- **Parent entry (`lhopital-oq-04`)**: the order-1 case. `tendsto_div_sub_of_hasDerivAt`
  gives `f(x)/(x-a) → f'(a)` when `f a = 0`, and `lhopital_zero_taylor` divides the two
  leading-order limits to get `f(x)/g(x) → f'(a)/g'(a)`, with **no** Mean Value Theorem
  and zero axioms. This is precisely `n = 1` of the present problem.
- **Mathlib Taylor infrastructure** (`Mathlib.Analysis.Calculus.Taylor`), verified names:
  - `taylorWithinEval f n s x₀ x` — the degree-`n` Taylor polynomial of `f` on set `s`,
    based at `x₀`, evaluated at `x`; equals
    `∑_{k=0}^{n} (iteratedDerivWithin k f s x₀ / k!) · (x - x₀)^k`.
  - `taylor_isLittleO` — `(fun x ↦ f x - taylorWithinEval f n s x₀ x) =o[𝓝[s] x₀] fun x ↦ (x - x₀)^n`,
    under `Convex ℝ s`, `x₀ ∈ s`, `ContDiffOn ℝ n f s`. **The key input.**
  - `Real.taylor_tendsto` — the same fact packaged as a limit:
    `Tendsto (fun x ↦ (f x - taylorWithinEval f n s x₀ x) / (x - x₀)^n) (𝓝[s] x₀) (𝓝 0)`.
  - `taylor_mean_remainder_lagrange`, `taylor_mean_remainder_lagrange_iteratedDeriv` —
    Lagrange remainder forms (an alternative route with an explicit intermediate point).
  - `taylor_within_apply` — the explicit sum expansion of `taylorWithinEval`, useful for
    collapsing the polynomial to its top term under the vanishing hypotheses.
- `HasDerivAt.tendsto_slope`, `Filter.Tendsto.div`, `div_div_div_cancel_right₀` — the
  limit-arithmetic / cancellation toolkit already used by the parent.

### What's Still Open

- No gallery entry (and, as far as we can tell, no single packaged Mathlib lemma) states
  the iterated `0/0` L'Hôpital result as a ratio of `n`-th Taylor coefficients. Mathlib has
  `HasDerivAt.lhopital_zero_*` (single-step, MVT-based) and the Taylor remainder theorems,
  but not the composite statement of this problem.
- The clean coefficient-extraction limit `f(x)/(x-a)^n → f^(n)(a)/n!` is not, to our
  knowledge, a named Mathlib lemma; it must be derived from `taylor_isLittleO` /
  `Real.taylor_tendsto` by collapsing the Taylor polynomial.

### Our Goal

Formalize, with zero axioms and no `native_decide`:

1. `tendsto_div_pow_of_iteratedDeriv` (name tentative): under the vanishing hypotheses
   `f^(k)(a) = 0` for `k < n` and suitable smoothness, `f(x)/(x-a)^n → f^(n)(a)/n!`.
2. `lhopital_zero_taylor_iterated` (name tentative): the ratio result
   `f(x)/g(x) → f^(n)(a)/g^(n)(a)`, by dividing the two coefficient limits.
3. At least one worked example, e.g. `(1 - cos x)/x² → 1/2` (`n = 2`), instantiating the
   rule with a genuinely second-order vanishing.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `lhopital-oq-04` (parent) | The `n = 1` case; supplies the divide-the-leading-limits template and `tendsto_div_sub_of_hasDerivAt` | `HasDerivAt.tendsto_slope`, `Tendsto.div`, `div_div_div_cancel_right₀`, `Tendsto.congr'` |
| `lhopital` (grandparent) | The MVT-based `0/0` rule this Taylor route deliberately avoids | Cauchy MVT, `HasDerivAt.lhopital_zero_right` |
| Taylor-series / analytic-function entries (if present) | Provide `ContDiff` / analyticity packaging for the smoothness hypotheses | `taylorWithinEval`, `ContDiffOn`, little-o asymptotics |

## Initial Thoughts

### Potential Approaches

1. **(Recommended) Little-o / `Real.taylor_tendsto` route.**
   Take a convex neighborhood `s` of `a` (e.g. `s = Set.univ`, which is convex and contains
   `a`), and `ContDiffOn ℝ n f s`. By `taylor_isLittleO` / `Real.taylor_tendsto`,
   `(f x - taylorWithinEval f n s a x)/(x-a)^n → 0`. Expand `taylorWithinEval` via
   `taylor_within_apply` into `∑_{k=0}^{n} (iteratedDerivWithin k f s a / k!)(x-a)^k`; under
   `f^(k)(a) = 0` for `k < n` all terms with `k < n` vanish and the `k = n` term is
   `(f^(n)(a)/n!)(x-a)^n`. Divide by `(x-a)^n` (nonzero on `𝓝[≠] a`): the polynomial term
   contributes the constant `f^(n)(a)/n!` and the remainder → 0, so
   `f(x)/(x-a)^n → f^(n)(a)/n!`. Then reuse the parent's divide-and-cancel argument with
   `(x-a)^n` in place of `(x-a)`. **This is the OQ's own suggested route and reuses the most
   Mathlib machinery.**

2. **Induction on `n` via repeated single-step L'Hôpital.** Peel one order at a time using
   the parent's `n = 1` lemma on `f(x)/(x-a)` and bookkeeping the derivative hypotheses.
   Rejected as primary: the indeterminate-form bookkeeping across the induction (each step
   changes both functions to their derivatives, and one must re-establish vanishing and
   differentiability) is fiddlier than the direct Taylor route, and it does not directly
   produce the clean "ratio of `n`-th coefficients" statement.

3. **Lagrange remainder route** (`taylor_mean_remainder_lagrange_iteratedDeriv`). Gives an
   explicit intermediate point `x' ∈ (a, x)` with `f(x) = (f^(n)(x')/n!)(x-a)^n` under the
   vanishing hypotheses, then let `x → a` and use continuity of `f^(n)`. Viable and very
   concrete, but requires `n+1`-fold differentiability and is naturally one-sided
   (`x₀ < x`), so a two-sided limit needs gluing both sides. Keep as a fallback.

Recommendation: **Approach 1.** It matches the open question's phrasing, needs only
`ContDiffOn ℝ n`, and gives a two-sided `𝓝[≠] a` statement directly.

### Key Difficulties

- **Collapsing the Taylor polynomial.** Turning `taylorWithinEval f n s a x` into the single
  monomial `(f^(n)(a)/n!)(x-a)^n` requires clean handling of the finite sum
  (`taylor_within_apply` / `Finset.sum`) and rewriting `n-1` vanishing terms. Expect some
  `Finset.sum` and `iteratedDerivWithin`-vs-`iteratedDeriv` friction.
- **`iteratedDerivWithin` vs `iteratedDeriv`.** Mathlib's Taylor lemmas are stated with
  `iteratedDerivWithin _ _ s`. If `s` has nonempty interior around `a` (e.g. `s = univ`),
  `iteratedDerivWithin k f univ = iteratedDeriv k f` (`iteratedDerivWithin_univ`, verify
  exact name); bridging hypotheses stated on `iteratedDeriv` (or on `HasDerivAt`) to the
  `Within` form is a real, if routine, step.
- **The `(x-a)^n` cancellation and nonvanishing.** On `𝓝[≠] a`, `x - a ≠ 0` so `(x-a)^n ≠ 0`
  (`pow_ne_zero`); the parent's `div_div_div_cancel_right₀` generalizes with `c = (x-a)^n`.
  The `g^(n)(a) ≠ 0` hypothesis is what makes `Tendsto.div` applicable (nonzero denominator
  limit).
- **Filter mismatch `𝓝[s] a` vs `𝓝[≠] a`.** `Real.taylor_tendsto` gives the limit along
  `𝓝[s] a`. With `s = univ` this is `𝓝 a`; restricting to `𝓝[≠] a` is a filter-refinement
  (`Tendsto.mono_left`) since `𝓝[≠] a ≤ 𝓝[univ] a = 𝓝 a`.
- **Smoothness hypothesis choice.** `ContDiffOn ℝ n f s` (or `ContDiff ℝ n f`) is the cleanest
  hypothesis for Approach 1. Deciding whether to state the theorem with `ContDiff`,
  `ContDiffOn`, or a bundle of `iteratedDeriv` / `HasDerivAt` facts affects downstream
  ergonomics.

### What Would a Proof Need?

- A lemma reducing `taylorWithinEval f n s a x` to `(f^(n)(a)/n!)(x-a)^n` given the vanishing
  of lower coefficients.
- The coefficient-extraction limit `f(x)/(x-a)^n → f^(n)(a)/n!` (the heart of the problem).
- Reuse of the parent's divide/cancel pattern with `(x-a)^n`, plus `Tendsto.div` using
  `g^(n)(a)/n! ≠ 0` (equivalently `g^(n)(a) ≠ 0`).
- One `n = 2` worked example to validate the statement end-to-end.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- All heavy analytic content is already in Mathlib: Taylor's theorem with remainder is
  packaged as `taylor_isLittleO` / `Real.taylor_tendsto`, and the parent entry supplies the
  exact divide-and-cancel template for the ratio step.
- The genuine work is (a) collapsing the finite Taylor polynomial to its top monomial under
  the vanishing hypotheses, (b) navigating `iteratedDerivWithin`-vs-`iteratedDeriv` and the
  `𝓝[s]`-vs-`𝓝[≠]` filter bookkeeping, and (c) generalizing the cancellation from `(x-a)`
  to `(x-a)^n`. None deep, but the `Finset.sum` collapse and `Within`-derivative bridging
  consume iterations.
- Not low (materially more than restating a Mathlib lemma), not high (no new mathematics,
  strong parent scaffolding).

**Estimated Effort**:
- Exploration: a few hours to pin the Taylor-polynomial collapse lemma and filter plumbing.
- If tractable: one focused session, ~120–220 lines.
- If hard: the `Finset.sum` collapse or the `Within`-derivative bridging balloons; fall back
  to the Lagrange-remainder route (Approach 3).

## References

### Papers
- Rudin, W. *Principles of Mathematical Analysis*, 3rd ed. (1976) — Taylor's theorem
  (Thm 5.15) and L'Hôpital's rule (Thm 5.13); the standard link between the `0/0` form and
  Taylor coefficients.
- Apostol, T. *Mathematical Analysis* — Taylor's formula with remainder; iterated
  indeterminate forms.

### Online Resources
- Wikipedia: "L'Hôpital's rule" (higher-order / iterated form) and "Taylor's theorem"
  (Peano and Lagrange remainder).

### Mathlib
- `Mathlib.Analysis.Calculus.Taylor` — `taylorWithinEval`, `taylor_within_apply`,
  `taylor_isLittleO` and `Real.taylor_tendsto` (Peano remainder; **primary tools**),
  `taylor_mean_remainder_lagrange`, `taylor_mean_remainder_lagrange_iteratedDeriv`
  (Lagrange remainder; fallback route).
- `Mathlib.Analysis.Calculus.IteratedDeriv.*` — `iteratedDeriv`, `iteratedDerivWithin`,
  `iteratedDerivWithin_univ` (verify exact name) — bridging `Within` and global derivatives.
- `Mathlib.Analysis.Calculus.ContDiff.*` — `ContDiff` / `ContDiffOn` smoothness hypotheses.
- Limit arithmetic / cancellation: `Filter.Tendsto`, `Filter.Tendsto.div`,
  `Filter.Tendsto.mono_left`, `Filter.Tendsto.congr'`, `div_div_div_cancel_right₀`,
  `sub_ne_zero`, `pow_ne_zero` (all used by, or adjacent to, the parent proof).

## Metadata

```yaml
tags:
  - analysis
  - calculus
  - lhopital
  - taylor-series
related_proofs:
  - lhopital-oq-04
difficulty: medium
source: gallery-gap
created: 2026-06-30
```
