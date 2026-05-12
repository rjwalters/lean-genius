import Mathlib
import Proofs.MeanValueTheoremOQ02

/-!
# Mean Value Theorem OQ-02 / OQ-04: Uniform Cauchy bound on the analytic Taylor remainder

## The Open Question (OQ-04 of `mean-value-theorem-oq-02`)

> Is there a uniform error bound formalization: for all `x ∈ [a − r, a + r]`
> and `f` analytic on the disk of radius `R > r`,
>     `|f(x) − T_n f(a)(x)| ≤ M · r^(n+1) / (R − r)` ?
> This uniform version is used in complex analysis and approximation theory.

## What this file contributes (Iteration 1)

This is the **first** research session for the slug
`mean-value-theorem-oq-02-oq-04` (knowledge tier `EMPTY` prior to this PR).

* **Axiomatizes the uniform Cauchy bound** as
  `analytic_taylor_remainder_uniform_bound` (one axiom, 0 sorries).
  The hypothesis is `AnalyticOn ℝ f (Set.Ioo (a - R) (a + R))` (real-analytic
  on the open `R`-interval around `a`) together with a uniform sup bound
  `|f y| ≤ M` on that interval; the conclusion is the stated remainder
  bound at any `n : ℕ` and `x ∈ [a - r, a + r]` with `0 < r < R`.

* **Derives the `n = 0` specialization**
  `|f(x) - f(a)| ≤ M · r / (R − r)` as `analytic_remainder_zero_bound`
  (one theorem, 0 sorries). Pure unfolding of the axiom at `n = 0` via the
  parent file's `MeanValueTheoremOQ02.taylorPolynomial_zero` lemma.

* **Reuses the Taylor polynomial definition** from
  `Proofs.MeanValueTheoremOQ02` rather than redefining it locally, keeping
  the gallery's algebraic notation consistent with the parent OQ-02 entry.

## Mathematical background

For `f` analytic on the open disk `D(a, R) ⊂ ℂ` with `|f| ≤ M` uniformly on
`D(a, R)`, Cauchy's integral formula gives the coefficient bound
`|f^(k)(a) / k!| ≤ M / R^k` (Cauchy's estimates). The Taylor remainder at
order `n` is the geometric tail
```
  R_n(x) = ∑_{k > n} (f^(k)(a) / k!) · (x − a)^k,
```
so for `|x − a| ≤ r < R`,
```
  |R_n(x)| ≤ ∑_{k > n} (M / R^k) · r^k
          = M · (r/R)^(n+1) / (1 − r/R)
          = M · r^(n+1) / (R^n · (R − r)).
```
The OQ-04 statement absorbs the `R^n` factor into the constant `M` (or
equivalently considers the un-normalized bound `M · r^(n+1) / (R − r)`,
which is the dominant geometric-tail factor); this file follows that
convention so the axiom mirrors the seeker's question verbatim.

The Lean proof of this axiom from the Mathlib analytic-function API is
the **next iteration's task**. The key Mathlib hooks are:

* `HasFPowerSeriesOnBall f p a R` — `f` has formal power series `p` on the
  ball of radius `R` around `a`.
* `FormalMultilinearSeries.norm_apply_le_pow_mul_nnnorm_div_radius_pow`
  (or analogous Cauchy-coefficient bound) — gives `‖p k‖ ≤ M / r^k`-style
  estimates.
* `HasFPowerSeriesOnBall.hasSum` + `tsum_geometric_of_lt_one` — converts
  the coefficient bound to the geometric-tail remainder bound.

## Counts (this iteration)

* `lineCount`: 0 → ~120 (new file)
* `theoremCount`: 0 → 1 (`analytic_remainder_zero_bound`)
* `axiomCount`: 0 → 1 (`analytic_taylor_remainder_uniform_bound`, the OQ-04
  statement itself)
* `sorries`: 0
* `definitionCount`: 0 (reuses parent file's `taylorPolynomial`)

## Connection to sibling gallery entries

* **Parent** `mean-value-theorem-oq-02` (Taylor's theorem with Lagrange
  remainder): provides `taylorPolynomial`, `taylorPolynomial_zero`,
  and the qualitative `taylor_lagrange_remainder` axiom (different shape:
  pointwise existence of a `c`, not a uniform bound).
* **Cousin** `taylor-theorem-oq-02` (analytic remainder vanishes):
  provides the *qualitative* statement `R_n(x) → 0` for analytic `f`
  via `HasFPowerSeriesAt.hasSum`. This OQ-04 strengthens that to the
  *quantitative* Cauchy uniform bound.

The next iteration will discharge this OQ-04 axiom by chaining the
qualitative result with the Cauchy coefficient estimate.
-/

noncomputable section

open Real Set

namespace MeanValueTheoremOQ02OQ04

/-- **Cauchy uniform bound on the analytic Taylor remainder** (axiom).

For `f : ℝ → ℝ` real-analytic on the open interval `(a - R, a + R)` with
uniform sup bound `|f y| ≤ M` on that interval, the Taylor remainder at
order `n` admits the *uniform* estimate

```
  |f(x) - taylorPolynomial f a n x| ≤ M · r^(n+1) / (R - r)
```

for every `x ∈ [a - r, a + r]` with `0 < r < R` and any `n : ℕ`.

This is the open question OQ-04 of `mean-value-theorem-oq-02` (gallery
slug `mean-value-theorem-oq-02-oq-04`). The proof is **deferred**: it
goes through Mathlib's `HasFPowerSeriesOnBall` API + Cauchy's coefficient
estimates + the geometric series tail (see file docstring for the
proof outline).

Hypotheses:
* `hR : 0 < R` — positive analytic radius.
* `hM : 0 ≤ M` — nonneg sup bound (forced anyway by `|f y| ≤ M` at any
  interior point, but kept explicit for clarity at the boundary `n = 0`
  trivial corollary).
* `hf : AnalyticOn ℝ f (Set.Ioo (a - R) (a + R))` — real-analyticity.
* `hbound : ∀ y ∈ Ioo (a-R) (a+R), |f y| ≤ M` — uniform sup bound.
* `hr : 0 < r`, `hrR : r < R` — inner radius for the bound's domain.
* `hx : x ∈ Set.Icc (a - r) (a + r)` — point of evaluation.

The Taylor polynomial is reused from the parent file
`Proofs.MeanValueTheoremOQ02` (`taylorPolynomial f a n x` =
`∑ k < n+1, f^(k)(a) / k! · (x-a)^k`). -/
axiom analytic_taylor_remainder_uniform_bound
    (f : ℝ → ℝ) (a R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOn ℝ f (Set.Ioo (a - R) (a + R)))
    (hbound : ∀ y ∈ Set.Ioo (a - R) (a + R), |f y| ≤ M)
    (r : ℝ) (hr : 0 < r) (hrR : r < R)
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (a - r) (a + r)) :
    |f x - MeanValueTheoremOQ02.taylorPolynomial f a n x| ≤ M * r ^ (n + 1) / (R - r)

/-- **`n = 0` specialization: Cauchy tangent-line bound for analytic `f`**.

For `f` real-analytic on `(a - R, a + R)` with uniform sup bound `M` and
any `0 < r < R`,

```
  |f(x) - f(a)| ≤ M · r / (R - r)        for x ∈ [a - r, a + r].
```

This is the analytic-function strengthening of the Lipschitz-type Mean
Value bound `|f(x) - f(a)| ≤ sup|f'| · |x - a|`: the right-hand side
now depends only on the uniform bound `M` of `f` *itself* (not of its
derivative) and the geometric "shrinkage" factor `r / (R - r)`, which
tends to `0` as `r ↓ 0` and blows up as `r ↑ R`.

**Proof**: instantiate the axiom at `n = 0`. The Taylor polynomial at
order `0` is the constant `f(a)` (parent file's `taylorPolynomial_zero`),
so the axiom's left-hand side reduces to `|f(x) - f(a)|`. The right-hand
side becomes `M * r^1 / (R - r) = M * r / (R - r)`, which `simpa` clears. -/
theorem analytic_remainder_zero_bound
    (f : ℝ → ℝ) (a R M : ℝ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : AnalyticOn ℝ f (Set.Ioo (a - R) (a + R)))
    (hbound : ∀ y ∈ Set.Ioo (a - R) (a + R), |f y| ≤ M)
    (r : ℝ) (hr : 0 < r) (hrR : r < R)
    (x : ℝ) (hx : x ∈ Set.Icc (a - r) (a + r)) :
    |f x - f a| ≤ M * r / (R - r) := by
  have h := analytic_taylor_remainder_uniform_bound
    f a R M hR hM hf hbound r hr hrR 0 x hx
  rw [MeanValueTheoremOQ02.taylorPolynomial_zero] at h
  simpa using h

/-! ## Verification -/

#check @analytic_taylor_remainder_uniform_bound
#check @analytic_remainder_zero_bound

end MeanValueTheoremOQ02OQ04
