/-
  binomial-theorem-oq-01-oq-01-oq-02:
  "Absorption identity as term-by-term differentiation of the binomial
   HasFPowerSeriesOnBall."
  ====================================================

  Verified: all theorems compile against Mathlib (lean v4.26.0) and depend only
  on the foundational axioms `propext`, `Classical.choice`, `Quot.sound`
  (0 sorries, 0 `axiom` declarations, no `native_decide`).

  The parent gallery proof `binomial-theorem-oq-01-oq-01`
  (proofs/Proofs/BinomialTheoremOQ01OQ01.lean) already provides:
    * `genBinom α k = (∏ j ∈ range k, (α - j)) / k!`   (the coefficient C(α,k))
    * `absorption : α * genBinom (α-1) k = (k+1) * genBinom α (k+1)`
        — the COEFFICIENT-LEVEL identity.
    * `binomial_series_analytic :
         HasFPowerSeriesOnBall (fun y => (1+y)^α) (binomialSeries ℝ α) 0 1`
        — the analytic framework (Real.one_add_rpow_hasFPowerSeriesOnBall_zero).

  This OQ asks for the ANALYTIC side: that d/dx (1+x)^α = α(1+x)^(α-1), and that
  this is exactly the absorption identity read off coefficient-by-coefficient.

  Key Mathlib lemma (verified to exist, Pow/Deriv.lean:668):
    HasDerivAt.rpow_const (hf : HasDerivAt f f' x) (hx : f x ≠ 0 ∨ 1 ≤ p) :
        HasDerivAt (fun y => f y ^ p) (f' * p * f x ^ (p - 1)) x
-/
import Mathlib
import Proofs.BinomialTheoremOQ01OQ01

open Real

namespace BinomialTheoremOQ01OQ01OQ02

/-- **The binomial derivative (pointwise).** `d/dx (1+x)^α = α·(1+x)^(α-1)` for
`x > -1`. Proof: `(fun y => 1+y)` has derivative `1` everywhere; `1+x ≠ 0` from
`-1 < x`; apply `HasDerivAt.rpow_const` and simplify `1 * α * _`. -/
theorem hasDerivAt_one_add_rpow (α x : ℝ) (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => (1 + y) ^ α) (α * (1 + x) ^ (α - 1)) x := by
  have hpos : (0:ℝ) < 1 + x := by linarith
  have h1x : (1 + x) ≠ 0 := ne_of_gt hpos
  have hbase : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
  have h := hbase.rpow_const (p := α) (Or.inl h1x)
  simpa using h

/-- **Coefficient match (the absorption identity as the derivative coefficient).**
The coefficient of `x^k` in `d/dx Σ C(α,j) x^j` is `(k+1)·C(α,k+1)`, while the
coefficient of `x^k` in `α·(1+x)^(α-1) = α Σ C(α-1,j) x^j` is `α·C(α-1,k)`. The
parent's `absorption` says these agree. This restates it in the suggestive form
`coeff of derivative = α · C(α-1,k)`. -/
theorem deriv_coeff_eq_absorption (α : ℝ) (k : ℕ) :
    (↑k + 1 : ℝ) * BinomialTheoremOQ01OQ01.genBinom α (k + 1)
      = α * BinomialTheoremOQ01OQ01.genBinom (α - 1) k :=
  (BinomialTheoremOQ01OQ01.absorption α k).symm

/-- **Derivative value at 0 from the linear coefficient.** `d/dx (1+x)^α |₀ = α`,
matching `genBinom α 1 = α`. Sanity link between the analytic derivative and the
k=0 case of the absorption identity. -/
theorem hasDerivAt_one_add_rpow_zero (α : ℝ) :
    HasDerivAt (fun y : ℝ => (1 + y) ^ α) α 0 := by
  have h := hasDerivAt_one_add_rpow α 0 (by norm_num)
  simpa using h

/-- **The pointwise derivative as a `deriv`.** `deriv (fun x => (1+x)^α) x = α(1+x)^(α-1)`
for `x > -1`. The `deriv`-level restatement of `hasDerivAt_one_add_rpow`. -/
theorem deriv_one_add_rpow (α x : ℝ) (hx : -1 < x) :
    deriv (fun y : ℝ => (1 + y) ^ α) x = α * (1 + x) ^ (α - 1) :=
  (hasDerivAt_one_add_rpow α x hx).deriv

/-- **Term-by-term differentiation of the binomial power series (the headline).**
Differentiating the `HasFPowerSeriesOnBall` representation of `(1+x)^α` term by term
yields the formal `derivSeries` of the binomial series, and that series represents the
Fréchet derivative `fderiv ℝ (fun y => (1+y)^α)` on the *same* unit ball. This is the
power-series form of `d/dx Σ C(α,k) x^k = Σ (k+1) C(α,k+1) x^k`. Combined with the
parent's `absorption` identity `(k+1)·C(α,k+1) = α·C(α-1,k)`, the differentiated series
is `α Σ C(α-1,k) x^k = α(1+x)^(α-1)` — exactly the analytic content of the absorption
identity. Proof: apply `HasFPowerSeriesOnBall.fderiv` to the parent's
`binomial_series_analytic`. -/
theorem binomial_derivSeries_analytic (α : ℝ) :
    HasFPowerSeriesOnBall (fderiv ℝ (fun y : ℝ => (1 + y) ^ α))
      (binomialSeries ℝ α).derivSeries 0 1 :=
  (BinomialTheoremOQ01OQ01.binomial_series_analytic α).fderiv

/-- **The two derivatives agree.** The Fréchet derivative obtained from term-by-term
differentiation of the binomial series, evaluated at the tangent vector `1`, recovers
the pointwise derivative `α(1+x)^(α-1)` for `x > -1`. This closes the loop between
`binomial_derivSeries_analytic` (the series side) and `hasDerivAt_one_add_rpow` (the
closed-form side). -/
theorem fderiv_one_add_rpow_apply_one (α x : ℝ) (hx : -1 < x) :
    fderiv ℝ (fun y : ℝ => (1 + y) ^ α) x 1 = α * (1 + x) ^ (α - 1) := by
  rw [fderiv_deriv]
  exact deriv_one_add_rpow α x hx

end BinomialTheoremOQ01OQ01OQ02
