/-
# Multinomial Marginal Central Limit Theorem (Phase-2 scaffold)

**Open Question** (binomial-theorem-oq-02-oq-01-oq-01-oq-03):
"Multinomial marginal CLT in Lean: does (Xᵢ - npᵢ) / √(npᵢ(1-pᵢ)) converge in
distribution to N(0,1) for each coordinate as n → ∞?"

## Status

**Phase-2 STATEMENT scaffold.** This file STATES the multinomial marginal CLT
and reduces it to the classical de Moivre–Laplace (binomial) CLT plus the
already-proved marginal-PMF identity from `BinomialTheoremOQ02OQ01OQ02`.

The de Moivre–Laplace CLT is taken as an axiom: a measure-theoretic proof from
Mathlib's `ProbabilityTheory.iid_central_limit_theorem` is non-trivial (CDF
↔ measure-weak-convergence bridge) and is left for a Phase-3 effort.

## What This File Provides

1. `binomialCDF n p x` — concrete CDF of Binomial(n, p), defined as
   ∑_{j ≤ x} C(n,j) p^j (1-p)^(n-j).
2. `multinomialMarginalCDF s p n i₀ x` — concrete CDF of the marginal X_{i₀}
   of Multinomial(n, p), defined by summing `multinomialProb` over the
   filtered piAntidiag.
3. `standardNormalCDF` — opaque marker for the standard normal CDF.
4. `binomial_clt_pointwise` — AXIOM: pointwise convergence of standardized
   binomial CDF to standardNormalCDF.
5. `multinomialMarginalCDF_eq_binomialCDF` — reduction lemma. The marginal
   CDF of the multinomial equals the binomial CDF with parameter p(i₀).
   Provable from `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf` by
   regrouping the sum over k into fibers over k(i₀); the reduction is
   recorded as a sorry-marked lemma (Phase-3 target).
6. `multinomial_marginal_clt` — DERIVED THEOREM (no axiom of its own).
   Combines (4) and (5) via `Filter.Tendsto.congr`.

## Mathematical Content

For (X₁, ..., Xₖ) ~ Multinomial(n, p₁, ..., pₖ), each marginal Xᵢ ~ Binomial(n, pᵢ)
(this was proved in `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`).
The classical de Moivre–Laplace theorem gives:

    P( (X − np) / √(np(1−p)) ≤ x )  →  Φ(x)    as n → ∞

for any x ∈ ℝ, where Φ is the standard normal CDF. Composing these two facts
gives the multinomial marginal CLT.

## Honest Reporting

- Sorries: 1 (the cdf-equality reduction, provable from existing lemmas).
- Axioms: 2 (`binomial_clt_pointwise` + `standardNormalCDF` opaque).
- Status: axiomatized — not "verified".

The contribution of this file is the *statement and reduction structure*, not
the CLT itself.

## Why CDF formulation

Mathlib's CLT (`ProbabilityTheory.iid_central_limit_theorem`) is stated in
terms of measure-weak-convergence of the law of standardized sums to the
Gaussian measure. Our statement is in CDF form to (a) avoid the heavy
measure-theory setup for a marginal-only result, (b) match the classical
"de Moivre–Laplace" presentation, and (c) keep the reduction to the
already-proved marginal-PMF identity transparent.

## Dependencies

- `BinomialTheoremOQ02OQ01OQ02` — `multinomialProb`, `multinomial_marginal_pmf`
- Mathlib — `Real.sqrt`, `Filter.Tendsto`, `nhds`
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ02

namespace BinomialTheoremOQ02OQ01OQ01OQ03

open Finset BigOperators

/-! ## CDF definitions -/

/-- The CDF of Binomial(n, p) at `x`:
    `binomialCDF n p x = ∑_{j ≤ x, 0 ≤ j ≤ n} C(n, j) · p^j · (1 - p)^(n - j)`.

    No constraints on `p` are enforced at the definition level; the axiom
    `binomial_clt_pointwise` requires `0 < p < 1`. -/
noncomputable def binomialCDF (n : ℕ) (p : ℝ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    if (j : ℝ) ≤ x then
      (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j)
    else 0

/-- The marginal CDF of coordinate `i₀` for X ~ Multinomial(n, p). -/
noncomputable def multinomialMarginalCDF
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (i₀ : α) (x : ℝ) : ℝ :=
  ∑ k ∈ s.piAntidiag n,
    if ((k i₀ : ℕ) : ℝ) ≤ x then
      BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
    else 0

/-! ## Standard normal CDF (opaque) -/

/-- The standard normal CDF, `Φ(x) = (1/√(2π)) ∫_{-∞}^x e^{-t²/2} dt`.

    Declared `opaque` here — Mathlib provides a measure-theoretic standard
    normal (`Mathlib.Probability.Distributions.Gaussian.Basic`); bridging
    that measure to a CDF function is left for a Phase-3 effort. -/
opaque standardNormalCDF : ℝ → ℝ

/-! ## Axiom: classical de Moivre–Laplace (binomial CLT) -/

/-- **AXIOM** (de Moivre–Laplace, 1733/1812): the standardized binomial CDF
    converges pointwise to the standard normal CDF as `n → ∞`.

    For `0 < p < 1` and any `x : ℝ`,
    `binomialCDF n p (np + x √(np(1−p)))  →  Φ(x)`.

    Mathematical justification: classical, see e.g. Feller, *Introduction to
    Probability Theory*, Vol. I (1968), Ch. VII §3. The Mathlib path is via
    `ProbabilityTheory.iid_central_limit_theorem` plus a CDF-bridge; recorded
    as an axiom here (Phase-3 target). -/
axiom binomial_clt_pointwise
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        binomialCDF n p ((n : ℝ) * p + x * Real.sqrt ((n : ℝ) * p * (1 - p))))
      Filter.atTop (nhds (standardNormalCDF x))

/-! ## Reduction lemma -/

/-- **Reduction lemma**: the marginal CDF of the multinomial equals the
    binomial CDF with parameter `p(i₀)`.

    Proof sketch (Phase-3): regroup `∑ k ∈ s.piAntidiag n` into fibers over
    the value `j = k i₀` for `j ∈ {0, ..., n}`; on each fiber, apply
    `BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf` to collapse the
    inner sum to `C(n, j) · p(i₀)^j · (1 − p(i₀))^(n − j)`. The if-condition
    `(k i₀ : ℝ) ≤ x` becomes `(j : ℝ) ≤ x`, which factors out of the inner
    sum since `j` is fixed on each fiber. -/
theorem multinomialMarginalCDF_eq_binomialCDF
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (x : ℝ) :
    multinomialMarginalCDF s p n i₀ x = binomialCDF n (p i₀) x := by
  sorry

/-! ## Main theorem: multinomial marginal CLT (derived) -/

/-- **Multinomial marginal CLT** (DERIVED THEOREM, no separate axiom):
    for X ~ Multinomial(n, p), each non-degenerate marginal `Xᵢ` has the
    standardized CDF converging pointwise to `Φ(x)`.

    Proof: combine the de Moivre–Laplace axiom (`binomial_clt_pointwise`)
    with the reduction lemma (`multinomialMarginalCDF_eq_binomialCDF`)
    via `Filter.Tendsto.congr`. -/
theorem multinomial_marginal_clt
    {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (hp0 : 0 < p i₀) (hp1 : p i₀ < 1) (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        multinomialMarginalCDF s p n i₀
          ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))))
      Filter.atTop (nhds (standardNormalCDF x)) := by
  have key : ∀ n : ℕ,
      multinomialMarginalCDF s p n i₀
        ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))) =
      binomialCDF n (p i₀)
        ((n : ℝ) * p i₀ + x * Real.sqrt ((n : ℝ) * p i₀ * (1 - p i₀))) := by
    intro n
    exact multinomialMarginalCDF_eq_binomialCDF s p n hp i₀ hi₀ _
  exact (binomial_clt_pointwise (p i₀) hp0 hp1 x).congr (fun n => (key n).symm)

end BinomialTheoremOQ02OQ01OQ01OQ03
