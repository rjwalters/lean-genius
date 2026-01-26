/-!
# Erdős Problem #50 — Singularity of the Totient Distribution Function

Schoenberg proved that for every c ∈ [0,1], the natural density of
{ n ∈ ℕ : φ(n)/n < c } exists. Denoting this density by f(c), Erdős
showed that f is purely singular (continuous but with derivative 0
almost everywhere).

**Question ($250):** Is it true that there is no x such that f'(x) exists
and is positive? That is, does f have zero derivative wherever it exists?

## Background

The Euler totient function φ(n) counts integers up to n coprime to n.
The ratio φ(n)/n = ∏_{p | n} (1 − 1/p) depends only on the prime
factors of n. Schoenberg's theorem establishes that the distribution
function f(c) = d({ n : φ(n)/n < c }) is well-defined.

Erdős proved f is purely singular, meaning its derivative vanishes
almost everywhere with respect to Lebesgue measure. The prize question
asks the stronger statement: f'(x) > 0 for *no* x at all.

## Status: OPEN ($250 prize)

*Reference:* [erdosproblems.com/50](https://www.erdosproblems.com/50)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Totient
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Filter Finset

/-! ## Core Definitions -/

/-- The set of natural numbers where φ(n)/n < c. -/
def totientRatioBelow (c : ℝ) : Set ℕ :=
  { n | 0 < n ∧ (n.totient : ℝ) / (n : ℝ) < c }

/-- Asymptotic natural density of a set of naturals. -/
noncomputable def naturalDensity (S : Set ℕ) : ℝ :=
  Filter.liminf (fun N =>
    (Finset.card (Finset.filter (· ∈ S) (Finset.range (N + 1))) : ℝ)
    / (↑(N + 1) : ℝ)) atTop

/-- **Schoenberg's distribution function.**
f(c) = natural density of { n : φ(n)/n < c } for c ∈ [0,1].
Schoenberg proved this density exists for all c. -/
noncomputable def schoenbergF (c : ℝ) : ℝ :=
  naturalDensity (totientRatioBelow c)

/-! ## Schoenberg's Theorem -/

/-- **Schoenberg's Theorem.** For every c ∈ [0,1], the natural density
of { n : φ(n)/n < c } exists (i.e., the liminf equals the limsup). -/
axiom schoenberg_density_exists (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
  ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ schoenbergF c = d

/-- f is non-decreasing. -/
axiom schoenbergF_mono (c₁ c₂ : ℝ) (h : c₁ ≤ c₂) :
  schoenbergF c₁ ≤ schoenbergF c₂

/-- f(0) = 0 and f(1) = 1. -/
axiom schoenbergF_boundary : schoenbergF 0 = 0 ∧ schoenbergF 1 = 1

/-- f is continuous. -/
axiom schoenbergF_continuous : Continuous schoenbergF

/-! ## Erdős's Result: Pure Singularity -/

/-- **Erdős's Theorem.** The distribution function f is purely singular:
it is continuous but f'(x) = 0 for Lebesgue-almost every x ∈ [0,1].
This means f increases only on a set of measure zero. -/
axiom erdos_purely_singular :
  ∀ᵐ (x : ℝ) ∂MeasureTheory.MeasureSpace.volume,
    x ∈ Set.Icc 0 1 →
    HasDerivAt schoenbergF 0 x

/-! ## Main Conjecture ($250) -/

/-- **Erdős Problem #50 ($250 prize).**
Is it true that f'(x) does not exist and equal a positive value
for any x? That is, wherever f is differentiable, the derivative
is zero (or does not exist). -/
axiom erdos_50_conjecture :
  ¬ ∃ x : ℝ, ∃ d : ℝ, 0 < d ∧ HasDerivAt schoenbergF d x

/-! ## Properties of φ(n)/n -/

/-- φ(n)/n = ∏_{p | n} (1 − 1/p): the ratio depends only on the
set of prime factors of n. -/
axiom totient_ratio_product (n : ℕ) (hn : 0 < n) :
  (n.totient : ℝ) / n = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))

/-- The infimum of φ(n)/n over all n > 0 is 0. In particular,
liminf_{n→∞} φ(n)/n = 0 (achieved along primorials). -/
axiom totient_ratio_inf :
  Filter.liminf (fun n => (n.totient : ℝ) / (n : ℝ)) atTop = 0

/-- The supremum of φ(n)/n for n > 1 is strictly less than 1
(only φ(1)/1 = 1; for n > 1, φ(n)/n < 1). -/
axiom totient_ratio_lt_one (n : ℕ) (hn : 1 < n) :
  (n.totient : ℝ) / n < 1
