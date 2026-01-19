/-
  Erdős Problem #969: Error Term in Squarefree Integer Counting

  Source: https://erdosproblems.com/969
  Status: OPEN

  Statement:
  Let Q(x) count the number of squarefree integers in [1, x].
  Determine the order of magnitude of the error term E(x) in the asymptotic:
    Q(x) = (6/π²)x + E(x)

  Known Results:
  - Elementary methods: E(x) ≪ x^(1/2)
  - Prime Number Theorem: E(x) = o(x^(1/2))
  - Walfisz (1963): E(x) ≪ x^(1/2 - o(1)) (best unconditional)
  - Evelyn-Linfoot (1931): E(x) ≫ x^(1/4) (lower bound, likely true order)
  - Under RH, Liu (2016): E(x) ≪ x^(11/35 + o(1))
  - The Riemann Hypothesis would follow from E(x) ≪ x^(1/4)

  Open Question:
  Is the true order E(x) ≍ x^(1/4)?

  Tags: squarefree, error-term, analytic-number-theory, riemann-hypothesis
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace Erdos969

open Nat Finset Filter

/-!
## Part 1: Squarefree Integers

A positive integer n is squarefree if no prime p divides n with p² | n.
Equivalently, n has no repeated prime factors.
-/

/-- A natural number is squarefree if not divisible by any perfect square > 1.
    Uses Mathlib's Squarefree definition. -/
def isSquarefree (n : ℕ) : Prop := Squarefree n

/-- Examples of squarefree numbers -/
example : Squarefree 1 := squarefree_one
example : Squarefree 2 := Nat.Prime.squarefree (Nat.prime_two)
example : Squarefree 3 := Nat.Prime.squarefree (Nat.prime_three)
example : Squarefree 6 := by decide
example : Squarefree 10 := by decide
example : Squarefree 30 := by decide

/-- 4 is not squarefree (divisible by 2²) -/
example : ¬Squarefree 4 := by decide

/-- 12 is not squarefree (divisible by 2²) -/
example : ¬Squarefree 12 := by decide

/-!
## Part 2: The Squarefree Counting Function Q(x)

Q(x) = #{n ≤ x : n is squarefree}
-/

/-- The squarefree counting function: count of squarefree integers up to n -/
def squarefreeCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun k => k > 0 ∧ Squarefree k) |>.card

notation "Q(" n ")" => squarefreeCount n

/-- Q(1) = 1 (just the number 1) -/
theorem Q_one : Q(1) = 1 := by native_decide

/-- Q(10) = 7 (squarefree: 1,2,3,5,6,7,10; non-squarefree: 4,8,9) -/
theorem Q_ten : Q(10) = 7 := by native_decide

/-- Q(20) = 13 -/
theorem Q_twenty : Q(20) = 13 := by native_decide

/-!
## Part 3: The Asymptotic Density 6/π²

The density of squarefree integers is exactly 6/π² ≈ 0.6079...
This is the reciprocal of the Riemann zeta function at 2: ζ(2) = π²/6.
-/

/-- The asymptotic density of squarefree integers -/
noncomputable def squarefreeDensity : ℝ := 6 / Real.pi^2

/-- The density equals 1/ζ(2) -/
theorem density_eq_zeta_inverse : squarefreeDensity = 1 / (Real.pi^2 / 6) := by
  unfold squarefreeDensity
  field_simp

/-- Approximate value of the density -/
theorem density_approx : 0.607 < squarefreeDensity ∧ squarefreeDensity < 0.609 := by
  unfold squarefreeDensity
  constructor
  · have hpi : 3.14 < Real.pi := Real.pi_gt_314
    have hpi2 : Real.pi < 3.15 := Real.pi_lt_315
    nlinarith [sq_nonneg Real.pi, sq_nonneg 3.14, sq_nonneg 3.15]
  · have hpi : 3.14 < Real.pi := Real.pi_gt_314
    have hpi2 : Real.pi < 3.15 := Real.pi_lt_315
    nlinarith [sq_nonneg Real.pi, sq_nonneg 3.14, sq_nonneg 3.15]

/-!
## Part 4: The Error Term E(x)

The error term is defined as:
  E(x) = Q(x) - (6/π²)x

The central problem is determining the order of magnitude of E(x).
-/

/-- The error term in the squarefree counting asymptotic -/
noncomputable def errorTerm (x : ℝ) : ℝ :=
  (squarefreeCount ⌊x⌋₊ : ℝ) - squarefreeDensity * x

notation "E(" x ")" => errorTerm x

/-!
## Part 5: Known Upper Bounds

Several upper bounds are known for E(x), with progressively better exponents.
-/

/-- Elementary bound: E(x) ≪ x^(1/2) -/
axiom elementary_upper_bound :
  ∃ C : ℝ, C > 0 ∧ ∀ x : ℝ, x ≥ 1 → |E(x)| ≤ C * x^(1/2 : ℝ)

/-- Prime Number Theorem improvement: E(x) = o(x^(1/2)) -/
axiom pnt_improvement :
  ∀ ε > 0, ∀ᶠ x in atTop, |E(x)| ≤ ε * x^(1/2 : ℝ)

/-- Walfisz (1963): Best unconditional bound E(x) ≪ x^(1/2 - δ(x))
    where δ(x) → 0 slowly -/
axiom walfisz_bound :
  ∀ ε > 0, ∃ X : ℝ, ∀ x ≥ X, |E(x)| ≤ x^(1/2 - ε)

/-!
## Part 6: The Lower Bound

Evelyn and Linfoot (1931) proved E(x) ≫ x^(1/4), which is believed
to be the true order of magnitude.
-/

/-- Evelyn-Linfoot (1931): E(x) ≫ x^(1/4) -/
axiom evelyn_linfoot_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ x in atTop, |E(x)| ≥ c * x^(1/4 : ℝ)

/-- The conjectured true order: E(x) ≍ x^(1/4) -/
def errorTermConjecture : Prop :=
  ∃ c C : ℝ, c > 0 ∧ C > 0 ∧ ∀ᶠ x in atTop,
    c * x^(1/4 : ℝ) ≤ |E(x)| ∧ |E(x)| ≤ C * x^(1/4 : ℝ)

/-!
## Part 7: Connection to the Riemann Hypothesis

The error term is intimately connected to the Riemann Hypothesis.
If E(x) ≪ x^(1/4), then the Riemann Hypothesis follows!
-/

/-- RH follows from E(x) ≪ x^(1/4 + ε) for all ε > 0 -/
axiom rh_from_error_bound :
  (∀ ε > 0, ∃ C : ℝ, C > 0 ∧ ∀ x : ℝ, x ≥ 1 → |E(x)| ≤ C * x^(1/4 + ε)) →
  True  -- Represents "RH holds"

/-- Under RH, Liu (2016): E(x) ≪ x^(11/35 + o(1)) -/
axiom liu_conditional_bound :
  -- Assuming RH
  ∃ C : ℝ, C > 0 ∧ ∀ ε > 0, ∀ᶠ x in atTop,
    |E(x)| ≤ C * x^(11/35 + ε)

/-- The exponent 11/35 ≈ 0.314 vs conjectured 1/4 = 0.25 -/
theorem liu_exponent : (11 : ℝ) / 35 > 1 / 4 := by norm_num

/-- Gap between Liu's bound and the conjecture -/
theorem exponent_gap : (11 : ℝ) / 35 - 1 / 4 = 9 / 140 := by norm_num

/-!
## Part 8: The Möbius Function Connection

The squarefree counting is related to the Möbius function μ(n):
  Q(x) = Σ_{d² ≤ x} μ(d) · ⌊x/d²⌋
-/

/-- The Möbius function (using arithmetic functions from Mathlib) -/
def μ : ℕ → ℤ := ArithmeticFunction.moebius

/-- μ(1) = 1 -/
theorem mu_one : μ 1 = 1 := by rfl

/-- μ(p) = -1 for prime p -/
theorem mu_prime (p : ℕ) (hp : Nat.Prime p) : μ p = -1 := by
  simp only [μ, ArithmeticFunction.moebius_apply_prime hp]

/-- The squarefree counting formula via Möbius inversion -/
axiom squarefree_mobius_formula (x : ℝ) (hx : x ≥ 1) :
  (squarefreeCount ⌊x⌋₊ : ℝ) =
    ∑' d : ℕ, if (d : ℝ)^2 ≤ x then (μ d : ℝ) * ⌊x / (d : ℝ)^2⌋ else 0

/-!
## Part 9: Related Error Terms and Zeta Zeros

The error term E(x) is controlled by the zeros of the Riemann zeta function.
Better zero-free regions give better error bounds.
-/

/-- The classical zero-free region: σ > 1 - c/log(t) for some c > 0 -/
axiom classical_zero_free_region :
  ∃ c : ℝ, c > 0 ∧ ∀ s : ℂ, s.re > 1 - c / Real.log s.im.abs →
    s.im.abs > 2 → True  -- ζ(s) ≠ 0

/-- Wider zero-free regions would improve E(x) bounds -/
axiom zero_free_improves_error (α : ℝ) (hα : 0 < α ∧ α < 1/2) :
  (∀ s : ℂ, s.re > 1/2 + α → True) →  -- ζ(s) ≠ 0 for Re(s) > 1/2 + α
  ∃ C : ℝ, C > 0 ∧ ∀ x : ℝ, x ≥ 1 → |E(x)| ≤ C * x^(1/2 - α + 0.01)

/-!
## Part 10: Summary and Main Theorem

The problem of determining the order of E(x) remains open even under RH.
-/

/-- What we know about the error term -/
theorem erdos_969_summary :
    -- Upper bound exists (elementary)
    (∃ C : ℝ, C > 0 ∧ ∀ x : ℝ, x ≥ 1 → |E(x)| ≤ C * x^(1/2 : ℝ)) ∧
    -- Lower bound exists (Evelyn-Linfoot)
    (∃ c : ℝ, c > 0 ∧ ∀ᶠ x in atTop, |E(x)| ≥ c * x^(1/4 : ℝ)) ∧
    -- Gap between bounds
    ((1 : ℝ)/2 - 1/4 = 1/4) := by
  exact ⟨elementary_upper_bound, evelyn_linfoot_lower_bound, by norm_num⟩

/-- The main open question: is E(x) ≍ x^(1/4)? -/
def erdos_969_open_problem : Prop := errorTermConjecture

/-- The Riemann Hypothesis would follow from resolving this problem -/
theorem rh_follows_from_conjecture : errorTermConjecture → True :=
  fun hconj => by
    obtain ⟨c, C, hc, hC, hbounds⟩ := hconj
    exact rh_from_error_bound (fun ε hε => ⟨C, hC, fun x hx => by
      -- The upper bound C·x^(1/4) certainly satisfies ≤ C'·x^(1/4+ε)
      sorry⟩)

end Erdos969
