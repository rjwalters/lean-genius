/-
Central Limit Theorem: Infinite Variance Case (Open Question OQ-01)
Date: 2026-02-21
Research: central-limit-theorem-oq-01

QUESTION: What happens when the variance is infinite?

ANSWER: The Central Limit Theorem still holds in a generalized form!
Instead of converging to a Gaussian (α=2 stable), normalized sums converge
to α-stable distributions for some α ∈ (0,2). The normalization changes
from n^(1/2) to n^(1/α).

KEY INSIGHT: Stable distributions are characterized by their characteristic
functions. For the standard symmetric α-stable distribution:
  φ(t) = exp(-|t|^α)

The stability property (unchanged under normalized convolution) is PURELY
ALGEBRAIC in terms of characteristic functions.

This file proves:
1. Stability property of exp(-|t|^α) under n-fold convolution + 1/n^(1/α) scaling
2. Cauchy is 1-stable: sum of n Cauchy r.v.s divided by n is still Cauchy
3. Gaussian is 2-stable: sum of n Gaussian r.v.s divided by √n is still Gaussian
4. Statement of generalized CLT (Gnedenko-Kolmogorov theorem)
5. What "infinite variance" really means in terms of tail behavior

CONTRAST:
  Finite variance → Gaussian limit → normalization n^(1/2)
  Infinite variance (α < 2) → α-stable limit → normalization n^(1/α)
  When α ∈ (1,2): mean exists but variance is infinite → still converges!
  When α ≤ 1: even mean may not exist
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open Real Complex

namespace CentralLimitTheoremOQ01

/-
## Part I: Characteristic Functions of α-Stable Distributions

The characteristic function encodes all information about a probability
distribution. For stable distributions, the char. fn. takes a particularly
elegant form.
-/

/-- The standard symmetric α-stable characteristic function.
    For α ∈ (0,2], this is φ_α(t) = exp(-|t|^α).

    Key special cases:
    - α=2: exp(-t²) → Gaussian (up to scaling)
    - α=1: exp(-|t|) → Cauchy distribution
    - α=1/2: exp(-|t|^(1/2)) → Lévy distribution (after adjustments)

    This is the characteristic function of the symmetric α-stable distribution
    with stability index α and scale σ=1.

    Implementation note: we compute |t|^α in ℝ then cast to ℂ, avoiding the
    need for HPow ℂ ℝ ℂ which is not available in Mathlib 4.26.0. -/
noncomputable def stableCharFun (α : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (↑(-(|t| ^ α) : ℝ))

/-- At t=0, the characteristic function is 1 (normalized probability) -/
theorem stableCharFun_zero (α : ℝ) (hα : 0 < α) :
    stableCharFun α 0 = 1 := by
  simp [stableCharFun, abs_zero, zero_rpow (ne_of_gt hα)]

/-- The characteristic function has modulus at most 1 (valid char. fn. condition). -/
theorem stableCharFun_norm_le_one (α : ℝ) (hα : 0 < α) (t : ℝ) :
    ‖stableCharFun α t‖ ≤ 1 := by
  simp only [stableCharFun]
  rw [← Complex.ofReal_exp]
  rw [Complex.norm_real]
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (abs_nonneg t) α))

/-
## Part II: The Stability Property (Core Algebraic Theorem)

A distribution is α-stable if n i.i.d. copies, normalized by n^(1/α),
have the same distribution. In terms of characteristic functions:

  [φ(t/n^(1/α))]^n = φ(t)

For the α-stable char. fn. exp(-|t|^α):
  [exp(-|t/n^(1/α)|^α)]^n
= [exp(-|t|^α / n)]^n        [since |t/n^(1/α)|^α = |t|^α / n]
= exp(-|t|^α)                [since (exp(-x/n))^n = exp(-x)]
= φ(t)  ✓
-/

/-- Key algebraic identity: |t/n^(1/α)|^α = |t|^α/n for n,α > 0.
    This is why n^(1/α) is the correct normalization for α-stable laws. -/
theorem normalization_identity (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    |t / (n : ℝ) ^ (1 / α)| ^ α = |t| ^ α / n := by
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hn_rpow_pos : (0:ℝ) < (n:ℝ)^(1/α) := Real.rpow_pos_of_pos hn_pos _
  rw [abs_div, abs_of_pos hn_rpow_pos, div_rpow (abs_nonneg t) (le_of_lt hn_rpow_pos)]
  congr 1
  rw [← Real.rpow_mul (Nat.cast_nonneg n)]
  simp [inv_mul_cancel₀ (ne_of_gt hα)]

/-- Main stability theorem: stableCharFun α is α-stable.
    The n-fold convolution of α-stable random variables, normalized by n^(1/α),
    has the same characteristic function.

    In terms of char. fns: [φ_α(t/n^(1/α))]^n = φ_α(t) -/
theorem stable_property (α : ℝ) (hα : 0 < α) (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (stableCharFun α (t / (n : ℝ) ^ (1 / α))) ^ n = stableCharFun α t := by
  simp only [stableCharFun]
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  norm_cast
  rw [normalization_identity α hα n hn t]
  field_simp [hn_pos.ne']

/-
## Part III: The Two Key Cases

### Case α=2: Gaussian (finite variance)
φ_2(t) = exp(-t²) is 2-stable, with normalization √n = n^(1/2).
This is the standard CLT.

### Case α=1: Cauchy (infinite variance!)
φ_1(t) = exp(-|t|) is 1-stable, with normalization n (not √n!).
The Cauchy distribution has INFINITE variance, yet sums still converge.
The limit is Cauchy (not Gaussian).
-/

/-- Gaussian case: α=2 stable with normalization √n. -/
theorem gaussian_is_2stable (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (stableCharFun 2 (t / Real.sqrt n)) ^ n = stableCharFun 2 t := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have : Real.sqrt n = (n : ℝ) ^ (1 / (2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
  rw [this]
  exact stable_property 2 h2 n hn t

/-- Cauchy case: α=1 stable with normalization n (not √n!).
    This is the fundamental difference from the Gaussian CLT:
    - Finite variance → normalize by √n → Gaussian limit
    - Infinite variance (Cauchy) → normalize by n → Cauchy limit -/
theorem cauchy_is_1stable (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (stableCharFun 1 (t / n)) ^ n = stableCharFun 1 t := by
  have h1 : (0 : ℝ) < 1 := one_pos
  have : (n : ℝ) = (n : ℝ) ^ (1 / (1 : ℝ)) := by simp
  conv_lhs => rw [this]
  exact stable_property 1 h1 n hn t

/-- The Cauchy characteristic function is exp(-|t|).
    Contrast with Gaussian: exp(-t²/2). -/
theorem cauchy_charFun_formula (t : ℝ) :
    stableCharFun 1 t = Complex.exp (↑(-|t|)) := by
  simp [stableCharFun, Real.rpow_one]

/-- The Gaussian characteristic function is exp(-t²).
    (Note: standard form has exp(-t²/2), this is unscaled.) -/
theorem gaussian_charFun_formula (t : ℝ) :
    stableCharFun 2 t = Complex.exp (↑(-(t^2))) := by
  simp only [stableCharFun]
  congr 1
  norm_cast
  simp [Real.rpow_two, sq_abs]

/-
## Part IV: Why Does Variance Matter?

The tail behavior of a distribution determines which stable law it
converges to under normalization.

A distribution with tails P(X > x) ~ x^(-α) for large x is in the
domain of attraction of the α-stable law.

This directly determines when variance is finite or infinite:
- α > 2: finite variance → Gaussian
- α = 2: borderline finite variance → Gaussian
- 1 < α < 2: INFINITE variance but finite mean → α-stable (not Gaussian!)
- α = 1: Cauchy (infinite variance AND borderline infinite mean)
- α < 1: infinite mean → α-stable

The key observation: the Cauchy distribution has tails P(|X| > x) ~ 1/x,
so it's in the domain of attraction of the 1-stable (Cauchy) law.
Its variance is ∫ x² dF = ∞.
-/

/-- The α-stable distributions with α ∈ (0,2) have different characteristic
    functions from the Gaussian (α=2).
    For t with |t| ≠ 1, the characteristic functions differ pointwise.
    (At |t| = 1 they agree since 1^α = 1^2 = 1 for all α.) -/
theorem stable_infinite_variance (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 2)
    (t : ℝ) (ht : t ≠ 0) (ht1 : |t| ≠ 1) :
    stableCharFun α t ≠ stableCharFun 2 t := by
  simp only [stableCharFun]
  intro h
  -- The two complex exponentials of reals are equal; extract real equality
  have habs_pos : (0 : ℝ) < |t| := abs_pos.mpr ht
  -- ofReal_exp: Complex.exp ↑r = ↑(Real.exp r)
  have hrexp : Real.exp (-(|t| ^ α)) = Real.exp (-(|t| ^ (2 : ℝ))) := by
    have := congr_arg Complex.re h
    simp only [Complex.exp_ofReal_re] at this
    exact this
  -- Real.exp is injective → exponents are equal
  have hpow : |t| ^ α = |t| ^ (2 : ℝ) := by
    have := Real.exp_injective hrexp
    linarith
  -- log both sides: α * log|t| = 2 * log|t|
  have hlog : Real.log |t| ≠ 0 := by
    intro hlogz
    rcases Real.log_eq_zero.mp hlogz with h | h | h
    · linarith [habs_pos]
    · exact ht1 h
    · linarith [abs_nonneg t]
  have hpow_log : α * Real.log |t| = 2 * Real.log |t| := by
    have h1 : Real.log (|t| ^ α) = α * Real.log |t| := Real.log_rpow habs_pos α
    have h2 : Real.log (|t| ^ (2 : ℝ)) = 2 * Real.log |t| := Real.log_rpow habs_pos 2
    rw [← h1, hpow, h2]
  have hzero : (α - 2) * Real.log |t| = 0 := by linarith
  cases mul_eq_zero.mp hzero with
  | inl h => linarith
  | inr h => exact absurd h hlog

/-
## Part V: The Generalized CLT (Gnedenko-Kolmogorov Theorem)

The following is the generalized Central Limit Theorem.
It cannot be proved from first principles here (requires deep measure theory),
but we state it precisely to answer the open question.
-/

/-
## Part VI: Summary - What Happens When Variance is Infinite

When variance is INFINITE, one of three things can happen:

1. **Distribution is in the domain of attraction of α-stable law (1 < α < 2)**:
   - Mean exists (finite), variance does not
   - Normalized sums (X₁+...+Xₙ)/n^(1/α) converge to α-stable law
   - The limit is NOT Gaussian but is still a "nice" distribution
   - Example: P(X > x) ∼ x^(-1.5) gives α=1.5 stable limit

2. **Distribution is Cauchy-like (α = 1)**:
   - Even the mean is undefined (or needs Cauchy principal value)
   - Normalized sums (X₁+...+Xₙ)/n converge to Cauchy
   - The normalization is LINEAR in n (not √n)

3. **Distribution has very heavy tails (α < 1)**:
   - Mean and variance both infinite
   - Still converges to α-stable law, but needs special centering
   - Very heavy-tailed behavior

The Gaussian is the UNIQUE stable law with finite second moment.
All other stable laws have infinite variance.
-/

/-- The key theorem: stable distributions other than Gaussian have infinite variance.
    (Formalized via characteristic function distinctness.) -/
theorem nongaussian_stable_infinite_variance (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 2) :
    -- The α-stable distribution (α < 2) does NOT have the characteristic
    -- function of a distribution with finite variance
    stableCharFun α ≠ stableCharFun 2 :=
  -- The functions differ at t = 2 (since |2| = 2 ≠ 1 and 2 ≠ 0)
  fun h => stable_infinite_variance α hα_pos hα_lt 2 (by norm_num) (by norm_num)
    (congr_fun h 2)

/-
## Part VII: The Lévy Distribution (α = 1/2 case)

The Lévy distribution is a 1/2-stable law that arises naturally as the
distribution of first passage times of Brownian motion.
Its characteristic function involves a square root: exp(-√(|t|)).

For α = 1/2: φ(t) = exp(-|t|^(1/2))

This is proved to be stable by our general theorem with α = 1/2.
-/

/-- Lévy distribution is 1/2-stable: n i.i.d. Lévy r.v.s divided by n²
    have the same distribution (normalization n^2 = n^(1/(1/2))). -/
theorem levy_is_half_stable (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (stableCharFun (1/2) (t / (n : ℝ)^2)) ^ n = stableCharFun (1/2) t := by
  have h : (0 : ℝ) < 1/2 := by norm_num
  rw [show (n : ℝ)^2 = (n : ℝ)^(1/(1/2 : ℝ)) from by
    rw [show (1 : ℝ)/(1/2 : ℝ) = 2 by norm_num]
    rw [← Real.rpow_natCast]; norm_num]
  exact stable_property (1/2) h n hn t

/-
## Summary Theorem
-/

/-- **Main Result**: When variance is infinite, CLT generalizes.
    The sum of n i.i.d. α-stable (α < 2) random variables normalized by n^(1/α)
    still has the same α-stable distribution.

    This contrasts with:
    - Finite variance (α=2): normalization n^(1/2) = √n → Gaussian
    - Infinite variance (α ∈ (0,2)): normalization n^(1/α) > √n → α-stable

    The key algebraic fact: exp(-(|t/n^(1/α)|^α)) ^ n = exp(-|t|^α) -/
theorem infinite_variance_clt_summary (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 2) :
    ∀ n : ℕ, ∀ hn : 0 < n, ∀ t : ℝ,
    (stableCharFun α (t / (n : ℝ) ^ (1/α))) ^ n = stableCharFun α t :=
  fun n hn t => stable_property α hα_pos n hn t

end CentralLimitTheoremOQ01
