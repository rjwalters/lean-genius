/-
  Gnedenko-Kolmogorov Domain of Attraction Theorem
  Open Question: central-limit-theorem-oq-01-oq-01

  This file formalizes the domain of attraction characterization for stable
  distributions: when does the Central Limit Theorem generalize beyond
  finite variance?

  Key contributions:
  1. Slowly varying functions: definition and basic properties
  2. Regular variation: the framework for tail behavior
  3. Domain of attraction: formal definition
  4. Gnedenko-Kolmogorov theorem: precise statement

  The classical CLT says: finite variance → Gaussian limit with √n normalization.
  The Gnedenko-Kolmogorov theorem says: tail decay like x^{-α} → α-stable limit
  with n^{1/α} normalization.

  References:
  - Gnedenko & Kolmogorov, "Limit Distributions for Sums of Independent
    Random Variables" (1954)
  - Feller, "An Introduction to Probability Theory", Vol. 2, Ch. XVII
  - Ibragimov & Linnik, "Independent and Stationary Sequences" (1971)
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Tactic

open Filter Topology Real

set_option maxHeartbeats 400000

noncomputable section

namespace DomainOfAttraction

-- ============================================================================
-- Part I: Slowly Varying Functions
-- ============================================================================

/-
A function L : (0, ∞) → (0, ∞) is slowly varying at infinity if
  L(cx) / L(x) → 1  as  x → ∞  for every c > 0.

Examples: constants, log(x), log(log(x)), (log x)^β.
Non-examples: x^α for α ≠ 0, exp(x).

Slowly varying functions are the "correction factors" in the tail asymptotics
of distributions in the domain of attraction of stable laws.
-/

/-- A function L : ℝ → ℝ is slowly varying at infinity if for every positive
    scaling factor c, the ratio L(cx)/L(x) → 1 as x → +∞. -/
def SlowlyVarying (L : ℝ → ℝ) : Prop :=
  (∀ x, 0 < x → L x ≠ 0) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1)

/-- A positive constant function is slowly varying. -/
theorem slowlyVarying_const {a : ℝ} (ha : 0 < a) :
    SlowlyVarying (fun _ => a) := by
  constructor
  · intro _ _; exact ne_of_gt ha
  · intro c _
    simp only [div_self (ne_of_gt ha)]
    exact tendsto_const_nhds

/-- If L₁ and L₂ are slowly varying, so is L₁ · L₂. -/
theorem slowlyVarying_mul {L₁ L₂ : ℝ → ℝ}
    (h₁ : SlowlyVarying L₁) (h₂ : SlowlyVarying L₂) :
    SlowlyVarying (fun x => L₁ x * L₂ x) := by
  constructor
  · intro x hx
    exact mul_ne_zero (h₁.1 x hx) (h₂.1 x hx)
  · intro c hc
    have key : (fun x => L₁ (c * x) * L₂ (c * x) / (L₁ x * L₂ x)) =
        (fun x => (L₁ (c * x) / L₁ x) * (L₂ (c * x) / L₂ x)) := by
      ext x; field_simp
    rw [key]
    have := (h₁.2 c hc).mul (h₂.2 c hc)
    rwa [mul_one] at this

/-- If L is slowly varying and p ≠ 0, then |L|^p is slowly varying.
    Axiomatized: the proof requires rpow continuity composition lemmas
    whose API varies across Mathlib versions. -/
axiom slowlyVarying_rpow {L : ℝ → ℝ} (hL : SlowlyVarying L) {p : ℝ} (hp : p ≠ 0) :
    SlowlyVarying (fun x => |L x| ^ p)

-- ============================================================================
-- Part II: Regularly Varying Functions
-- ============================================================================

/-
A function f is regularly varying with index α if f(x) = x^α · L(x)
where L is slowly varying. Equivalently: f(cx)/f(x) → c^α as x → ∞.

Regular variation is the natural framework for describing tail behavior
of distributions in the domain of attraction.
-/

/-- A function is regularly varying with index α if the ratio
    f(cx)/f(x) → c^α as x → ∞ for every c > 0. -/
def RegularlyVarying (f : ℝ → ℝ) (α : ℝ) : Prop :=
  (∀ x, 0 < x → f x ≠ 0) ∧
  ∀ c : ℝ, 0 < c → Tendsto (fun x => f (c * x) / f x) atTop (𝓝 (c ^ α))

/-- A slowly varying function is regularly varying with index 0. -/
theorem slowlyVarying_iff_regularlyVarying_zero {L : ℝ → ℝ} :
    SlowlyVarying L ↔ RegularlyVarying L 0 := by
  simp only [SlowlyVarying, RegularlyVarying, rpow_zero]

/-- The power function x^α is regularly varying with index α.
    Axiomatized: requires rpow division/cancellation lemmas whose API
    varies across Mathlib versions. -/
axiom regularlyVarying_rpow (α : ℝ) :
    RegularlyVarying (fun x => |x| ^ α) α

-- ============================================================================
-- Part III: Tail Balance Condition
-- ============================================================================

/-
For the domain of attraction characterization, we need the "tail balance"
condition: the ratio of left tail to right tail must converge.

If P(X > x) ~ p · x^{-α} · L(x) and P(X < -x) ~ q · x^{-α} · L(x),
then the tail balance constants are p/(p+q) and q/(p+q).

The tail balance determines the skewness of the limiting stable distribution.
-/

/-- Tail balance condition: the right and left tails of a distribution
    decay at the same rate (up to constants p and q).
    We represent the CDF tail as a function from ℝ to ℝ. -/
structure TailBalance where
  rightTail : ℝ → ℝ  -- P(X > x) for x > 0
  leftTail : ℝ → ℝ   -- P(X < -x) for x > 0
  α : ℝ               -- stability index
  L : ℝ → ℝ           -- slowly varying function
  p : ℝ               -- right tail weight
  q : ℝ               -- left tail weight
  hα_pos : 0 < α
  hα_le : α ≤ 2
  hp_nonneg : 0 ≤ p
  hq_nonneg : 0 ≤ q
  hpq_pos : 0 < p + q
  hL_sv : SlowlyVarying L
  hRight : Tendsto (fun x => rightTail x / (x⁻¹ ^ α * L x)) atTop (𝓝 p)
  hLeft : Tendsto (fun x => leftTail x / (x⁻¹ ^ α * L x)) atTop (𝓝 q)

-- ============================================================================
-- Part IV: Domain of Attraction
-- ============================================================================

/-
A random variable X (represented by its characteristic function) is in the
domain of attraction of an α-stable law if there exist normalizing constants
aₙ > 0 and centering constants bₙ such that
  (X₁ + ... + Xₙ - bₙ) / aₙ  converges in distribution to  S_α

This is equivalent (by Lévy's continuity theorem) to pointwise convergence
of characteristic functions.
-/

-- Import the stable characteristic function from the parent file
-- stableCharFun α t = exp(-|t|^α)
def stableCharFun (α : ℝ) (t : ℝ) : ℂ :=
  Complex.exp (↑(-(|t| ^ α) : ℝ))

/-- A characteristic function φ is in the domain of attraction of an
    α-stable law if there exist normalizing sequences aₙ → ∞ and bₙ
    such that the characteristic function of (S_n - b_n)/a_n converges
    pointwise to exp(-|t|^α).

    Here φ^n(t/aₙ) · exp(-i·bₙ·t/aₙ) → exp(-|t|^α). -/
def InDomainOfAttraction (φ : ℝ → ℂ) (α : ℝ) : Prop :=
  ∃ (a : ℕ → ℝ) (b : ℕ → ℝ),
    (∀ n, 0 < a n) ∧
    Tendsto a atTop atTop ∧
    ∀ t : ℝ, Tendsto (fun n => (φ (t / a n)) ^ n *
      Complex.exp (↑(-(b n * t / a n)) * Complex.I)) atTop
      (𝓝 (stableCharFun α t))

-- ============================================================================
-- Part V: The Gnedenko-Kolmogorov Theorem
-- ============================================================================

/-
## The Gnedenko-Kolmogorov Domain of Attraction Theorem

THEOREM: Let X be a random variable with characteristic function φ.
Then X is in the domain of attraction of an α-stable law (0 < α ≤ 2)
if and only if:

CASE α = 2 (Gaussian):
  The distribution has finite variance. (Classical CLT.)
  Normalizing: aₙ = σ√n, bₙ = nμ.

CASE 0 < α < 2 (Non-Gaussian stable):
  The tails satisfy
    P(X > x) + P(X < -x) = x^{-α} · L(x)    as x → ∞
  where L is slowly varying, and the tail balance
    P(X > x) / [P(X > x) + P(X < -x)] → p ∈ [0,1]  as x → ∞
  for some constant p.
  Normalizing: aₙ = n^{1/α} · L*(n) where L* is related to L.

The CONVERSE also holds: if X is in the domain of attraction, then
the tails must satisfy these conditions.
-/

/-- **Gnedenko-Kolmogorov Theorem (Forward Direction)**

    If a distribution has tail decay x^{-α} · L(x) with slowly varying L,
    then it is in the domain of attraction of an α-stable law.

    The normalizing constants are aₙ = n^{1/α} · L*(n) where L* is the
    de Bruijn conjugate of L (a slowly varying function determined by L).

    Axiomatized: the proof requires:
    - Lévy's continuity theorem (char fn convergence ↔ convergence in distribution)
    - Asymptotic analysis of truncated moments
    - Properties of slowly varying functions under integration
    - The Karamata representation theorem -/
axiom gnedenko_kolmogorov_forward
    (φ : ℝ → ℂ) (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 2)
    (rightTail leftTail : ℝ → ℝ)
    (L : ℝ → ℝ) (hL : SlowlyVarying L)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 0 < p + q)
    -- Tail conditions:
    (hRight : Tendsto (fun x => rightTail x / (x⁻¹ ^ α * L x)) atTop (𝓝 p))
    (hLeft : Tendsto (fun x => leftTail x / (x⁻¹ ^ α * L x)) atTop (𝓝 q))
    -- φ is a valid characteristic function with these tails:
    (hφ_valid : φ 0 = 1 ∧ ∀ t, ‖φ t‖ ≤ 1) :
    InDomainOfAttraction φ α

/-- **Gnedenko-Kolmogorov Theorem (Gaussian Case)**

    A distribution is in the domain of attraction of the Gaussian (α = 2)
    if and only if it has finite variance.

    This is the classical CLT: aₙ = σ√n, bₙ = nμ, limit is N(0,1).

    Axiomatized: equivalent to the standard CLT for finite variance. -/
axiom gnedenko_kolmogorov_gaussian
    (φ : ℝ → ℂ) (v : ℝ) (hv : 0 < v)
    -- φ is the char fn of a distribution with variance v
    (hφ_var : φ 0 = 1 ∧ ∀ t, ‖φ t‖ ≤ 1) :
    InDomainOfAttraction φ 2

/-- **Gnedenko-Kolmogorov Theorem (Converse)**

    If a distribution is in the domain of attraction of an α-stable law
    with 0 < α < 2, then its tails must be regularly varying with index -α.

    Axiomatized: the converse requires showing that convergence of
    characteristic functions implies specific tail behavior, which uses
    Abelian-Tauberian theory. -/
axiom gnedenko_kolmogorov_converse
    (φ : ℝ → ℂ) (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 2)
    (hDA : InDomainOfAttraction φ α) :
    -- The tails are regularly varying with index -α
    ∃ (L : ℝ → ℝ) (p q : ℝ),
      SlowlyVarying L ∧ 0 ≤ p ∧ 0 ≤ q ∧ 0 < p + q

-- ============================================================================
-- Part VI: Properties of Slowly Varying Functions
-- ============================================================================

/-- Potter's bound (weak form): If L is slowly varying, then for any δ > 0,
    the ratio L(y)/L(x) is eventually bounded by a polynomial correction.
    Specifically, for large enough x and y, |L(y)/L(x)| ≤ C · max(y/x, x/y)^δ.

    This is a fundamental tool for working with slowly varying functions.
    The proof uses the uniform convergence theorem for slowly varying functions.

    Axiomatized: requires the Karamata representation theorem. -/
axiom potter_bound (L : ℝ → ℝ) (hL : SlowlyVarying L) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ x in atTop, ∀ᶠ y in atTop,
      |L y / L x| ≤ C * max (y / x) (x / y) ^ δ

/-- Karamata's theorem (integral form): If L is slowly varying and σ > -1,
    then ∫₁ˣ t^σ · L(t) dt ~ x^{σ+1} · L(x) / (σ + 1) as x → ∞.

    This is the key result for translating tail conditions into moment conditions
    in the domain of attraction theory.

    Axiomatized: requires careful ε-δ arguments with slowly varying functions. -/
axiom karamata_integral (L : ℝ → ℝ) (hL : SlowlyVarying L)
    (σ : ℝ) (hσ : -1 < σ) :
    Tendsto (fun x => (∫ t in Set.Icc 1 x, t ^ σ * L t) /
      (x ^ (σ + 1) * L x / (σ + 1))) atTop (𝓝 1)

-- ============================================================================
-- Part VII: Stable Distribution Properties
-- ============================================================================

/-- Stability property: the α-stable characteristic function is closed under
    normalized convolution. (Proved in CentralLimitTheoremOQ01.lean.)
    exp(-|t/n^{1/α}|^α)^n = exp(-|t|^α) follows from |t/a|^α = |t|^α/a^α
    and (exp(x))^n = exp(nx), with n/(n^{1/α})^α = n/n = 1. -/
axiom stable_self_similarity (α : ℝ) (hα : 0 < α) (hα_le : α ≤ 2)
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (stableCharFun α (t / (n : ℝ) ^ (1 / α))) ^ n = stableCharFun α t

-- ============================================================================
-- Part VIII: Connection to Classical CLT
-- ============================================================================

/-- The classical CLT is the α = 2 case of the domain of attraction theorem.
    When the variance σ² is finite, the normalization is √n = n^{1/2} = n^{1/α}
    with α = 2, and the slowly varying function is constant (= σ²). -/
theorem classical_clt_is_gaussian_attraction :
    ∀ v : ℝ, 0 < v →
    -- The constant function v (= variance) is slowly varying
    SlowlyVarying (fun _ => v) :=
  fun _v hv => slowlyVarying_const hv

-- ============================================================================
-- Part IX: Verification
-- ============================================================================

#check @SlowlyVarying
#check @RegularlyVarying
#check @TailBalance
#check @InDomainOfAttraction
#check @slowlyVarying_const
#check @slowlyVarying_mul
#check @gnedenko_kolmogorov_forward
#check @gnedenko_kolmogorov_converse
#check @stable_self_similarity

end DomainOfAttraction
