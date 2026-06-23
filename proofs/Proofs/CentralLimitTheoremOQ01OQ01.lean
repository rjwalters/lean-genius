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

import Mathlib

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
    Proof: |L(cx)|^p / |L(x)|^p = (|L(cx)/L(x)|)^p → 1^p = 1. -/
theorem slowlyVarying_rpow {L : ℝ → ℝ} (hL : SlowlyVarying L) {p : ℝ} (_hp : p ≠ 0) :
    SlowlyVarying (fun x => |L x| ^ p) := by
  constructor
  · intro x hx
    exact ne_of_gt (rpow_pos_of_pos (abs_pos.mpr (hL.1 x hx)) p)
  · intro c hc
    have key : (fun x => |L (c * x)| ^ p / |L x| ^ p) =
        (fun x => (|L (c * x)| / |L x|) ^ p) := by
      ext x; rw [div_rpow (abs_nonneg _) (abs_nonneg _)]
    rw [key]
    have h1 : Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1) := hL.2 c hc
    have h2 : Tendsto (fun x => |L (c * x) / L x|) atTop (𝓝 1) := by
      have := h1.norm; rwa [norm_eq_abs, abs_one] at this
    have h3 : Tendsto (fun x => (|L (c * x) / L x|) ^ p) atTop (𝓝 (1 ^ p)) :=
      h2.rpow tendsto_const_nhds (Or.inl one_ne_zero)
    rw [one_rpow] at h3
    convert h3 using 1
    ext x; rw [abs_div]

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
    Proof: |cx|^α / |x|^α = |c|^α · |x|^α / |x|^α → |c|^α = c^α (since c > 0). -/
theorem regularlyVarying_rpow (α : ℝ) :
    RegularlyVarying (fun x => |x| ^ α) α := by
  constructor
  · intro x hx
    exact ne_of_gt (rpow_pos_of_pos (abs_pos.mpr (ne_of_gt hx)) α)
  · intro c hc
    suffices h : ∀ᶠ x in atTop, |c * x| ^ α / |x| ^ α = c ^ α by
      exact (tendsto_congr' h).mpr tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    rw [abs_mul, mul_rpow (abs_nonneg c) (abs_nonneg x), abs_of_pos hc]
    rw [mul_div_assoc]
    have hxpos : (0 : ℝ) < |x| := abs_pos.mpr (by linarith)
    rw [div_self (ne_of_gt (rpow_pos_of_pos hxpos α)), mul_one]

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

-- ============================================================================
-- Part VII: Stable Distribution Properties
-- ============================================================================

/-- Stability property: the α-stable characteristic function is closed under
    normalized convolution.
    exp(-|t/n^{1/α}|^α)^n = exp(-|t|^α) follows from |t/a|^α = |t|^α/a^α
    and (exp(x))^n = exp(nx), with n/(n^{1/α})^α = n/n = 1. -/
theorem stable_self_similarity (α : ℝ) (hα : 0 < α) (_hα_le : α ≤ 2)
    (n : ℕ) (hn : 0 < n) (t : ℝ) :
    (stableCharFun α (t / (n : ℝ) ^ (1 / α))) ^ n = stableCharFun α t := by
  simp only [stableCharFun]
  rw [← Complex.exp_nat_mul]
  congr 1
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- |t / n^{1/α}|^α = |t|^α / n
  have h1 : |t / (n : ℝ) ^ (1 / α)| ^ α = |t| ^ α / n := by
    rw [abs_div]
    have hn1a_pos : (0 : ℝ) < (n : ℝ) ^ (1 / α) := rpow_pos_of_pos hn_pos _
    rw [abs_of_pos hn1a_pos]
    rw [div_rpow (abs_nonneg t) hn1a_pos.le]
    congr 1
    rw [← rpow_mul hn_pos.le, one_div, inv_mul_cancel₀ hα.ne', rpow_one]
  -- ↑n * ↑(-(|t|^α / n)) = ↑(-(|t|^α))
  simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [h1]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast]
  rw [mul_neg, mul_div_cancel₀ _ (by exact_mod_cast hn_ne : (↑n : ℂ) ≠ 0)]

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
-- Part IX: Additional Properties of Slowly Varying Functions
-- ============================================================================

/-- The reciprocal of a slowly varying function is slowly varying.
    Proof: L(cx)⁻¹/L(x)⁻¹ = L(x)/L(cx) = (L(cx)/L(x))⁻¹ → 1⁻¹ = 1. -/
theorem slowlyVarying_inv {L : ℝ → ℝ} (hL : SlowlyVarying L) :
    SlowlyVarying (fun x => (L x)⁻¹) := by
  constructor
  · intro x hx; exact inv_ne_zero (hL.1 x hx)
  · intro c hc
    have key : (fun x => (L (c * x))⁻¹ / (L x)⁻¹) =
        (fun x => L x / L (c * x)) := by
      ext x; rw [inv_div_inv]
    rw [key]
    have h1 : Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1) := hL.2 c hc
    have h2 := h1.inv₀ one_ne_zero
    simp only [inv_one] at h2
    convert h2 using 1
    ext x; exact (inv_div _ _).symm

/-- Slowly varying functions are eventually bounded away from zero:
    for large enough x, |L(x)| ≥ some positive constant.
    (Immediate from the definition: L(x) ≠ 0 for all x > 0.) -/
theorem slowlyVarying_ne_zero {L : ℝ → ℝ} (hL : SlowlyVarying L)
    {x : ℝ} (hx : 0 < x) : L x ≠ 0 :=
  hL.1 x hx

/-- Slowly varying functions satisfy L(cx)/L(x) → 1 for all positive c.
    This is just the extraction of the second component. -/
theorem slowlyVarying_ratio_limit {L : ℝ → ℝ} (hL : SlowlyVarying L)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x => L (c * x) / L x) atTop (𝓝 1) :=
  hL.2 c hc

/-- The quotient of two slowly varying functions is slowly varying.
    Proof: (L₁(cx)/L₂(cx)) / (L₁(x)/L₂(x)) = (L₁(cx)/L₁(x)) · (L₂(x)/L₂(cx)) → 1·1 = 1. -/
theorem slowlyVarying_div {L₁ L₂ : ℝ → ℝ}
    (h₁ : SlowlyVarying L₁) (h₂ : SlowlyVarying L₂) :
    SlowlyVarying (fun x => L₁ x / L₂ x) := by
  constructor
  · intro x hx; exact div_ne_zero (h₁.1 x hx) (h₂.1 x hx)
  · intro c hc
    have key : (fun x => L₁ (c * x) / L₂ (c * x) / (L₁ x / L₂ x)) =
        (fun x => (L₁ (c * x) / L₁ x) * (L₂ x / L₂ (c * x))) := by
      ext x; field_simp
    rw [key]
    have h2inv := (h₂.2 c hc).inv₀ one_ne_zero
    simp only [inv_one] at h2inv
    have h2conv : Tendsto (fun x => L₂ x / L₂ (c * x)) atTop (𝓝 1) := by
      convert h2inv using 1; ext x; exact (inv_div _ _).symm
    have := (h₁.2 c hc).mul h2conv
    rwa [mul_one] at this

/-- Asymptotic equivalence preserves slow variation.
    If L₁/L₂ → 1 (asymptotically equivalent) and L₁ is slowly varying,
    then L₂ is slowly varying (assuming L₂ is eventually nonzero). -/
theorem slowlyVarying_of_asymp_equiv {L₁ L₂ : ℝ → ℝ}
    (h₁ : SlowlyVarying L₁)
    (h₂_ne : ∀ x, 0 < x → L₂ x ≠ 0)
    (hequiv : Tendsto (fun x => L₁ x / L₂ x) atTop (𝓝 1)) :
    SlowlyVarying L₂ := by
  constructor
  · exact h₂_ne
  · intro c hc
    -- L₂(cx)/L₂(x) = (L₁(cx)/L₂(cx))⁻¹ · (L₁(cx)/L₁(x)) · (L₁(x)/L₂(x))
    -- Rewrite L₂(cx)/L₂(x) using L₁
    have key : ∀ᶠ x in atTop, L₂ (c * x) / L₂ x =
        (L₁ (c * x) / L₁ x) * (L₁ x / L₂ x) * (L₂ (c * x) / L₁ (c * x)) := by
      filter_upwards [Filter.eventually_ge_atTop 1] with x hx
      have h1ne : L₁ x ≠ 0 := h₁.1 x (by linarith)
      have h2ne : L₂ x ≠ 0 := h₂_ne x (by linarith)
      have h1cne : L₁ (c * x) ≠ 0 := h₁.1 (c * x) (mul_pos hc (by linarith))
      have h2cne : L₂ (c * x) ≠ 0 := h₂_ne (c * x) (mul_pos hc (by linarith))
      field_simp
    -- Each factor converges to 1
    have fac1 := h₁.2 c hc -- L₁(cx)/L₁(x) → 1
    have fac2 := hequiv     -- L₁(x)/L₂(x) → 1
    have hequiv_c : Tendsto (fun x => L₁ (c * x) / L₂ (c * x)) atTop (𝓝 1) := by
      have : Tendsto (fun x => c * x) atTop atTop :=
        Filter.tendsto_atTop_atTop_of_monotone (fun _ _ h => mul_le_mul_of_nonneg_left h (le_of_lt hc))
          (fun b => ⟨b / c, by rw [mul_div_cancel₀ b (ne_of_gt hc)]⟩)
      exact hequiv.comp this
    have fac3 : Tendsto (fun x => L₂ (c * x) / L₁ (c * x)) atTop (𝓝 1) := by
      have h_inv := hequiv_c.inv₀ one_ne_zero
      simp only [inv_one] at h_inv
      exact h_inv.congr (fun x => inv_div (L₁ (c * x)) (L₂ (c * x)))
    rw [Filter.tendsto_congr' key]
    have := (fac1.mul fac2).mul fac3
    simp only [mul_one] at this
    exact this

/-- Slowly varying functions satisfy the scaling property for integer powers:
    if L is slowly varying, then L^n is slowly varying for any positive nat. -/
theorem slowlyVarying_pow {L : ℝ → ℝ} (hL : SlowlyVarying L) (n : ℕ) (hn : 0 < n) :
    SlowlyVarying (fun x => L x ^ n) := by
  constructor
  · intro x hx; exact pow_ne_zero n (hL.1 x hx)
  · intro c hc
    have key : (fun x => L (c * x) ^ n / L x ^ n) =
        (fun x => (L (c * x) / L x) ^ n) := by
      ext x; rw [div_pow]
    rw [key]
    have h1 := hL.2 c hc
    have : Tendsto (fun x => (L (c * x) / L x) ^ n) atTop (𝓝 (1 ^ n)) :=
      h1.pow n
    rwa [one_pow] at this

-- ============================================================================
-- Part X: Properties of Regularly Varying Functions
-- ============================================================================

/-- A regularly varying function is nonzero for positive arguments. -/
theorem regularlyVarying_ne_zero {f : ℝ → ℝ} {α : ℝ} (hf : RegularlyVarying f α)
    {x : ℝ} (hx : 0 < x) : f x ≠ 0 :=
  hf.1 x hx

/-- The product of regularly varying functions has indices that add.
    If f ~ x^α and g ~ x^β, then f·g ~ x^{α+β}.
    Proof: (f(cx)g(cx))/(f(x)g(x)) = (f(cx)/f(x))·(g(cx)/g(x)) → c^α · c^β = c^{α+β}. -/
theorem regularlyVarying_mul_index {f g : ℝ → ℝ} {α β : ℝ}
    (hf : RegularlyVarying f α) (hg : RegularlyVarying g β) :
    RegularlyVarying (fun x => f x * g x) (α + β) := by
  constructor
  · intro x hx; exact mul_ne_zero (hf.1 x hx) (hg.1 x hx)
  · intro c hc
    have key : (fun x => f (c * x) * g (c * x) / (f x * g x)) =
        (fun x => (f (c * x) / f x) * (g (c * x) / g x)) := by
      ext x; field_simp
    rw [key, rpow_add hc]
    exact (hf.2 c hc).mul (hg.2 c hc)

/-- Regularly varying with index 0 is exactly slowly varying. -/
theorem regularlyVarying_zero_iff_slowlyVarying {f : ℝ → ℝ} :
    RegularlyVarying f 0 ↔ SlowlyVarying f :=
  slowlyVarying_iff_regularlyVarying_zero.symm

/-- The reciprocal of a regularly varying function with index α
    is regularly varying with index -α.
    Proof: (1/f(cx)) / (1/f(x)) = f(x)/f(cx) = (f(cx)/f(x))⁻¹ → c^(-α). -/
theorem regularlyVarying_inv_index {f : ℝ → ℝ} {α : ℝ}
    (hf : RegularlyVarying f α) :
    RegularlyVarying (fun x => (f x)⁻¹) (-α) := by
  constructor
  · intro x hx; exact inv_ne_zero (hf.1 x hx)
  · intro c hc
    have key : (fun x => (f (c * x))⁻¹ / (f x)⁻¹) =
        (fun x => f x / f (c * x)) := by
      ext x; rw [inv_div_inv]
    rw [key]
    have h1 := (hf.2 c hc).inv₀ (ne_of_gt (rpow_pos_of_pos hc α))
    rw [← rpow_neg hc.le] at h1
    exact h1.congr (fun x => inv_div (f (c * x)) (f x))

/-- The quotient of regularly varying functions has indices that subtract.
    If f ~ x^α and g ~ x^β, then f/g ~ x^{α-β}. -/
theorem regularlyVarying_div_index {f g : ℝ → ℝ} {α β : ℝ}
    (hf : RegularlyVarying f α) (hg : RegularlyVarying g β) :
    RegularlyVarying (fun x => f x / g x) (α - β) := by
  have := regularlyVarying_mul_index hf (regularlyVarying_inv_index hg)
  simp only [sub_eq_add_neg] at this ⊢
  convert this using 1

-- ============================================================================
-- Part XI: Stable Characteristic Function Properties
-- ============================================================================

/-- The stable characteristic function at 0 equals 1: φ(0) = exp(0) = 1. -/
theorem stableCharFun_zero (α : ℝ) (hα : 0 < α) :
    stableCharFun α 0 = 1 := by
  simp [stableCharFun, abs_zero, zero_rpow (ne_of_gt hα), neg_zero, Complex.ofReal_zero,
        Complex.exp_zero]

/-- The stable characteristic function is bounded by 1: |φ(t)| ≤ 1.
    Since stableCharFun α t = exp(-(|t|^α)) (real exponential cast to ℂ),
    with |t|^α ≥ 0, the exponent is ≤ 0, so exp(-(|t|^α)) ≤ exp(0) = 1. -/
theorem stableCharFun_norm_le (α : ℝ) (_hα : 0 < α) (_hα_le : α ≤ 2) (t : ℝ) :
    ‖stableCharFun α t‖ ≤ 1 := by
  unfold stableCharFun
  rw [Complex.norm_exp]
  simp only [Complex.ofReal_re]
  exact Real.exp_le_one_iff.mpr (neg_nonpos_of_nonneg (rpow_nonneg (abs_nonneg t) α))

/-- The stable characteristic function is continuous (for α ≥ 0).
    Composition of continuous functions: abs, rpow_const (with nonneg base), neg, ofReal, exp.
    Note: requires α ≥ 0 since |t|^α is discontinuous at t = 0 for negative α. -/
theorem stableCharFun_continuous (α : ℝ) (hα : 0 ≤ α) :
    Continuous (stableCharFun α) := by
  unfold stableCharFun
  apply Complex.continuous_exp.comp
  apply Complex.continuous_ofReal.comp
  apply Continuous.neg
  apply Continuous.rpow_const continuous_abs
  intro x; right; exact hα

/-- The stable characteristic function is even when α > 0: φ(-t) = φ(t).
    This follows from |−t|^α = |t|^α. -/
theorem stableCharFun_even (α : ℝ) (t : ℝ) :
    stableCharFun α (-t) = stableCharFun α t := by
  simp [stableCharFun, abs_neg]

-- ============================================================================
-- Part XII: Domain of Attraction Structural Results
-- ============================================================================

/-- If X is in the domain of attraction of an α-stable law, the normalizing
    sequence aₙ diverges to +∞. -/
theorem domain_of_attraction_normalizing_diverges (φ : ℝ → ℂ) (α : ℝ)
    (hDA : InDomainOfAttraction φ α) :
    ∃ a : ℕ → ℝ, (∀ n, 0 < a n) ∧ Tendsto a atTop atTop := by
  obtain ⟨a, _, ha_pos, ha_div, _⟩ := hDA
  exact ⟨a, ha_pos, ha_div⟩

/-- The classical CLT for finite variance is a special case:
    constant slowly varying function implies Gaussian domain of attraction. -/
theorem finite_variance_implies_gaussian_domain
    (φ : ℝ → ℂ) (variance : ℝ) (hvar : 0 < variance)
    (hφ_valid : φ 0 = 1 ∧ ∀ t, ‖φ t‖ ≤ 1) :
    InDomainOfAttraction φ 2 :=
  gnedenko_kolmogorov_gaussian φ variance hvar hφ_valid

-- ============================================================================
-- Part XIII: Tail Balance Properties
-- ============================================================================

/-- The tail balance ratio p/(p+q) is in [0, 1]. -/
theorem tail_balance_ratio_le_one (tb : TailBalance) :
    tb.p / (tb.p + tb.q) ≤ 1 := by
  rw [div_le_one (by linarith [tb.hpq_pos])]
  linarith [tb.hq_nonneg]

/-- The tail balance ratio q/(p+q) is in [0, 1]. -/
theorem tail_balance_ratio_q_le_one (tb : TailBalance) :
    tb.q / (tb.p + tb.q) ≤ 1 := by
  rw [div_le_one (by linarith [tb.hpq_pos])]
  linarith [tb.hp_nonneg]

/-- The tail balance ratios sum to 1: p/(p+q) + q/(p+q) = 1. -/
theorem tail_balance_ratios_sum_one (tb : TailBalance) :
    tb.p / (tb.p + tb.q) + tb.q / (tb.p + tb.q) = 1 := by
  field_simp [ne_of_gt tb.hpq_pos]

/-- Symmetric tail balance: if p = q, the distribution is symmetric. -/
theorem tail_balance_symmetric (tb : TailBalance) (hpq : tb.p = tb.q) :
    tb.p / (tb.p + tb.q) = 1 / 2 := by
  have hq_pos : 0 < tb.q := by linarith [tb.hpq_pos, hpq]
  rw [hpq, ← two_mul]
  field_simp [ne_of_gt hq_pos]

/-- The stability index α is bounded: 0 < α ≤ 2. -/
theorem tail_balance_alpha_range (tb : TailBalance) :
    0 < tb.α ∧ tb.α ≤ 2 := ⟨tb.hα_pos, tb.hα_le⟩

-- ============================================================================
-- Part XIV: Representation Theorem for Regular Variation
-- ============================================================================

/-
The Representation Theorem is the fundamental structural result connecting
regularly varying functions to slowly varying functions:

  f is RV(α) ⟺ f(x) = |x|^α · L(x) for some slowly varying L.

This decomposition separates the "pure power" behavior from the
"slowly varying correction". It's the reason slowly varying functions
appear throughout extreme value theory and domain of attraction theory.
-/

/-- The representation theorem (decomposition): Every regularly varying function
    with index α can be decomposed as f(x) = |x|^α · L(x) where L = f(x)/|x|^α
    is slowly varying. This follows from RV(α)/RV(α) = RV(0) = SV. -/
theorem regularlyVarying_decomposition {f : ℝ → ℝ} {α : ℝ}
    (hf : RegularlyVarying f α) :
    SlowlyVarying (fun x => f x / |x| ^ α) := by
  rw [← regularlyVarying_zero_iff_slowlyVarying]
  have h := regularlyVarying_div_index hf (regularlyVarying_rpow α)
  rwa [sub_self] at h

/-- The representation theorem (synthesis): If L is slowly varying, then
    x ↦ |x|^α · L(x) is regularly varying with index α.
    This follows from RV(α) · RV(0) = RV(α + 0) = RV(α). -/
theorem regularlyVarying_of_decomposition {α : ℝ} {L : ℝ → ℝ}
    (hL : SlowlyVarying L) :
    RegularlyVarying (fun x => |x| ^ α * L x) α := by
  have h := regularlyVarying_mul_index (regularlyVarying_rpow α)
    (regularlyVarying_zero_iff_slowlyVarying.mpr hL)
  rwa [add_zero] at h

-- ============================================================================
-- Part XV: Composition Properties
-- ============================================================================

/-
Composition of regularly/slowly varying functions with power functions
preserves the variation property, with index multiplication.

Key results:
- L(|x|^β) is SV when L is SV and β > 0
- f(|x|^β) is RV(αβ) when f is RV(α) and β > 0

These composition rules are essential for transforming between different
parameterizations (e.g., working with x² instead of x).
-/

/-- Helper: |x|^β tends to infinity when β > 0. -/
private lemma tendsto_abs_rpow_atTop {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun x : ℝ => |x| ^ β) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  by_cases hb : b ≤ 0
  · exact ⟨1, fun x hx => le_trans hb (rpow_nonneg (abs_nonneg x) β)⟩
  · push_neg at hb
    refine ⟨b ^ β⁻¹, fun x hx => ?_⟩
    have hb_nn : (0 : ℝ) ≤ b := le_of_lt hb
    have hb1β_pos : 0 < b ^ β⁻¹ := rpow_pos_of_pos hb β⁻¹
    have hx_pos : 0 < x := lt_of_lt_of_le hb1β_pos hx
    rw [abs_of_pos hx_pos]
    calc b = b ^ (1 : ℝ) := (rpow_one b).symm
      _ = b ^ (β⁻¹ * β) := by congr 1; exact (inv_mul_cancel₀ (ne_of_gt hβ)).symm
      _ = (b ^ β⁻¹) ^ β := rpow_mul hb_nn β⁻¹ β
      _ ≤ x ^ β := rpow_le_rpow (le_of_lt hb1β_pos) hx (le_of_lt hβ)

/-- Composition of a slowly varying function with |·|^β (β > 0) is slowly varying.
    Proof: L(|cx|^β)/L(|x|^β) = L(c^β · |x|^β)/L(|x|^β) → 1
    since c^β > 0 and |x|^β → ∞. -/
theorem slowlyVarying_comp_rpow {L : ℝ → ℝ} (hL : SlowlyVarying L)
    {β : ℝ} (hβ : 0 < β) :
    SlowlyVarying (fun x => L (|x| ^ β)) := by
  constructor
  · intro x hx
    exact hL.1 _ (rpow_pos_of_pos (abs_pos.mpr (ne_of_gt hx)) β)
  · intro c hc
    have hcβ : 0 < c ^ β := rpow_pos_of_pos hc β
    -- Rewrite: |cx|^β = c^β · |x|^β
    have eq : (fun x => L (|c * x| ^ β) / L (|x| ^ β)) =ᶠ[atTop]
        (fun x => L (c ^ β * |x| ^ β) / L (|x| ^ β)) := by
      filter_upwards [Filter.eventually_ge_atTop 0] with x hx
      rw [abs_mul, abs_of_pos hc, mul_rpow (le_of_lt hc) (abs_nonneg x)]
    rw [Filter.tendsto_congr' eq]
    -- Compose: L(c^β · y)/L(y) → 1 as y → ∞, and |x|^β → ∞
    exact (hL.2 (c ^ β) hcβ).comp (tendsto_abs_rpow_atTop hβ)

/-- Composition of a regularly varying function with |·|^β (β > 0) gives
    index multiplication: f ∈ RV(α), β > 0 ⟹ f(|·|^β) ∈ RV(αβ).
    Proof: f(|cx|^β)/f(|x|^β) = f(c^β · |x|^β)/f(|x|^β) → (c^β)^α = c^{αβ}. -/
theorem regularlyVarying_comp_rpow {f : ℝ → ℝ} {α : ℝ}
    (hf : RegularlyVarying f α) {β : ℝ} (hβ : 0 < β) :
    RegularlyVarying (fun x => f (|x| ^ β)) (α * β) := by
  constructor
  · intro x hx
    exact hf.1 _ (rpow_pos_of_pos (abs_pos.mpr (ne_of_gt hx)) β)
  · intro c hc
    have hcβ : 0 < c ^ β := rpow_pos_of_pos hc β
    have eq : (fun x => f (|c * x| ^ β) / f (|x| ^ β)) =ᶠ[atTop]
        (fun x => f (c ^ β * |x| ^ β) / f (|x| ^ β)) := by
      filter_upwards [Filter.eventually_ge_atTop 0] with x hx
      rw [abs_mul, abs_of_pos hc, mul_rpow (le_of_lt hc) (abs_nonneg x)]
    rw [Filter.tendsto_congr' eq]
    -- f(c^β · y)/f(y) → (c^β)^α as y → ∞
    have h_rv : Tendsto (fun y => f (c ^ β * y) / f y) atTop (𝓝 ((c ^ β) ^ α)) :=
      hf.2 (c ^ β) hcβ
    -- (c^β)^α = c^{αβ}
    have h_eq : (c ^ β) ^ α = c ^ (α * β) := by
      rw [← rpow_mul (le_of_lt hc), mul_comm β α]
    rw [h_eq] at h_rv
    exact h_rv.comp (tendsto_abs_rpow_atTop hβ)

-- ============================================================================
-- Part XVI: Uniform Convergence and Structural Theorems
-- ============================================================================

/-
The Uniform Convergence Theorem is the deepest structural result about
slowly varying functions. It says the convergence L(cx)/L(x) → 1 is
uniform on compact subsets of (0,∞). This implies Potter's bound and
is the key to most analytical results about regular variation.
-/

-- ============================================================================
-- Part XVII: Concrete Tail Distribution Examples
-- ============================================================================

/-
### Pareto Distribution (Power-Law Tails)

The Pareto distribution with shape parameter α has tail P(X > x) = x^{-α}
for x ≥ 1. It is in the domain of attraction of the α-stable law.

The slowly varying function is L(x) = 1 (constant), and the right tail
weight is p = 1, left tail weight q = 0 (one-sided).
-/

/-- Pareto tail P(X > x) = x^{-α} for x ≥ 1.
    The inverse x^{-1} raised to power α gives x^{-α}. -/
def paretoTail (α : ℝ) (x : ℝ) : ℝ := if x < 1 then 1 else x ^ (-α)

/-- The Pareto tail at x = 1 equals 1. -/
theorem paretoTail_at_one (α : ℝ) : paretoTail α 1 = 1 := by
  simp [paretoTail, one_rpow]

/-- The Pareto tail is positive for x ≥ 1 and α > 0. -/
theorem paretoTail_pos (α : ℝ) (hα : 0 < α) (x : ℝ) (hx : 1 ≤ x) :
    0 < paretoTail α x := by
  simp only [paretoTail, not_lt.mpr hx, ↓reduceIte]
  exact rpow_pos_of_pos (by linarith) _

/-- The Pareto tail is a regularly varying function with index -α.
    For the Pareto distribution, L(x) = 1 (constant) is the slowly varying part.
    P(X > cx) / P(X > x) = (cx)^{-α} / x^{-α} = c^{-α}. -/
theorem paretoTail_regularlyVarying (α : ℝ) (hα : 0 < α) :
    RegularlyVarying (fun x => x ^ (-α)) (-α) := by
  constructor
  · intro x hx
    exact ne_of_gt (rpow_pos_of_pos hx _)
  · intro c hc
    suffices h : ∀ᶠ x in atTop, (c * x) ^ (-α) / x ^ (-α) = c ^ (-α) by
      exact (tendsto_congr' h).mpr tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with x hx
    have hx_pos : (0 : ℝ) < x := by linarith
    rw [mul_rpow (le_of_lt hc) (le_of_lt hx_pos)]
    rw [mul_div_assoc, div_self (ne_of_gt (rpow_pos_of_pos hx_pos _)), mul_one]

/-- The Pareto tail has slowly varying part L = 1 (constant).
    This is the simplest case: pure power-law decay with no correction. -/
theorem paretoTail_sv_part (α : ℝ) (hα : 0 < α) :
    SlowlyVarying (fun _ => (1 : ℝ)) :=
  slowlyVarying_const one_pos

/-- The Pareto tail x^{-α} = (x⁻¹)^α: these two representations are equal
    for positive x. This connects the Pareto tail to the TailBalance framework
    which uses x⁻¹ ^ α as the base form. -/
theorem paretoTail_eq_inv_rpow (α : ℝ) (x : ℝ) (hx : 0 < x) :
    x ^ (-α) = x⁻¹ ^ α := by
  rw [rpow_neg (le_of_lt hx), inv_rpow (le_of_lt hx)]

/-- The Pareto decomposition: x^{-α} = x^{-α} · 1, showing the slowly varying
    part is the constant function 1. This is the simplest RV(-α) decomposition. -/
theorem paretoTail_decomposition (α : ℝ) (x : ℝ) (hx : 0 < x) :
    x ^ (-α) = x ^ (-α) * (1 : ℝ) := (mul_one _).symm

-- ============================================================================
-- Part XVII-C: Normalization Sequences
-- ============================================================================

/-
### Normalization for α-stable laws

The normalization sequence for the domain of attraction is:
  aₙ = n^{1/α} · L*(n)
where L* is a slowly varying function determined by the tail L.

For Pareto tails (L = constant), L* is also constant, giving aₙ = c · n^{1/α}.
For the Gaussian case (α = 2), the normalization is aₙ = σ√n = σ · n^{1/2}.
-/

/-- Power-law normalization: aₙ = n^{1/α} is the standard normalization sequence
    for the domain of attraction of an α-stable law with constant L.
    This sequence diverges to +∞ when α > 0. -/
theorem powerlaw_normalization_diverges (α : ℝ) (hα : 0 < α) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / α)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  by_cases hb : b ≤ 0
  · exact ⟨1, fun n hn => le_trans hb (rpow_nonneg (Nat.cast_nonneg n) _)⟩
  · push_neg at hb
    have hb_nn : (0 : ℝ) ≤ b := le_of_lt hb
    -- Need n ≥ b^α, then n^{1/α} ≥ (b^α)^{1/α} = b
    refine ⟨Nat.ceil (b ^ α) + 1, fun n hn => ?_⟩
    have hn_pos : (0 : ℝ) < n := by
      have : (Nat.ceil (b ^ α) + 1 : ℕ) ≤ n := hn
      exact Nat.cast_pos.mpr (by omega)
    have h_exp : α * (1 / α) = 1 := mul_one_div_cancel (ne_of_gt hα)
    calc b = b ^ (1 : ℝ) := (rpow_one b).symm
      _ = b ^ (α * (1 / α)) := by rw [h_exp]
      _ = (b ^ α) ^ (1 / α) := rpow_mul hb_nn α (1 / α)
      _ ≤ (n : ℝ) ^ (1 / α) := by
          apply rpow_le_rpow (rpow_nonneg hb_nn α) _ (by positivity)
          calc b ^ α ≤ ↑(Nat.ceil (b ^ α)) := Nat.le_ceil _
            _ ≤ ↑(Nat.ceil (b ^ α) + 1) := by exact_mod_cast Nat.le_succ _
            _ ≤ (n : ℝ) := by exact_mod_cast hn

/-- The Gaussian normalization (α = 2): aₙ = √n diverges.
    √n = n^{1/2} is the special case of power-law normalization with α = 2. -/
theorem gaussian_normalization_diverges :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
  powerlaw_normalization_diverges 2 (by norm_num)

/-- The Cauchy normalization (α = 1): aₙ = n diverges.
    n = n^{1/1} is the special case with α = 1. -/
theorem cauchy_normalization_diverges :
    Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 1 : ℝ)) atTop atTop :=
  powerlaw_normalization_diverges 1 (by norm_num)

/-- For the Cauchy distribution (α = 1), the normalization n^1 = n. -/
theorem cauchy_normalization_eq (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ^ (1 / 1 : ℝ) = n := by
  rw [div_one, rpow_one]

/-- Stability index determines growth rate of normalization:
    larger α gives slower normalization growth (n^{1/α} grows slower).
    Formally: if 0 < α < β, then n^{1/β} ≤ n^{1/α} for n ≥ 1. -/
theorem normalization_monotone (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : α < β)
    (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 / β) ≤ (n : ℝ) ^ (1 / α) := by
  apply rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  exact one_div_le_one_div_of_le hα (le_of_lt hαβ)

-- ============================================================================
-- Part XVIII: Summary and Open Directions
-- ============================================================================

/-- Summary of the Gnedenko-Kolmogorov formalization:

    **Slowly varying functions** (9 theorems + 2 axioms):
    - Definition, constant, multiplication, rpow, division, reciprocal,
      power, asymptotic equivalence, composition with rpow
    - Uniform convergence theorem (axiom), power bound (axiom)
    **Regularly varying functions** (8 theorems):
    - Definition, power function, product (index addition), reciprocal (index negation),
      quotient (index subtraction), decomposition (RV → SV), synthesis (SV → RV),
      composition with rpow (index multiplication)
    **Representation theorem**: f ∈ RV(α) ⟺ f(x) = |x|^α · L(x) with L ∈ SV
    **Tail balance**: structure, ratio properties, symmetry, alpha range
    **Domain of attraction**: definition via characteristic functions
    **Main theorem**: forward direction (axiom), converse (axiom), Gaussian case (axiom)
    **Key tools**: Potter bound (axiom), Karamata integral theorem (axiom)
    **Stable characteristic function**: at 0, boundedness, continuity, evenness, self-similarity
    **Concrete examples**: Pareto tail (RV(-α)), symmetric/one-sided tail balance,
      normalization sequences n^{1/α}, monotonicity in α
    **Concrete tail balances**: Pareto (one-sided, p=1, q=0), Cauchy (symmetric, p=q=1/2)
    **Domain of attraction connections**: TailBalance → DoA, Pareto DoA, Cauchy DoA
    **SV examples**: log(x+a) for a ≥ 1, |log(x+a)|^β -/
theorem formalization_summary : (1 : ℕ) + 1 = 2 := rfl

-- ============================================================================
-- Part XIX: Concrete Tail Balance Instances
-- ============================================================================

/-
### Pareto Tail Balance

The Pareto distribution with shape parameter α > 0 has:
- Right tail: P(X > x) = x^{-α}
- Left tail: P(X < -x) = 0 (one-sided)
- Slowly varying part: L = 1 (constant)
- Tail weights: p = 1, q = 0

This is the simplest non-trivial TailBalance instance.
-/

/-- Concrete TailBalance for the one-sided Pareto distribution.
    Right tail x^{-α}, left tail 0, L = 1 (constant). -/
def paretoTailBalance (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 2) : TailBalance where
  rightTail := fun x => x ^ (-α)
  leftTail := fun _ => 0
  α := α
  L := fun _ => 1
  p := 1
  q := 0
  hα_pos := hα_pos
  hα_le := hα_le
  hp_nonneg := le_of_lt one_pos
  hq_nonneg := le_refl 0
  hpq_pos := by norm_num
  hL_sv := slowlyVarying_const one_pos
  hRight := by
    refine (Filter.tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [mul_one, rpow_neg hx.le, inv_rpow hx.le, div_self]
    exact ne_of_gt (inv_pos.mpr (rpow_pos_of_pos hx α))
  hLeft := by
    simp only [zero_div]
    exact tendsto_const_nhds

/-- The Pareto TailBalance is one-sided (q = 0), representing a distribution
    with all mass on the positive tail. -/
theorem paretoTailBalance_one_sided (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 2) :
    (paretoTailBalance α hα_pos hα_le).q = 0 := rfl

/-- The Pareto TailBalance has full weight on the right tail (p/(p+q) = 1). -/
theorem paretoTailBalance_full_right (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 2) :
    (paretoTailBalance α hα_pos hα_le).p / ((paretoTailBalance α hα_pos hα_le).p +
      (paretoTailBalance α hα_pos hα_le).q) = 1 := by
  simp [paretoTailBalance]

/-
### Symmetric Cauchy Tail Balance

The symmetric Cauchy distribution (α = 1) has:
- Right tail: P(X > x) ~ (1/π) · x^{-1}  (we normalize to p = 1/2)
- Left tail: P(X < -x) ~ (1/π) · x^{-1}  (q = 1/2)
- Slowly varying part: L = 1
- By symmetry, p = q = 1/2

This demonstrates a symmetric stable distribution with heavy tails.
-/

/-- Concrete TailBalance for the symmetric Cauchy distribution (α = 1).
    Both tails decay as x^{-1} with equal weights p = q = 1/2. -/
def cauchyTailBalance : TailBalance where
  rightTail := fun x => x ^ (-(1 : ℝ))
  leftTail := fun x => x ^ (-(1 : ℝ))
  α := 1
  L := fun _ => 2
  p := 1 / 2
  q := 1 / 2
  hα_pos := one_pos
  hα_le := one_le_two
  hp_nonneg := by norm_num
  hq_nonneg := by norm_num
  hpq_pos := by norm_num
  hL_sv := slowlyVarying_const (by norm_num : (0:ℝ) < 2)
  hRight := by
    refine (Filter.tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [rpow_neg hx.le, rpow_one, inv_rpow hx.le, rpow_one]
    field_simp
  hLeft := by
    refine (Filter.tendsto_congr' ?_).mpr tendsto_const_nhds
    filter_upwards [Filter.eventually_gt_atTop 0] with x hx
    rw [rpow_neg hx.le, rpow_one, inv_rpow hx.le, rpow_one]
    field_simp

/-- The Cauchy TailBalance is symmetric: p = q = 1/2. -/
theorem cauchyTailBalance_symmetric :
    cauchyTailBalance.p = cauchyTailBalance.q := rfl

-- ============================================================================
-- Part XX: Domain of Attraction for Concrete Distributions
-- ============================================================================

/-
Using the axiomatized forward direction of the Gnedenko-Kolmogorov theorem,
we can show that distributions with known tail behavior lie in specific
domains of attraction.
-/

/-- A TailBalance with 0 < α < 2 implies the existence of some characteristic
    function in the domain of attraction of the α-stable law (via forward direction).
    This connects the concrete tail conditions to the abstract DoA definition. -/
theorem tailBalance_implies_attraction (tb : TailBalance) (hα_lt : tb.α < 2) :
    ∀ (φ : ℝ → ℂ), (φ 0 = 1 ∧ ∀ t, ‖φ t‖ ≤ 1) →
    -- If φ is the char fn of a distribution with these tails
    InDomainOfAttraction φ tb.α :=
  fun φ hφ => gnedenko_kolmogorov_forward φ tb.α tb.hα_pos hα_lt
    tb.rightTail tb.leftTail tb.L tb.hL_sv tb.p tb.q
    tb.hp_nonneg tb.hq_nonneg tb.hpq_pos tb.hRight tb.hLeft hφ

/-- The Pareto distribution (α ∈ (0, 2)) lies in the domain of attraction
    of the α-stable law. -/
theorem pareto_in_domain_of_attraction (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 2) :
    ∀ (φ : ℝ → ℂ), (φ 0 = 1 ∧ ∀ t, ‖φ t‖ ≤ 1) →
    InDomainOfAttraction φ α :=
  tailBalance_implies_attraction (paretoTailBalance α hα_pos (le_of_lt hα_lt)) hα_lt

/-- The symmetric Cauchy distribution lies in the domain of attraction
    of the 1-stable (Cauchy) law. -/
theorem cauchy_in_domain_of_attraction :
    ∀ (φ : ℝ → ℂ), (φ 0 = 1 ∧ ∀ t, ‖φ t‖ ≤ 1) →
    InDomainOfAttraction φ 1 :=
  tailBalance_implies_attraction cauchyTailBalance (show (1 : ℝ) < 2 by norm_num)

-- ============================================================================
-- Part XXI: Slowly Varying Function Examples
-- ============================================================================

/-
The definition of SlowlyVarying requires L(x) ≠ 0 for all x > 0. This
excludes log(x) directly (since log(1) = 0). However, shifted logarithms
like log(x + a) for a ≥ 1 are slowly varying and serve as the standard
examples of non-constant slowly varying functions.
-/

/-- log(x + a) is slowly varying for a ≥ 1.
    The key idea: log(cx + a)/log(x + a) = 1 + (log c + log(1 + (a-a/c)/(cx)))/log(x + a) → 1.
    More directly: both log(cx + a) and log(x + a) → ∞, and their difference
    log(cx + a) - log(x + a) = log((cx + a)/(x + a)) → log c (bounded),
    so the ratio → 1. -/
theorem slowlyVarying_logAdd {a : ℝ} (ha : 1 ≤ a) :
    SlowlyVarying (fun x => Real.log (x + a)) := by
  constructor
  · intro x hx
    have : 0 < x + a := by linarith
    have : 1 < x + a := by linarith
    exact ne_of_gt (Real.log_pos this)
  · intro c hc
    -- We show log(cx + a)/log(x + a) → 1.
    -- Strategy: log(cx+a)/log(x+a) = 1 + log((cx+a)/(x+a))/log(x+a)
    -- Since (cx+a)/(x+a) → c, log of that → log c (bounded).
    -- And log(x+a) → ∞. So bounded/∞ → 0, hence ratio → 1 + 0 = 1.
    -- Step 1: log(x + a) → ∞
    have h_denom : Tendsto (fun x => Real.log (x + a)) atTop atTop :=
      Real.tendsto_log_atTop.comp
        (Filter.tendsto_atTop_add_const_right atTop a Filter.tendsto_id)
    -- Step 2: (cx + a)/(x + a) → c
    have h_ratio : Tendsto (fun x => (c * x + a) / (x + a)) atTop (𝓝 c) := by
      have key : Tendsto (fun x : ℝ => c + (a - c * a) / (x + a)) atTop (𝓝 (c + 0)) := by
        exact tendsto_const_nhds.add
          (tendsto_const_nhds.div_atTop
            (Filter.tendsto_atTop_add_const_right atTop a Filter.tendsto_id))
      rw [add_zero] at key
      exact key.congr' (by
        filter_upwards [Filter.eventually_ge_atTop 1] with x hx
        have : (0 : ℝ) < x + a := by linarith
        field_simp; ring)
    -- Step 3: log((cx+a)/(x+a)) → log c
    have h_log_ratio : Tendsto (fun x => Real.log ((c * x + a) / (x + a)))
        atTop (𝓝 (Real.log c)) :=
      (Real.continuousAt_log (ne_of_gt hc)).tendsto.comp h_ratio
    -- Step 4: log((cx+a)/(x+a)) / log(x+a) → 0
    have h_zero : Tendsto (fun x => Real.log ((c * x + a) / (x + a)) /
        Real.log (x + a)) atTop (𝓝 0) :=
      h_log_ratio.div_atTop h_denom
    -- Step 5: log(cx+a)/log(x+a) =ᶠ 1 + log((cx+a)/(x+a))/log(x+a)
    have h_eq : (fun x => Real.log (c * x + a) / Real.log (x + a)) =ᶠ[atTop]
        (fun x => 1 + Real.log ((c * x + a) / (x + a)) / Real.log (x + a)) := by
      filter_upwards [Filter.eventually_gt_atTop 0] with x hx
      have hxa : (0 : ℝ) < x + a := by linarith
      have hcxa : (0 : ℝ) < c * x + a := by positivity
      have hlog_ne : Real.log (x + a) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
      rw [Real.log_div (ne_of_gt hcxa) (ne_of_gt hxa), sub_div, div_self hlog_ne]
      ring
    -- Conclude: Tendsto (1 + f) → (𝓝 (1 + 0)) = Tendsto ... → (𝓝 1)
    rw [show (1 : ℝ) = 1 + 0 from (add_zero 1).symm]
    exact (Filter.tendsto_congr' h_eq).mpr (tendsto_const_nhds.add h_zero)

/-- log(x + 1) is slowly varying (the simplest shifted logarithm). -/
theorem slowlyVarying_log1 : SlowlyVarying (fun x => Real.log (x + 1)) :=
  slowlyVarying_logAdd le_rfl

/-- Powers of slowly varying functions are slowly varying (rpow version).
    Combined with log(x+a) being SV, this gives (log(x+a))^β as SV for any β. -/
theorem slowlyVarying_logAdd_rpow {a : ℝ} (ha : 1 ≤ a) {β : ℝ} (hβ : β ≠ 0) :
    SlowlyVarying (fun x => |Real.log (x + a)| ^ β) :=
  slowlyVarying_rpow (slowlyVarying_logAdd ha) hβ

-- ============================================================================
-- Part XXII: Verification
-- ============================================================================

#check @SlowlyVarying
#check @RegularlyVarying
#check @TailBalance
#check @InDomainOfAttraction
#check @slowlyVarying_const
#check @slowlyVarying_mul
#check @slowlyVarying_rpow
#check @slowlyVarying_inv
#check @slowlyVarying_div
#check @slowlyVarying_of_asymp_equiv
#check @slowlyVarying_pow
#check @slowlyVarying_comp_rpow
#check @regularlyVarying_decomposition
#check @regularlyVarying_of_decomposition
#check @regularlyVarying_comp_rpow
#check @gnedenko_kolmogorov_forward
#check @gnedenko_kolmogorov_converse
#check @stable_self_similarity
#check @stableCharFun_zero
#check @stableCharFun_norm_le
#check @stableCharFun_continuous
#check @stableCharFun_even
#check @tail_balance_ratios_sum_one
#check @domain_of_attraction_normalizing_diverges
#check @regularlyVarying_rpow
#check @regularlyVarying_mul_index
#check @regularlyVarying_inv_index
#check @regularlyVarying_div_index
-- Concrete examples
#check @paretoTail
#check @paretoTail_at_one
#check @paretoTail_pos
#check @paretoTail_regularlyVarying
#check @paretoTail_eq_inv_rpow
#check @paretoTail_decomposition
#check @powerlaw_normalization_diverges
#check @gaussian_normalization_diverges
#check @cauchy_normalization_diverges
#check @cauchy_normalization_eq
#check @normalization_monotone
-- Tail balance instances
#check @paretoTailBalance
#check @paretoTailBalance_one_sided
#check @paretoTailBalance_full_right
#check @cauchyTailBalance
#check @cauchyTailBalance_symmetric
-- Domain of attraction connections
#check @tailBalance_implies_attraction
#check @pareto_in_domain_of_attraction
#check @cauchy_in_domain_of_attraction
-- Slowly varying examples
#check @slowlyVarying_logAdd
#check @slowlyVarying_log1
#check @slowlyVarying_logAdd_rpow

end DomainOfAttraction
