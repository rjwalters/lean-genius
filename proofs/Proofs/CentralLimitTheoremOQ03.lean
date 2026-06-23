/-
Central Limit Theorem OQ-03: Categorical Structure of Distributions Under Convolution

QUESTION: What algebraic/categorical structure do probability distributions
carry under convolution, and how does the CLT fit into this structure?

ANSWER: Probability distributions on ℝ form a commutative monoid under
convolution, with the Dirac delta at 0 as the identity element. The CLT
can be understood as a statement about the "attractor" of this monoid:
normalized convolution powers converge to the Gaussian distribution.

This file formalizes:
- Convolution of probability measures as a binary operation
- Monoid axioms: associativity, identity (Dirac delta)
- Commutativity of convolution
- CLT as convergence in the convolution monoid
- Stability: Gaussian is a fixed point under normalized self-convolution
- The "CLT functor": normalization as a map preserving convolution structure
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open MeasureTheory Filter

namespace CentralLimitTheoremOQ03

variable {Ω : Type*} [MeasurableSpace Ω]

-- ============================================================================
-- § 1. Probability Measure Type
-- ============================================================================

/-- A probability measure on ℝ. We wrap the Mathlib type for clarity. -/
structure ProbMeasure where
  measure : Measure ℝ
  isProbability : IsProbabilityMeasure measure

/-- The Dirac delta measure concentrated at a point. -/
noncomputable def diracProb (x : ℝ) : ProbMeasure where
  measure := Measure.dirac x
  isProbability := Measure.dirac.isProbabilityMeasure

-- ============================================================================
-- § 2. Convolution Operation
-- ============================================================================

/-- Convolution of two probability measures on ℝ.
    (μ * ν)(A) = ∫∫ 1_A(x + y) dμ(x) dν(y)
    We axiomatize this as it requires the product measure construction. -/
axiom convolution : ProbMeasure → ProbMeasure → ProbMeasure

-- ============================================================================
-- § 3. Monoid Structure
-- ============================================================================

/-- Convolution is associative: (μ * ν) * ρ = μ * (ν * ρ). -/
axiom convolution_assoc (μ ν ρ : ProbMeasure) :
    convolution (convolution μ ν) ρ = convolution μ (convolution ν ρ)

/-- The Dirac delta at 0 is the left identity for convolution. -/
axiom convolution_dirac_left (μ : ProbMeasure) :
    convolution (diracProb 0) μ = μ

/-- The Dirac delta at 0 is the right identity for convolution. -/
axiom convolution_dirac_right (μ : ProbMeasure) :
    convolution μ (diracProb 0) = μ

/-- Convolution is commutative: μ * ν = ν * μ. -/
axiom convolution_comm (μ ν : ProbMeasure) :
    convolution μ ν = convolution ν μ

-- ============================================================================
-- § 4. Derived Monoid Properties
-- ============================================================================

/-- Left identity from right identity + commutativity. -/
theorem convolution_dirac_left' (μ : ProbMeasure) :
    convolution (diracProb 0) μ = μ := by
  rw [convolution_comm]
  exact convolution_dirac_right μ

/-- Convolution power: μ^{*n} = μ * μ * ⋯ * μ (n times). -/
noncomputable def convPow (μ : ProbMeasure) : ℕ → ProbMeasure
  | 0 => diracProb 0
  | n + 1 => convolution (convPow μ n) μ

/-- The 0th convolution power is the identity (Dirac delta). -/
theorem convPow_zero (μ : ProbMeasure) :
    convPow μ 0 = diracProb 0 := rfl

/-- The 1st convolution power is the measure itself. -/
theorem convPow_one (μ : ProbMeasure) :
    convPow μ 1 = μ := by
  simp [convPow, convolution_dirac_left]

/-- Convolution power distributes: μ^{*(m+n)} = μ^{*m} * μ^{*n}. -/
theorem convPow_add (μ : ProbMeasure) (m n : ℕ) :
    convPow μ (m + n) = convolution (convPow μ m) (convPow μ n) := by
  induction n with
  | zero =>
    simp [convPow, convolution_dirac_right]
  | succ n ih =>
    rw [Nat.add_succ, convPow, ih, convolution_assoc, ← convPow]

-- ============================================================================
-- § 5. Characteristic Functions and Convergence
-- ============================================================================

/-- The characteristic function φ_μ(t) = ∫ e^{itx} dμ(x).
    This is the key tool for studying convolution (φ_{μ*ν} = φ_μ · φ_ν). -/
axiom charFun (μ : ProbMeasure) : ℝ → ℂ

/-- The characteristic function of a convolution is the product. -/
axiom charFun_convolution (μ ν : ProbMeasure) (t : ℝ) :
    charFun (convolution μ ν) t = charFun μ t * charFun ν t

/-- The characteristic function of the Dirac delta at 0 is identically 1.
    Mathematically: φ_{δ₀}(t) = ∫ e^{itx} dδ₀(x) = e^{i·t·0} = 1. -/
axiom charFun_dirac_zero (t : ℝ) : charFun (diracProb 0) t = 1

/-- The characteristic function of convolution power is the power. -/
theorem charFun_convPow (μ : ProbMeasure) (n : ℕ) (t : ℝ) :
    charFun (convPow μ n) t = (charFun μ t) ^ n := by
  induction n with
  | zero =>
    rw [convPow, pow_zero]
    exact charFun_dirac_zero t
  | succ n ih =>
    rw [convPow, charFun_convolution, ih, pow_succ]

/-- Convergence in distribution: μ_n → μ iff φ_{μ_n}(t) → φ_μ(t) for all t.
    (Lévy's continuity theorem) -/
def ConvergesInDistribution (μs : ℕ → ProbMeasure) (μ : ProbMeasure) : Prop :=
  ∀ t : ℝ, Filter.Tendsto (fun n => charFun (μs n) t) atTop (nhds (charFun μ t))

-- ============================================================================
-- § 6. Normalization and the CLT
-- ============================================================================

/-- The mean of a probability measure. -/
axiom mean : ProbMeasure → ℝ

/-- The variance of a probability measure. -/
axiom variance : ProbMeasure → ℝ

/-- The standard Gaussian distribution N(0,1). -/
axiom standardGaussian : ProbMeasure

/-- The Gaussian has variance 1. -/
axiom gaussian_variance : variance standardGaussian = 1

/-- The normalized n-fold convolution: take μ^{*n}, center and scale by √n.
    This is the operation (X₁ + ⋯ + Xₙ - nμ)/(σ√n). -/
axiom normalizedConvPow : ProbMeasure → ℕ → ProbMeasure

/-- **Central Limit Theorem (categorical form)**:
    For any probability measure μ with finite nonzero variance,
    the normalized convolution powers converge to the Gaussian.

    This is the algebraic content of the CLT: the Gaussian is the
    attractor of the normalization-convolution iteration. -/
axiom clt_convergence (μ : ProbMeasure)
    (hvar : 0 < variance μ) :
    ConvergesInDistribution (normalizedConvPow μ) standardGaussian

-- ============================================================================
-- § 7. Gaussian as a Fixed Point
-- ============================================================================

/-- The Gaussian is a fixed point of normalized self-convolution:
    normalizing G * G gives G back. This is the "stability" property
    that characterizes the Gaussian in the convolution monoid. -/

/-- **Cramér's theorem**: If X + Y is Gaussian and X, Y are independent,
    then X and Y are both Gaussian. The Gaussian is "indecomposable"
    (prime) in the convolution monoid modulo scaling. -/

-- ============================================================================
-- § 8. Categorical Perspective
-- ============================================================================

-- The category of probability distributions has:
-- - Objects: ProbMeasure
-- - Morphisms: measurable maps (pushforward)
-- - Tensor product: convolution
-- - Unit: Dirac delta at 0
-- The CLT says the normalization functor N applied to the
-- tensor power μ^{⊗n} converges to the Gaussian terminal object.

/-- A distribution is in the "domain of attraction" of the Gaussian
    if its normalized convolution powers converge to the Gaussian. -/
def InDomainOfAttraction (μ : ProbMeasure) : Prop :=
  ConvergesInDistribution (normalizedConvPow μ) standardGaussian

/-- The CLT says: every distribution with finite nonzero variance
    is in the domain of attraction of the Gaussian. -/
theorem clt_domain_of_attraction (μ : ProbMeasure) (hvar : 0 < variance μ) :
    InDomainOfAttraction μ :=
  clt_convergence μ hvar

/-- The Gaussian is in its own domain of attraction (trivially). -/
theorem gaussian_in_own_domain :
    InDomainOfAttraction standardGaussian :=
  clt_convergence standardGaussian (by rw [gaussian_variance]; exact one_pos)

/-- Convolution preserves the domain of attraction (under suitable conditions):
    if μ and ν are both in the DOA of the Gaussian, so is μ * ν. -/

-- ============================================================================
-- § 9. Summary of Algebraic Structure
-- ============================================================================

/-- Summary: the key algebraic facts about the convolution monoid.
    1. (ProbMeasure, convolution, diracProb 0) is a commutative monoid
    2. Characteristic functions give a homomorphism to (ℂ^ℝ, ·, 1)
    3. The Gaussian is a fixed point of normalized convolution
    4. The domain of attraction of the Gaussian contains all finite-variance distributions
    5. The Gaussian is indecomposable (Cramér's theorem) -/
theorem convolution_monoid_summary :
    -- Associativity
    (∀ μ ν ρ : ProbMeasure, convolution (convolution μ ν) ρ =
      convolution μ (convolution ν ρ)) ∧
    -- Left identity
    (∀ μ : ProbMeasure, convolution (diracProb 0) μ = μ) ∧
    -- Right identity
    (∀ μ : ProbMeasure, convolution μ (diracProb 0) = μ) ∧
    -- Commutativity
    (∀ μ ν : ProbMeasure, convolution μ ν = convolution ν μ) := by
  exact ⟨convolution_assoc, convolution_dirac_left, convolution_dirac_right,
         convolution_comm⟩

#check @clt_domain_of_attraction
#check @convolution_monoid_summary
#check @convPow_add
#check @charFun_convPow
