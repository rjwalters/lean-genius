/-
Infinitely Divisible Distributions in Lean

Open Question (central-limit-theorem-oq-03-oq-02):
"Can infinitely divisible distributions and the Lévy-Khintchine theorem
be formalized in Lean 4?"

A probability distribution μ is infinitely divisible if for every n ≥ 1,
there exists Q_n such that Q_n^{*n} = μ (n-fold convolution).
Examples: Gaussian, Poisson, Cauchy, Gamma, all stable distributions.
The Lévy-Khintchine theorem classifies all ID distributions via a triple
(b, σ², ν): drift + diffusion + Lévy jump measure.

This file formalizes:
1. Infrastructure: convolution monoid on probability measures
2. Key lemma: (μ*ν)^{*n} = μ^{*n} * ν^{*n} (convPow_dist, proved)
3. Definition: IsInfDivisible
4. Proved: δ₀ is ID; ID closed under convolution; ID closed under convPow
5. Axiomatized: Gaussian is ID; Lévy-Khintchine theorem
6. Corollaries from Lévy-Khintchine
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open MeasureTheory

namespace CentralLimitTheoremOQ03OQ02

-- ============================================================================
-- § 1. Probability Measure Infrastructure
-- ============================================================================

/-- A probability measure on ℝ. -/
structure ProbMeasure where
  measure : Measure ℝ
  isProbability : IsProbabilityMeasure measure

/-- The Dirac delta at a point. -/
noncomputable def diracProb (x : ℝ) : ProbMeasure where
  measure := Measure.dirac x
  isProbability := inferInstance

/-- Convolution of probability measures: distribution of X + Y for independent X ~ μ, Y ~ ν.
Axiomatized — the construction requires product measure and push-forward. -/
axiom convolution : ProbMeasure → ProbMeasure → ProbMeasure

axiom convolution_assoc (μ ν ρ : ProbMeasure) :
    convolution (convolution μ ν) ρ = convolution μ (convolution ν ρ)

axiom convolution_comm (μ ν : ProbMeasure) :
    convolution μ ν = convolution ν μ

axiom convolution_dirac_right (μ : ProbMeasure) :
    convolution μ (diracProb 0) = μ

theorem convolution_dirac_left (μ : ProbMeasure) :
    convolution (diracProb 0) μ = μ := by
  rw [convolution_comm]; exact convolution_dirac_right μ

/-- Convolution power: μ^{*n} = μ * ⋯ * μ (n times); μ^{*0} = δ₀. -/
noncomputable def convPow (μ : ProbMeasure) : ℕ → ProbMeasure
  | 0 => diracProb 0
  | n + 1 => convolution (convPow μ n) μ

@[simp] theorem convPow_zero (μ : ProbMeasure) : convPow μ 0 = diracProb 0 := rfl
@[simp] theorem convPow_succ (μ : ProbMeasure) (n : ℕ) :
    convPow μ (n + 1) = convolution (convPow μ n) μ := rfl

theorem convPow_one (μ : ProbMeasure) : convPow μ 1 = μ := by
  simp [convolution_dirac_left]

/-- μ^{*(m+n)} = μ^{*m} * μ^{*n}. -/
theorem convPow_add (μ : ProbMeasure) (m n : ℕ) :
    convPow μ (m + n) = convolution (convPow μ m) (convPow μ n) := by
  induction n with
  | zero => simp [convolution_dirac_right]
  | succ n ih =>
    rw [Nat.add_succ, convPow_succ, ih, convolution_assoc, ← convPow_succ]

-- ============================================================================
-- § 2. The Interchange Law and Distributivity
-- ============================================================================

/-- **Interchange law**: conv(conv(A,B), conv(C,D)) = conv(conv(A,C), conv(B,D)).
Proved by repeated application of associativity and commutativity. -/
lemma convolution_interchange (A B C D : ProbMeasure) :
    convolution (convolution A B) (convolution C D) =
    convolution (convolution A C) (convolution B D) :=
  calc convolution (convolution A B) (convolution C D)
      = convolution A (convolution B (convolution C D)) := convolution_assoc A B _
    _ = convolution A (convolution (convolution B C) D) := by rw [convolution_assoc B C D]
    _ = convolution A (convolution (convolution C B) D) := by rw [convolution_comm B C]
    _ = convolution A (convolution C (convolution B D)) := by rw [convolution_assoc C B D]
    _ = convolution (convolution A C) (convolution B D) := (convolution_assoc A C _).symm

/-- **(μ * ν)^{*n} = μ^{*n} * ν^{*n}**: convolution power distributes over convolution.
This is the key lemma for proving closure of infinite divisibility under convolution. -/
theorem convPow_dist (μ ν : ProbMeasure) (n : ℕ) :
    convPow (convolution μ ν) n = convolution (convPow μ n) (convPow ν n) := by
  induction n with
  | zero =>
    simp only [convPow_zero]
    exact (convolution_dirac_right (diracProb 0)).symm
  | succ n ih =>
    simp only [convPow_succ, ih]
    exact convolution_interchange (convPow μ n) (convPow ν n) μ ν

/-- (μ^{*n})^{*m} = μ^{*(n*m)}: convolution power of convolution power. -/
theorem convPow_mul (μ : ProbMeasure) (n m : ℕ) :
    convPow (convPow μ n) m = convPow μ (n * m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [convPow_succ, ih, Nat.mul_succ, ← convPow_add]

-- ============================================================================
-- § 3. Characteristic Functions
-- ============================================================================

/-- The characteristic function φ_μ(t) = E[e^{itX}] where X ~ μ.
Axiomatized — requires complex-valued integration. -/
axiom charFun : ProbMeasure → ℝ → ℂ

/-- φ_{μ*ν}(t) = φ_μ(t) · φ_ν(t). -/
axiom charFun_convolution (μ ν : ProbMeasure) (t : ℝ) :
    charFun (convolution μ ν) t = charFun μ t * charFun ν t

/-- φ_{δ₀}(t) = 1. -/
axiom charFun_dirac_zero (t : ℝ) : charFun (diracProb 0) t = 1

/-- φ_{μ^{*n}}(t) = φ_μ(t)^n. -/
theorem charFun_convPow (μ : ProbMeasure) (n : ℕ) (t : ℝ) :
    charFun (convPow μ n) t = (charFun μ t) ^ n := by
  induction n with
  | zero => simp [charFun_dirac_zero]
  | succ n ih =>
    simp only [convPow_succ, charFun_convolution, ih]
    ring

-- ============================================================================
-- § 4. Infinite Divisibility
-- ============================================================================

/-- A distribution μ is **infinitely divisible** if for every n ≥ 1,
μ has a convolution n-th root: ∃ ν, ν^{*n} = μ.

The name "infinitely divisible" reflects that μ can be "split into n identical
independent pieces" for any n. -/
def IsInfDivisible (μ : ProbMeasure) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : ProbMeasure, convPow ν n = μ

-- ============================================================================
-- § 5. Examples
-- ============================================================================

/-- **δ₀ is infinitely divisible**: δ₀^{*n} = δ₀ for all n ≥ 1,
so δ₀ is its own convolution root of every order. -/
theorem infDivisible_dirac : IsInfDivisible (diracProb 0) := by
  intro n hn
  refine ⟨diracProb 0, ?_⟩
  induction n with
  | zero => exact absurd hn (lt_irrefl 0)
  | succ n ih =>
    simp only [convPow_succ]
    by_cases h : n = 0
    · subst h; simp [convPow_zero, convolution_dirac_right]
    · rw [ih (Nat.pos_of_ne_zero h)]; exact convolution_dirac_right _

/-- **The standard Gaussian N(0,1) is infinitely divisible**.
The n-th root of N(0,1) is N(0,1/n): its characteristic function φ(t) = e^{-t²/2}
satisfies (e^{-t²/(2n)})^n = e^{-t²/2}. Axiomatized — needs Gaussian convolution theory. -/
axiom standardGaussian : ProbMeasure
axiom standardGaussian_infDivisible : IsInfDivisible standardGaussian

-- ============================================================================
-- § 6. Closure Properties (proved)
-- ============================================================================

/-- **Closure under convolution** (proved from definitions):
If μ and ν are infinitely divisible, so is μ * ν.

Proof: Given n, let μ_n (resp. ν_n) be the n-th convolution root of μ (resp. ν).
Then (μ_n * ν_n)^{*n} = μ_n^{*n} * ν_n^{*n} = μ * ν by `convPow_dist`. -/
theorem infDivisible_convolution {μ ν : ProbMeasure}
    (hμ : IsInfDivisible μ) (hν : IsInfDivisible ν) :
    IsInfDivisible (convolution μ ν) := by
  intro n hn
  obtain ⟨μ_n, hμ_n⟩ := hμ n hn
  obtain ⟨ν_n, hν_n⟩ := hν n hn
  exact ⟨convolution μ_n ν_n, by rw [convPow_dist, hμ_n, hν_n]⟩

/-- **Closure under convolution powers** (proved from definitions):
If μ is infinitely divisible, so is every convolution power μ^{*n}.

Proof: For the k-th root of μ^{*n}, let ρ be the k-th root of μ.
Then (ρ^{*n})^{*k} = ρ^{*(n*k)} = (ρ^{*k})^{*n} = μ^{*n}. -/
theorem infDivisible_convPow {μ : ProbMeasure} (hμ : IsInfDivisible μ) (n : ℕ) :
    IsInfDivisible (convPow μ n) := by
  intro k hk
  by_cases hn : n = 0
  · -- convPow μ 0 = δ₀, which is ID
    subst hn; simp only [convPow_zero]
    exact infDivisible_dirac k hk
  · -- Take ρ = k-th root of μ, then ρ^{*n} is the k-th root of μ^{*n}
    obtain ⟨ρ, hρ⟩ := hμ k hk
    exact ⟨convPow ρ n, by
      rw [convPow_mul, Nat.mul_comm, ← convPow_mul, hρ]⟩

-- ============================================================================
-- § 7. Lévy-Khintchine Theorem (Axiomatized)
-- ============================================================================

/-- A **Lévy measure** on ℝ: a σ-finite Borel measure on ℝ satisfying
- ν({0}) = 0 (no mass at 0)
- ∫ (1 ∧ |x|²) ν(dx) < ∞ (integrability near 0 and at ∞)

The Lévy measure encodes the jump structure of a Lévy process associated to μ. -/
structure LevyMeasure where
  measure : Measure ℝ
  /-- ν has no mass at 0. -/
  zero_mass : measure {0} = 0
  /-- Integrability condition: the measure is integrable in the sense
  that ∫_{|x|≤1} x² ν(dx) < ∞ and ν({|x|>1}) < ∞. -/
  integrability : ∫⁻ x, ENNReal.ofReal (min 1 (‖(x : ℝ)‖^2)) ∂measure < ⊤

/-- The **Lévy-Khintchine representation** of the characteristic exponent:
Ψ(t; b, σ², ν) = i·b·t - σ²·t²/2 + ∫_{ℝ\{0}} (e^{itx} - 1 - itx·1_{|x|<1}) ν(dx)

Every infinitely divisible distribution μ satisfies φ_μ(t) = exp(Ψ(t; b, σ², ν))
for a unique triple (b, σ², ν). -/
axiom levyKhintchineExponent : ℝ → ℝ → LevyMeasure → ℝ → ℂ

/-- **Lévy-Khintchine Theorem** (axiomatized):
A probability distribution μ is infinitely divisible if and only if
its characteristic function has the form φ_μ(t) = exp(Ψ(t; b, σ², ν))
for some b ∈ ℝ, σ² ≥ 0, and Lévy measure ν. The triple (b, σ², ν) is unique.

Proof requires: Bochner's theorem, compactness of Lévy measures,
and detailed analysis of characteristic functions.
Estimated formalization: ~2000+ lines with full supporting infrastructure. -/
axiom levy_khintchine (μ : ProbMeasure) :
    IsInfDivisible μ ↔
    ∃ (b : ℝ) (σ2 : ℝ) (_ : 0 ≤ σ2) (ν : LevyMeasure),
      ∀ t : ℝ, charFun μ t = Complex.exp (levyKhintchineExponent b σ2 ν t)

-- ============================================================================
-- § 8. Corollaries
-- ============================================================================

/-- Every ID distribution has a Lévy-Khintchine representation. -/
theorem infDivisible_hasLKRep {μ : ProbMeasure} (hμ : IsInfDivisible μ) :
    ∃ (b : ℝ) (σ2 : ℝ) (_ : 0 ≤ σ2) (ν : LevyMeasure),
      ∀ t : ℝ, charFun μ t = Complex.exp (levyKhintchineExponent b σ2 ν t) :=
  (levy_khintchine μ).mp hμ

/-- A distribution with an LK representation is infinitely divisible. -/
theorem lkRep_infDivisible {μ : ProbMeasure} {b σ2 : ℝ} (hσ : 0 ≤ σ2)
    {ν : LevyMeasure}
    (h : ∀ t : ℝ, charFun μ t = Complex.exp (levyKhintchineExponent b σ2 ν t)) :
    IsInfDivisible μ :=
  (levy_khintchine μ).mpr ⟨b, σ2, hσ, ν, h⟩

/-- The ID distributions form a **convolution submonoid** of ProbMeasure. -/
theorem infDivisible_submonoid :
    -- δ₀ is ID (identity of the monoid)
    IsInfDivisible (diracProb 0) ∧
    -- N(0,1) is ID
    IsInfDivisible standardGaussian ∧
    -- Closed under convolution (binary operation)
    (∀ μ ν : ProbMeasure, IsInfDivisible μ → IsInfDivisible ν →
      IsInfDivisible (convolution μ ν)) ∧
    -- Closed under convolution powers
    (∀ μ : ProbMeasure, ∀ n : ℕ, IsInfDivisible μ → IsInfDivisible (convPow μ n)) :=
  ⟨infDivisible_dirac,
   standardGaussian_infDivisible,
   fun _ _ hμ hν => infDivisible_convolution hμ hν,
   fun _ n hμ => infDivisible_convPow hμ n⟩

#check @infDivisible_convolution
#check @infDivisible_convPow
#check @convPow_dist
#check @levy_khintchine
#check @infDivisible_submonoid

end CentralLimitTheoremOQ03OQ02
