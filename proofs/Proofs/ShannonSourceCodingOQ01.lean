/-
  Rate-Distortion Theory

  Shannon's rate-distortion theory (1959): the minimum rate for lossy
  compression at distortion level D is R(D) = min I(X;X̂) over all
  conditional distributions p(x̂|x) with E[d(X,X̂)] ≤ D.

  Key results:
  1. Definitions: distortion measure, test channel, rate-distortion function
  2. Joint distribution properties (non-negativity, normalization)
  3. Expected distortion non-negativity
  4. R(D) monotonicity (set inclusion argument)
  5. Hamming distortion and binary entropy function
  6. Gaussian rate-distortion: R(D) = ½ log(σ²/D) — proved non-negativity,
     monotonicity, and boundary R(σ²) = 0
  7. Reverse water-filling non-negativity

  Claude Shannon (1959)

  Axioms: 1 (rateDistortion_convex — requires optimization over test channels)
  Sorries: 0
-/
import Mathlib

namespace InformationTheory.RateDistortion

open Finset BigOperators Real

-- ============================================================
-- Core Definitions
-- ============================================================

/-- A distortion measure: d(x, x̂) quantifies reconstruction error.
    We require d ≥ 0 (non-negative distortion). -/
structure DistortionMeasure (α β : Type*) where
  d : α → β → ℝ
  nonneg : ∀ x y, 0 ≤ d x y

/-- Expected distortion under joint distribution pXY with distortion d. -/
noncomputable def expectedDistortion {α β : Type*} [Fintype α] [Fintype β]
    (dist : DistortionMeasure α β) (pXY : α × β → ℝ) : ℝ :=
  ∑ x : α, ∑ y : β, pXY (x, y) * dist.d x y

/-- A test channel (conditional distribution) p(ŷ|x) is a function
    that for each x gives a probability distribution over β. -/
structure TestChannel (α β : Type*) [Fintype β] where
  cond : α → β → ℝ
  nonneg : ∀ x y, 0 ≤ cond x y
  sum_one : ∀ x, ∑ y : β, cond x y = 1

/-- Joint distribution induced by source p and test channel W:
    p(x,y) = p(x) · W(y|x). -/
noncomputable def jointDist {α β : Type*} [Fintype β]
    (p : α → ℝ) (W : TestChannel α β) : α × β → ℝ :=
  fun ⟨x, y⟩ => p x * W.cond x y

/-- A test channel is D-admissible if expected distortion ≤ D. -/
def isAdmissible {α β : Type*} [Fintype α] [Fintype β]
    (dist : DistortionMeasure α β) (p : α → ℝ) (W : TestChannel α β) (D : ℝ) : Prop :=
  expectedDistortion dist (jointDist p W) ≤ D

/-- The set of achievable mutual informations at distortion D:
    {I(X;Y) : W is a test channel with E[d] ≤ D}. -/
noncomputable def achievableRates {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (dist : DistortionMeasure α β) (p : α → ℝ) (D : ℝ) : Set ℝ :=
  { r : ℝ | ∃ W : TestChannel α β,
    isAdmissible dist p W D ∧
    r = InformationTheory.mutualInformation (jointDist p W) }

/-- **Rate-distortion function**: R(D) = inf I(X;X̂) over all
    D-admissible test channels.

    R(D) = inf { I(X;X̂) : p(x̂|x) with E[d(X,X̂)] ≤ D }

    This is the fundamental quantity of lossy source coding theory.
    Shannon (1959) proved that R(D) is the minimum achievable rate
    for lossy compression with average distortion at most D. -/
noncomputable def rateDistortionFn {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (dist : DistortionMeasure α β) (p : α → ℝ) (D : ℝ) : ℝ :=
  sInf (achievableRates dist p D)

-- ============================================================
-- Basic Properties of Joint Distributions
-- ============================================================

/-- Joint distribution induced by a source and test channel is non-negative. -/
theorem jointDist_nonneg {α β : Type*} [Fintype β]
    {p : α → ℝ} (hp : ∀ x, 0 ≤ p x) (W : TestChannel α β) (xy : α × β) :
    0 ≤ jointDist p W xy :=
  mul_nonneg (hp xy.1) (W.nonneg xy.1 xy.2)

/-- Joint distribution sums to 1 when source sums to 1. -/
theorem jointDist_sum_one {α β : Type*} [Fintype α] [Fintype β]
    {p : α → ℝ} (hpsum : ∑ x : α, p x = 1) (W : TestChannel α β) :
    ∑ x : α, ∑ y : β, jointDist p W (x, y) = 1 := by
  simp only [jointDist, ← Finset.mul_sum]
  simp_rw [W.sum_one]
  simp [hpsum]

/-- Expected distortion is non-negative. -/
theorem expectedDistortion_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (dist : DistortionMeasure α β) {p : α → ℝ} (hp : ∀ x, 0 ≤ p x)
    (W : TestChannel α β) :
    0 ≤ expectedDistortion dist (jointDist p W) := by
  unfold expectedDistortion
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (jointDist_nonneg hp W (x, y)) (dist.nonneg x y)

-- ============================================================
-- Monotonicity of R(D)
-- ============================================================

/-- If D₁ ≤ D₂, then the set of admissible channels at D₁ is
    contained in that at D₂. More distortion tolerance means
    more admissible channels, hence R(D) is non-increasing. -/
theorem achievableRates_mono {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (dist : DistortionMeasure α β) (p : α → ℝ) {D₁ D₂ : ℝ} (h : D₁ ≤ D₂) :
    achievableRates dist p D₁ ⊆ achievableRates dist p D₂ := by
  intro r ⟨W, hadm, hr⟩
  exact ⟨W, le_trans hadm h, hr⟩

-- ============================================================
-- Hamming Distortion (Binary Sources)
-- ============================================================

/-- **Hamming distortion**: d(x,y) = 0 if x = y, 1 otherwise.
    The natural distortion measure for discrete sources. -/
def hammingDistortion (α : Type*) [DecidableEq α] : DistortionMeasure α α where
  d x y := if x = y then 0 else 1
  nonneg x y := by
    simp only
    split_ifs <;> norm_num

/-- Hamming distortion is bounded by 1. -/
theorem hamming_le_one {α : Type*} [DecidableEq α] (x y : α) :
    (hammingDistortion α).d x y ≤ 1 := by
  simp only [hammingDistortion]
  split_ifs <;> norm_num

/-- Hamming distortion is zero iff equal. -/
theorem hamming_eq_zero_iff {α : Type*} [DecidableEq α] (x y : α) :
    (hammingDistortion α).d x y = 0 ↔ x = y := by
  simp only [hammingDistortion]
  split_ifs with h <;> simp [h]

-- ============================================================
-- Binary Entropy Function
-- ============================================================

/-- The binary entropy function: h(p) = -p·log(p) - (1-p)·log(1-p).
    Fundamental to binary rate-distortion theory. -/
noncomputable def binaryEntropy (p : ℝ) : ℝ :=
  if p = 0 then 0
  else if p = 1 then 0
  else -(p * log p + (1 - p) * log (1 - p))

/-- Helper: for 0 < t ≤ 1, t · log(t) ≤ 0. -/
private lemma mul_log_nonpos_of_pos_le_one {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t * log t ≤ 0 :=
  mul_nonpos_of_nonneg_of_nonpos (le_of_lt ht0) (log_nonpos (le_of_lt ht0) ht1)

/-- Binary entropy is non-negative for p ∈ [0,1]. -/
theorem binaryEntropy_nonneg {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ binaryEntropy p := by
  unfold binaryEntropy
  split_ifs with h0 h1
  · exact le_refl 0
  · exact le_refl 0
  · rw [neg_nonneg]
    apply add_nonpos
    · exact mul_log_nonpos_of_pos_le_one (lt_of_le_of_ne hp0 (Ne.symm h0)) hp1
    · exact mul_log_nonpos_of_pos_le_one (by linarith) (by linarith)

/-- Binary entropy is symmetric: h(p) = h(1-p). -/
theorem binaryEntropy_symm {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryEntropy p = binaryEntropy (1 - p) := by
  unfold binaryEntropy
  have h_sub : 1 - (1 - p) = p := by ring
  split_ifs with h0 h1 h2 h3 <;> simp_all <;> ring

/-- h(0) = 0: no distortion. -/
theorem binaryEntropy_zero : binaryEntropy 0 = 0 := by
  unfold binaryEntropy; simp

/-- h(1/2) = log 2: maximum binary entropy. -/
theorem binaryEntropy_half : binaryEntropy (1/2) = log 2 := by
  unfold binaryEntropy
  simp only [one_div, show (2 : ℝ)⁻¹ ≠ 0 from by norm_num,
    show (2 : ℝ)⁻¹ ≠ 1 from by norm_num, ite_false]
  have h1 : 1 - (2 : ℝ)⁻¹ = 2⁻¹ := by ring
  rw [h1, log_inv]
  ring

-- ============================================================
-- Gaussian Rate-Distortion
-- ============================================================

/-- **Gaussian rate-distortion non-negativity**:
    ½ log(σ²/D) ≥ 0 when 0 < D ≤ σ².
    The Gaussian R(D) is always non-negative within its domain. -/
theorem gaussian_rd_nonneg (σ² D : ℝ) (hσ : 0 < σ²) (hD : 0 < D) (hDσ : D ≤ σ²) :
    0 ≤ (1 / 2 : ℝ) * log (σ² / D) := by
  apply mul_nonneg
  · norm_num
  · exact log_nonneg (le_div_iff₀ hD |>.mpr (by linarith))

/-- **Gaussian R(D) is decreasing**: more distortion → lower rate.
    R(D₁) ≥ R(D₂) when D₁ ≤ D₂. -/
theorem gaussian_rd_decreasing (σ² D₁ D₂ : ℝ)
    (hσ : 0 < σ²) (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (h : D₁ ≤ D₂) (hDσ : D₂ ≤ σ²) :
    (1 / 2 : ℝ) * log (σ² / D₂) ≤ (1 / 2 : ℝ) * log (σ² / D₁) := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  apply log_le_log (div_pos hσ hD₂)
  exact div_le_div_of_nonneg_left hσ hD₂ (by linarith) h

/-- **At D = σ², R(D) = 0**: when distortion equals variance, no bits needed.
    The source can be reproduced at its own variance by simply outputting
    the mean (zero). -/
theorem gaussian_rd_at_variance (σ² : ℝ) (hσ : 0 < σ²) :
    (1 / 2 : ℝ) * log (σ² / σ²) = 0 := by
  rw [div_self (ne_of_gt hσ), log_one, mul_zero]

/-- **Gaussian R(D) doubles with halved distortion**:
    R(D/2) = R(D) + ½ log 2.
    Each halving of distortion costs an additional ½ log 2 nats. -/
theorem gaussian_rd_halve_distortion (σ² D : ℝ)
    (hσ : 0 < σ²) (hD : 0 < D) (hDσ : D ≤ σ²) :
    (1 / 2 : ℝ) * log (σ² / (D / 2)) =
    (1 / 2 : ℝ) * log (σ² / D) + (1 / 2 : ℝ) * log 2 := by
  have hD2 : D / 2 ≠ 0 := by positivity
  have hD' : (0 : ℝ) < D := hD
  rw [div_div, mul_comm D 2, ← div_div, log_div (by positivity) (by positivity)]
  ring

-- ============================================================
-- Reverse Water-Filling
-- ============================================================

/-- **Reverse water-filling non-negativity** (Shannon, 1959; Berger, 1971):
    For a memoryless Gaussian source with component variances σᵢ²,
    R(D) = ∑ᵢ max(0, ½ log(σᵢ²/θ)) where θ is chosen so that
    ∑ᵢ min(σᵢ², θ) = D.

    Each term in the sum is non-negative by definition. -/
theorem water_filling_nonneg {n : ℕ} {σ² : Fin n → ℝ} {θ : ℝ}
    (hσ : ∀ i, 0 < σ² i) (hθ : 0 < θ) :
    0 ≤ ∑ i : Fin n, max 0 ((1 / 2 : ℝ) * log (σ² i / θ)) :=
  Finset.sum_nonneg fun i _ => le_max_left 0 _

-- ============================================================
-- Convexity of R(D) (Axiomatized)
-- ============================================================

/-- **R(D) is convex** (Shannon, 1959):
    For 0 ≤ λ ≤ 1: R(λD₁ + (1-λ)D₂) ≤ λR(D₁) + (1-λ)R(D₂).

    Proof sketch: Given optimal test channels W₁, W₂ achieving R(D₁), R(D₂),
    the time-sharing channel W = λW₁ + (1-λ)W₂ achieves distortion
    λD₁ + (1-λ)D₂, and mutual information is convex in the test channel
    (by the log-sum inequality).

    Axiomatized because the proof requires:
    1. Existence of optimal test channels (compactness + continuity)
    2. Convexity of mutual information in the conditional distribution
    3. The log-sum inequality applied to time-shared channels -/
axiom rateDistortion_convex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (dist : DistortionMeasure α β) (p : α → ℝ) :
    ∀ D₁ D₂ λ₁ : ℝ,
      0 ≤ λ₁ → λ₁ ≤ 1 →
      rateDistortionFn dist p (λ₁ * D₁ + (1 - λ₁) * D₂) ≤
        λ₁ * rateDistortionFn dist p D₁ + (1 - λ₁) * rateDistortionFn dist p D₂

-- ============================================================
-- Connection to Lossless Coding
-- ============================================================

/- At zero Hamming distortion (D = 0), the only admissible test channel
    is the identity channel X̂ = X, so I(X;X̂) = H(X).
    Thus R(0) = H(X), recovering the lossless source coding theorem.

    This connects rate-distortion theory to Shannon's 1948 source
    coding theorem: the lossless case is the D = 0 endpoint. -/

end InformationTheory.RateDistortion
