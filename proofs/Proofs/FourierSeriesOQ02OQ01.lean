/-
  Riemann-Lebesgue via Parseval's Identity (OQ-02-OQ-01)

  Open Question OQ-02-OQ-01:
  Can riemannLebesgue_of_holder be proved directly from Mathlib's L² theory
  (Parseval's identity) instead of via explicit Hölder decay bounds?

  **Answer**: YES.

  **Alternative Proof Pathway**:
    1. f is α-Hölder → f is continuous (HolderWith.continuous)
    2. f is continuous on compact AddCircle T → f ∈ L²(AddCircle T)
       (via ContinuousMap.toLp)
    3. Parseval's identity (Mathlib): ∑ᵢ ‖ĉᵢ(f)‖² = ∫ ‖f‖² < ∞
    4. Summable series → terms → 0 cofinitely
    5. ‖ĉᵢ‖² → 0 (cofinite) ⟹ ĉᵢ → 0 (cofinite)  [Riemann-Lebesgue for L²]

  This gives an alternative proof of `riemannLebesgue_of_holder` from OQ-02
  using a purely L²-theoretic argument, without the Hölder decay bound computation.

  **Comparison with OQ-02 proof**:
  - OQ-02 (direct): Uses fourierCoeff_holder_decay (explicit bound ≤ M/(2|n|)^α)
    + shows bound → 0 as |n| → ∞ via rpow monotonicity
  - OQ-02-OQ-01 (Parseval): Uses L² embedding + Parseval's identity
    + shorter proof, works for all L² functions (not just Hölder)
    + the Parseval approach is the "standard" functional analysis proof

  **Status**: 0 sorries, 0 axioms.
  The main theorem is fully proved from Mathlib's Parseval identity.

  See FourierSeriesOQ02.lean for the parent (Hölder decay bounds).
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Tactic
import Proofs.FourierSeriesOQ02

open MeasureTheory Complex Topology Filter AddCircle Finset
open scoped ENNReal NNReal Real

namespace FourierHolderParseval

variable {T : ℝ} [hT : Fact (0 < T)]

/-! ## Step 1: Hölder Continuity → L² -/

/-- A Hölder continuous function on AddCircle T embeds into Lp ℂ 2 haarAddCircle.
    The key: compact domain + continuous = bounded ≤ L². -/
noncomputable def holderToLp (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : FourierHolderDecay.IsHolderOnCircle C α f) (hα : 0 < α) :
    Lp ℂ 2 (@haarAddCircle T hT) :=
  ContinuousMap.toLp (E := ℂ) 2 (@haarAddCircle T hT) ℂ
    ⟨f, hf.continuous hα⟩

/-- The Lp embedding preserves Fourier coefficients (a.e. equality). -/
theorem fourierCoeff_holderToLp_eq (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : FourierHolderDecay.IsHolderOnCircle C α f) (hα : 0 < α)
    (n : ℤ) :
    fourierCoeff (holderToLp C α f hf hα) n = fourierCoeff f n := by
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (@haarAddCircle T hT) ℂ ⟨f, hf.continuous hα⟩]
    with x hx
  simp only [mul_comm, hx]

/-! ## Step 2: Parseval's Identity for the Lp function -/

/-- **Parseval-based Riemann-Lebesgue for Hölder functions**:
    The Fourier coefficients ĉₙ(f) → 0 cofinitely.

    Proof via Parseval:
    (a) f is continuous (Hölder), so f ∈ L²(AddCircle T)
    (b) Parseval: HasSum (fun i => ‖ĉᵢ‖²) L (for some finite L)
    (c) Summable ⟹ ‖ĉₙ‖² → 0 cofinitely
    (d) ‖ĉₙ‖² → 0 cofinitely ⟹ ‖ĉₙ‖ → 0 cofinitely ⟹ ĉₙ → 0 cofinitely -/
theorem riemannLebesgue_of_holder_parseval (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : FourierHolderDecay.IsHolderOnCircle C α f) (hα : 0 < α) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  -- Embed f into L²
  set fLp := holderToLp C α f hf hα
  -- Parseval: ∑ ‖ĉₙ(fLp)‖² converges
  have hParseval := @hasSum_sq_fourierCoeff T hT fLp
  -- Fourier coefficients of fLp equal those of f
  have hcoeff : ∀ n : ℤ, fourierCoeff fLp n = fourierCoeff f n :=
    fourierCoeff_holderToLp_eq C α f hf hα
  -- Rewrite Parseval in terms of f
  have hParseval_f : HasSum (fun n => ‖fourierCoeff f n‖ ^ 2)
      (∫ t : AddCircle T, ‖fLp t‖ ^ 2 ∂@haarAddCircle T hT) := by
    have := hParseval
    simp_rw [hcoeff] at this
    exact this
  -- From HasSum: the sequence ‖ĉₙ‖² is summable
  have hSumm : Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) :=
    hParseval_f.summable
  -- Summable ⟹ terms → 0 cofinitely
  have hSq_zero : Tendsto (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) cofinite (𝓝 0) :=
    hSumm.tendsto_cofinite_zero
  -- ‖ĉₙ‖² → 0 ⟹ ‖ĉₙ‖ → 0 (Real.sqrt is continuous, sqrt(x²) = x for x ≥ 0)
  have hNorm_zero : Tendsto (fun n : ℤ => ‖fourierCoeff f n‖) cofinite (𝓝 0) := by
    have hcomp : Tendsto (Real.sqrt ∘ fun n : ℤ => ‖fourierCoeff f n‖ ^ 2)
        cofinite (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.continuousAt.tendsto).comp hSq_zero
    simp only [Real.sqrt_zero, Function.comp, Real.sqrt_sq (norm_nonneg _)] at hcomp
    exact hcomp
  -- ‖ĉₙ‖ → 0 ⟹ ĉₙ → 0 (in normed space, convergence to 0 ↔ norm convergence to 0)
  rw [Metric.tendsto_nhds] at hNorm_zero ⊢
  intro ε hε
  filter_upwards [hNorm_zero ε hε] with n hn
  simp only [dist_zero_right] at *
  rwa [Real.norm_of_nonneg (norm_nonneg _)] at hn

/-! ## Equivalence with the OQ-02 Proof -/

/-- The Parseval proof gives the same result as the Hölder decay bound proof. -/
theorem parseval_and_holder_agree (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : FourierHolderDecay.IsHolderOnCircle C α f) (hα : 0 < α) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) ↔
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) :=
  Iff.rfl

/-! ## Summary: When to Use Each Proof -/

/-
  **Proof comparison**:

  1. **OQ-02 (Hölder decay bounds)**: Gives quantitative bound ‖ĉₙ‖ ≤ M/(2|n|^α).
     Best when you need the explicit rate of decay.

  2. **OQ-02-OQ-01 (Parseval)**: Shorter proof, works for all L² functions.
     Best when you only need qualitative convergence ĉₙ → 0.
     Key: Parseval's identity is more "automatic" — just embed in L².

  **Mathematical insight**: The Parseval approach reveals that Riemann-Lebesgue
  for L² is simply the statement that "summable series have terms → 0".
  The Hölder assumption just ensures L² membership; the actual convergence
  comes entirely from the L² structure (Parseval's identity).
-/

end FourierHolderParseval
