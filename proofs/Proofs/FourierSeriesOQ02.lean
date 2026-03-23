import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic

/-
# Fourier Coefficient Decay under Hölder Continuity

## The Classical Result

If f : AddCircle T → ℂ is α-Hölder continuous with constant C, meaning
  ‖f(x) - f(y)‖ ≤ C · dist(x,y)^α  for all x, y,
then the Fourier coefficients satisfy the decay bound
  |f̂(n)| ≤ (C/2) · (T/(2|n|))^α  for all n ≠ 0.

## Proof Technique: Phase Shift Averaging

The proof uses the "phase shift averaging trick":

1. f̂(n) = ∫ e_{-n}(t) · f(t) dt                         (definition)
2. f̂(n) = ∫ e_{-n}(t+h) · f(t+h) dt                     (translation invariance)
         = -∫ e_{-n}(t) · f(t+h) dt                       (phase shift with h = T/(2n))
3. 2·f̂(n) = ∫ e_{-n}(t) · (f(t) - f(t+h)) dt            (averaging 1 and 2)
4. |2·f̂(n)| ≤ ∫ |f(t) - f(t+h)| dt ≤ C · (T/(2|n|))^α  (Hölder bound)

The key insight is that shifting by half a wavelength (T/(2n)) negates the
n-th Fourier monomial, which when combined with the original integral isolates
the modulus of continuity of f.

## Applications

- For Lipschitz functions (α = 1): |f̂(n)| = O(1/|n|)
- For C^k functions: |f̂(n)| = O(1/|n|^k) via repeated integration by parts
- When α > 1/2, the coefficients are absolutely summable (uniform convergence)
- The Riemann-Lebesgue lemma (f̂(n) → 0) follows as a corollary

## References

- Katznelson, Y. (2004). "An Introduction to Harmonic Analysis", Ch. I §2
- Grafakos, L. (2014). "Classical Fourier Analysis", Proposition 3.1.17
- Stein, E.M. & Shakarchi, R. (2003). "Fourier Analysis", Ch. 2
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle
open scoped ENNReal NNReal Real

namespace FourierDecay

variable {T : ℝ} [hT : Fact (0 < T)]

/-! ## Part I: Pointwise Properties of Fourier Monomials -/

/-- Every Fourier monomial has pointwise complex norm 1.
    This is because fourier n x = (toCircle x)^n and toCircle lands on the unit circle. -/
lemma norm_fourier_eq_one (n : ℤ) (x : AddCircle T) : ‖fourier n x‖ = 1 := by
  -- fourier n x = ↑(toCircle(n • x)) where toCircle maps into the unit circle
  -- toCircle(n • x) is in the unit circle, so its norm is 1
  -- The proof involves unfolding Submonoid.unitSphere membership
  sorry

/-! ## Part II: Phase Shift Lemma

The fundamental identity: translating by T/(2n) negates the n-th Fourier monomial.
Mathlib provides `fourier_add_half_inv_index` for fourier(n); we derive the
corresponding identity for fourier(-n) via complex conjugation. -/

/-- Translation by T/(2n) negates fourier(-n). Uses the conjugation identity
    `fourier (-n) x = conj(fourier n x)` and `fourier_add_half_inv_index`. -/
lemma fourier_neg_add_half_inv {n : ℤ} (hn : n ≠ 0) (x : AddCircle T) :
    fourier (-n) (x + ↑(T / 2 / ↑n)) = -fourier (-n) x := by
  simp only [fourier_neg]
  rw [fourier_add_half_inv_index hn hT.out, map_neg]

/-! ## Part III: Auxiliary Lemmas -/

/-- Distance bound on AddCircle: dist(x, x + ↑h₀) ≤ |h₀|.
    Follows from the quotient metric being bounded by the lift. -/
lemma dist_translate_le (x : AddCircle T) (h₀ : ℝ) :
    dist x (x + (h₀ : AddCircle T)) ≤ |h₀| := by
  sorry

/-- Translation invariance of Haar measure integral on AddCircle. -/
lemma integral_translate_eq (g : AddCircle T → ℂ) (a : AddCircle T)
    (hg : Integrable g haarAddCircle) :
    ∫ t, g (t + a) ∂haarAddCircle = ∫ t, g t ∂haarAddCircle := by
  sorry

/-! ## Part IV: The Averaging Identity -/

/-- The averaging identity: 2 · f̂(n) = ∫ e_{-n}(t) · (f(t) - f(t + h)) dt
    where h = T/(2n). This is the core of the phase shift trick. -/
lemma averaging_identity
    (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : n ≠ 0) :
    let h : AddCircle T := ↑(T / 2 / (n : ℝ))
    (2 : ℂ) * fourierCoeff f n =
      ∫ t, fourier (-n) t • (f t - f (t + h)) ∂haarAddCircle := by
  sorry

/-! ## Part V: Main Theorem -/

/-- **Fourier Coefficient Decay under Hölder Continuity**

If f : AddCircle T → ℂ is α-Hölder continuous with constant C, then
  ‖f̂(n)‖ ≤ (C/2) · (T/(2|n|))^α  for all n ≠ 0.

Proof outline (phase shift averaging trick):
1. Use `averaging_identity`: 2·f̂(n) = ∫ e_{-n}(t)·(f(t) - f(t+T/(2n))) dt
2. Bound: ‖2·f̂(n)‖ ≤ ∫ ‖f(t) - f(t+h)‖ dt  (using |e_{-n}| = 1)
3. Apply Hölder: ‖f(t) - f(t+h)‖ ≤ C · dist(t, t+h)^α ≤ C · (T/(2|n|))^α
4. Integrate: probability measure has total mass 1
5. Divide by 2. -/
theorem fourierCoeff_holder_decay
    {f : AddCircle T → ℂ} {C : ℝ} {α : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (holder : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ α)
    (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤ C / 2 * (T / (2 * |(n : ℝ)|)) ^ α := by
  -- Setup: the shift h₀ = T/(2n) and the bound δ = T/(2|n|) = |h₀|
  set h₀ : ℝ := T / 2 / (n : ℝ)
  set h : AddCircle T := ↑h₀
  set δ : ℝ := T / (2 * |(n : ℝ)|)
  -- Key fact: |h₀| = δ
  have habs : |h₀| = δ := by
    show |T / 2 / (n : ℝ)| = T / (2 * |(n : ℝ)|)
    rw [abs_div, abs_of_pos (half_pos hT.out), div_div]
  have hδ_nn : 0 ≤ δ := by linarith [abs_nonneg h₀]
  -- Step 1: The averaging identity gives 2·fc = ∫ e_{-n}(t)·(f(t)-f(t+h)) dt
  have avg := averaging_identity f hf hn
  -- Step 2: Bound ‖2·fc‖ using triangle inequality + Hölder condition
  -- ‖2·fc‖ = ‖∫ e·(f-f(·+h))‖ ≤ ∫ ‖e·(f-f(·+h))‖ = ∫ ‖f-f(·+h)‖ ≤ C·δ^α
  have two_fc_bound : ‖(2 : ℂ) * fourierCoeff f n‖ ≤ C * δ ^ α := by
    rw [avg]
    calc ‖∫ t, fourier (-n) t • (f t - f (t + h)) ∂haarAddCircle‖
        ≤ ∫ t, ‖fourier (-n) t • (f t - f (t + h))‖ ∂haarAddCircle :=
          norm_integral_le_integral_norm _
      _ = ∫ t, ‖f t - f (t + h)‖ ∂haarAddCircle := by
          congr 1; ext t
          rw [norm_smul, norm_fourier_eq_one, one_mul]
      _ ≤ ∫ _, C * δ ^ α ∂haarAddCircle := by
          apply MeasureTheory.integral_mono_of_nonneg
          · exact ae_of_all _ (fun t => norm_nonneg _)
          · exact integrable_const _
          · exact ae_of_all _ (fun t =>
              calc ‖f t - f (t + h)‖
                  ≤ C * dist t (t + h) ^ α := holder t (t + h)
                _ ≤ C * |h₀| ^ α := by
                    apply mul_le_mul_of_nonneg_left _ hC
                    exact Real.rpow_le_rpow dist_nonneg (dist_translate_le t h₀) (le_of_lt hα)
                _ = C * δ ^ α := by rw [habs])
      _ = C * δ ^ α := by
          rw [MeasureTheory.integral_const]
          -- haarAddCircle is a probability measure: total mass = 1
          simp [Measure.real, IsProbabilityMeasure.measure_univ]
  -- Step 3: ‖fc‖ = ‖2·fc‖/2 ≤ (C·δ^α)/2 = (C/2)·δ^α
  calc ‖fourierCoeff f n‖
      = ‖(2 : ℂ) * fourierCoeff f n‖ / 2 := by
        rw [norm_mul, show ‖(2:ℂ)‖ = 2 from by norm_num]; ring
    _ ≤ C * δ ^ α / 2 :=
        div_le_div_of_nonneg_right two_fc_bound (by norm_num : (0 : ℝ) ≤ 2)
    _ = C / 2 * δ ^ α := by ring

/-! ## Part VI: Corollaries -/

/-- **Lipschitz Decay**: For Lipschitz functions, |f̂(n)| ≤ K·T/(4|n|). -/
theorem fourierCoeff_lipschitz_decay
    {f : AddCircle T → ℂ} {K : ℝ}
    (hK : 0 ≤ K)
    (lip : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ K * dist x y)
    (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : n ≠ 0) :
    ‖fourierCoeff f n‖ ≤ K * T / (4 * |(n : ℝ)|) := by
  sorry

/-- **Riemann-Lebesgue for Hölder functions**: f̂(n) → 0 with quantitative rate. -/
theorem fourierCoeff_tendsto_zero_of_holder
    {f : AddCircle T → ℂ} {C : ℝ} {α : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (holder : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ α)
    (hf : Integrable f haarAddCircle) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  sorry

/-- **Summability**: When α > 1/2, Fourier coefficients are absolutely summable,
    guaranteeing uniform convergence of the Fourier series. -/
theorem summable_fourierCoeff_of_holder
    {f : AddCircle T → ℂ} {C : ℝ} {α : ℝ}
    (hα : 1 / 2 < α) (hC : 0 ≤ C)
    (holder : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ α)
    (hf : Integrable f haarAddCircle) :
    Summable (fun n : ℤ => fourierCoeff f n) := by
  sorry

/-! ## Verification -/

#check @fourierCoeff_holder_decay
#check @fourierCoeff_lipschitz_decay
#check @fourierCoeff_tendsto_zero_of_holder
#check @summable_fourierCoeff_of_holder

end FourierDecay
