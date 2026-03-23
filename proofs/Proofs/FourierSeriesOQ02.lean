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
  rw [fourier_apply]
  exact Circle.norm_coe _

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
  calc dist x (x + ↑h₀)
      = dist (x + 0) (x + ↑h₀) := by rw [add_zero]
    _ = dist (0 : AddCircle T) ↑h₀ := dist_add_left x 0 ↑h₀
    _ = ‖(h₀ : AddCircle T)‖ := by rw [dist_comm, dist_zero_right]
    _ ≤ ‖h₀‖ := QuotientAddGroup.norm_mk_le_norm
    _ = |h₀| := Real.norm_eq_abs h₀

/-- Translation invariance of Haar measure integral on AddCircle. -/
lemma integral_translate_eq (g : AddCircle T → ℂ) (a : AddCircle T)
    (_hg : Integrable g haarAddCircle) :
    ∫ t, g (t + a) ∂haarAddCircle = ∫ t, g t ∂haarAddCircle :=
  integral_add_right_eq_self g a

/-! ## Part IV: The Averaging Identity -/

/-- The averaging identity: 2 · f̂(n) = ∫ e_{-n}(t) · (f(t) - f(t + h)) dt
    where h = T/(2n). This is the core of the phase shift trick. -/
lemma averaging_identity
    (f : AddCircle T → ℂ) (hf : Integrable f haarAddCircle)
    {n : ℤ} (hn : n ≠ 0) :
    let h : AddCircle T := ↑(T / 2 / (n : ℝ))
    (2 : ℂ) * fourierCoeff f n =
      ∫ t, fourier (-n) t • (f t - f (t + h)) ∂haarAddCircle := by
  intro h
  -- Integrability: fourier(-n) is bounded (norm 1), so product with integrable f is integrable
  have hfh : Integrable (fun t => f (t + h)) haarAddCircle :=
    Integrable.comp_add_right hf h
  have hint1 : Integrable (fun t => fourier (-n) t • f t) haarAddCircle :=
    hf.mono ((fourier (-n)).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable)
      (ae_of_all _ fun t => by rw [norm_smul, norm_fourier_eq_one, one_mul])
  have hint2 : Integrable (fun t => fourier (-n) t • f (t + h)) haarAddCircle :=
    hfh.mono ((fourier (-n)).continuous.aestronglyMeasurable.smul hfh.aestronglyMeasurable)
      (ae_of_all _ fun t => by rw [norm_smul, norm_fourier_eq_one, one_mul])
  -- Translation invariance: ∫ e(-n)(t+h) • f(t+h) = ∫ e(-n)(t) • f(t) = fc
  have fc_shift : ∫ t, fourier (-n) (t + h) • f (t + h) ∂haarAddCircle
      = fourierCoeff f n :=
    integral_add_right_eq_self (fun t => fourier (-n) t • f t) h
  -- Phase shift: e(-n)(t+h) = -e(-n)(t), so ∫ e(-n)(t) • f(t+h) = -fc
  have shift_neg : ∫ t, fourier (-n) t • f (t + h) ∂haarAddCircle
      = -fourierCoeff f n := by
    -- fourier(-n)(t) = -fourier(-n)(t+h), so integrand = -(e(t+h)•f(t+h))
    have h_rw : (fun t => fourier (-n) (t + h) • f (t + h)) =
        fun t => -(fourier (-n) t • f (t + h)) :=
      funext fun t => by rw [fourier_neg_add_half_inv hn, neg_smul]
    rw [h_rw, integral_neg, neg_eq_iff_eq_neg] at fc_shift
    exact fc_shift
  -- Expand RHS: ∫ e•(f - f(·+h)) = ∫ e•f - ∫ e•f(·+h) = fc - (-fc) = 2*fc
  suffices h_eq : ∫ t, fourier (-n) t • (f t - f (t + h)) ∂haarAddCircle
      = fourierCoeff f n - (-fourierCoeff f n) by
    rw [h_eq]; ring
  rw [show (fun t => fourier (-n) t • (f t - f (t + h))) =
      fun t => fourier (-n) t • f t - fourier (-n) t • f (t + h) from
    funext fun t => smul_sub _ _ _]
  rw [integral_sub hint1 hint2, show (∫ t, fourier (-n) t • f t ∂haarAddCircle) =
    fourierCoeff f n from rfl, shift_neg]

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
  -- Hölder with α=1: dist^1 = dist
  have rpow1 : ∀ (x : ℝ), x ^ (1 : ℝ) = x := by
    intro x; rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) from Nat.cast_one.symm]
    exact_mod_cast pow_one x
  have holder : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ K * dist x y ^ (1 : ℝ) := by
    intro x y; rw [rpow1]; exact lip x y
  have h := fourierCoeff_holder_decay one_pos hK holder hf hn
  rw [rpow1] at h
  calc ‖fourierCoeff f n‖ ≤ K / 2 * (T / (2 * |(n : ℝ)|)) := h
    _ = K * T / (4 * |(n : ℝ)|) := by ring

/-- **Riemann-Lebesgue for Hölder functions**: f̂(n) → 0 with quantitative rate.
    Uses the decay bound from `fourierCoeff_holder_decay` and the Archimedean property
    to show only finitely many coefficients can exceed any ε > 0. -/
theorem fourierCoeff_tendsto_zero_of_holder
    {f : AddCircle T → ℂ} {C : ℝ} {α : ℝ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (holder : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ α)
    (hf : Integrable f haarAddCircle) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  simp only [dist_zero_right]
  rw [Filter.Eventually, Filter.mem_cofinite]
  -- Suffices: ∃ N, ∀ n with |n| > N, ‖fc n‖ < ε
  suffices ∃ N : ℕ, ∀ n : ℤ, N < n.natAbs → ‖fourierCoeff f n‖ < ε by
    obtain ⟨N, hN⟩ := this
    apply (Set.finite_Icc (-(N : ℤ)) ↑N).subset
    intro n hn
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at hn
    simp only [Set.mem_Icc]
    by_contra habs; push_neg at habs
    exact absurd (hN n (by omega)) (not_lt.mpr hn)
  -- Case C = 0: bound is 0 for all n ≠ 0
  by_cases hCz : C = 0
  · exact ⟨0, fun n hn => by
      have hne : n ≠ 0 := by omega
      have := fourierCoeff_holder_decay hα hC holder hf hne
      rw [hCz, zero_div, zero_mul] at this
      linarith [norm_nonneg (fourierCoeff f n)]⟩
  -- Case C > 0: use Archimedean property to find N where decay bound < ε
  · push_neg at hCz
    have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCz)
    have hTpos := hT.out
    have heps_C : 0 < 2 * ε / C := by positivity
    -- Choose N such that the decay bound (C/2)·(T/(2N))^α < ε
    obtain ⟨N, hN⟩ := exists_nat_gt (T / (2 * (2 * ε / C) ^ (1 / α)))
    refine ⟨N, fun n hn => ?_⟩
    have hne : n ≠ 0 := by omega
    have h_nR_pos : (0 : ℝ) < |(n : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hne)
    -- Convert: (N : ℝ) < |(n : ℝ)| via natAbs
    have h_natabs_eq : (n.natAbs : ℝ) = |(n : ℝ)| := by
      rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    have h_nR_gt : (N : ℝ) < |(n : ℝ)| := by
      linarith [show (N : ℝ) < (n.natAbs : ℝ) from Nat.cast_lt.mpr hn]
    -- T/(2|n|) < (2ε/C)^{1/α} from the bound on N
    have h_base_pos : 0 < 2 * (2 * ε / C) ^ (1 / α) := by positivity
    have h_2n_pos : (0 : ℝ) < 2 * |(n : ℝ)| := by linarith
    have h_ratio : T / (2 * |(n : ℝ)|) < (2 * ε / C) ^ (1 / α) := by
      rw [div_lt_iff₀ h_2n_pos]
      have hT_lt : T < ↑N * (2 * (2 * ε / C) ^ (1 / α)) :=
        (div_lt_iff₀ h_base_pos).mp hN
      calc T < ↑N * (2 * (2 * ε / C) ^ (1 / α)) := hT_lt
        _ ≤ |(n : ℝ)| * (2 * (2 * ε / C) ^ (1 / α)) := by
            apply mul_le_mul_of_nonneg_right (le_of_lt h_nR_gt); linarith
        _ = (2 * ε / C) ^ (1 / α) * (2 * |(n : ℝ)|) := by ring
    -- (T/(2|n|))^α < ((2ε/C)^{1/α})^α = 2ε/C
    have h_ratio_nn : 0 ≤ T / (2 * |(n : ℝ)|) := by positivity
    have h_rpow : (T / (2 * |(n : ℝ)|)) ^ α < 2 * ε / C := by
      calc (T / (2 * |(n : ℝ)|)) ^ α
          < ((2 * ε / C) ^ (1 / α)) ^ α :=
            Real.rpow_lt_rpow h_ratio_nn h_ratio hα
        _ = 2 * ε / C := by
            rw [← Real.rpow_mul (le_of_lt heps_C)]
            rw [show (1 / α) * α = 1 from by field_simp]
            exact Real.rpow_one _
    -- Final: ‖fc n‖ ≤ (C/2)·bound < (C/2)·(2ε/C) = ε
    calc ‖fourierCoeff f n‖
        ≤ C / 2 * (T / (2 * |(n : ℝ)|)) ^ α :=
          fourierCoeff_holder_decay hα hC holder hf hne
      _ < C / 2 * (2 * ε / C) := by nlinarith
      _ = ε := by field_simp

/-- **Summability (Bernstein's theorem)**: When α > 1/2, Fourier coefficients are
    absolutely summable, guaranteeing uniform convergence of the Fourier series.

    The proof uses dyadic decomposition and Cauchy-Schwarz: partition ℤ into dyadic blocks
    {2^k ≤ |n| < 2^{k+1}}, apply Cauchy-Schwarz to each block, then use Parseval's identity
    with the Hölder modulus of continuity to sum the geometric series in 2^{k(1/2-α)}. -/
theorem summable_fourierCoeff_of_holder
    {f : AddCircle T → ℂ} {C : ℝ} {α : ℝ}
    (hα : 1 / 2 < α) (hC : 0 ≤ C)
    (holder : ∀ x y : AddCircle T, ‖f x - f y‖ ≤ C * dist x y ^ α)
    (hf : Integrable f haarAddCircle) :
    Summable (fun n : ℤ => fourierCoeff f n) := by
  -- Bernstein's theorem: requires dyadic Cauchy-Schwarz + Parseval, ~200 lines
  sorry

/-! ## Verification -/

#check @fourierCoeff_holder_decay
#check @fourierCoeff_lipschitz_decay
#check @fourierCoeff_tendsto_zero_of_holder
#check @summable_fourierCoeff_of_holder

end FourierDecay
