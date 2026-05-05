/-
  Weierstrass Optimality for Fourier Coefficient Decay

  Proves holder_decay_is_optimal_seq: for 0 < α < 1, there exists an α-Hölder
  function on AddCircle T whose Fourier coefficients achieve the O(1/|n|^α) rate
  along the lacunary sequence n_k = 2^k.

  Witness: f(x) = ∑_{k:ℕ} r^k • fourier(2^k)(x)  where r = 2^{-α} ∈ (0,1).

  Key steps:
  1. f is well-defined (uniform convergence from Σ r^k < ∞)
  2. fourierCoeff f (2^k₀) = r^{k₀} (Fourier orthogonality via integral_tsum)
  3. f is α-Hölder: split-sum argument with p₀ = Nat.log 2 ⌈T/d⌉
-/
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Proofs.FourierSeriesOQ02Incomplete01
import Mathlib.Tactic

set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Complex Topology Filter AddCircle Finset
open scoped ENNReal NNReal Real

namespace WeierstrassOptimality

variable {T : ℝ} [hT : Fact (0 < T)]

/-!
## Part I: Fourier mode orthogonality

∫ x, fourier m x ∂haarAddCircle = if m = 0 then 1 else 0
fourierCoeff (fourier m) n = if m = n then 1 else 0
-/

/-- Integral of a single Fourier mode is 1 for mode 0 and 0 otherwise. -/
private theorem fourier_integral (m : ℤ) :
    ∫ t : AddCircle T, fourier m t ∂haarAddCircle = if m = 0 then 1 else 0 := by
  split_ifs with hm
  · subst hm; simp_rw [fourier_zero]
    rw [integral_const, measure_univ, ENNReal.one_toReal, one_smul]
  · exact integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hm hT.out)

/-- The Fourier coefficient of a Fourier mode: ĉ_m(fourier n) = if n = m then 1 else 0. -/
private theorem fourierCoeff_fourier_mode (n m : ℤ) :
    fourierCoeff (fourier n : AddCircle T → ℂ) m = if n = m then 1 else 0 := by
  simp only [fourierCoeff, smul_eq_mul]
  -- Rewrite: fourier(-m)(x) * fourier(n)(x) = fourier(n + (-m))(x)
  have h_prod : ∀ x : AddCircle T, fourier (-m) x * fourier n x = fourier (n + (-m)) x := by
    intro x; rw [← fourier_add]
  simp_rw [h_prod]
  -- Now ∫ x, fourier(n - m)(x) ∂μ = if n - m = 0 then 1 else 0
  rw [show ∀ k : ℤ, (k = 0) ↔ (n + (-m) = 0) ↔ (n = m) from
    fun k => Iff.rfl |>.trans (by constructor <;> intro h <;> omega)]
  rw [show n + (-m) = n - m from by ring]
  rw [show (if n - m = 0 then (1 : ℂ) else 0) = if n = m then 1 else 0 from by
    split_ifs with h1 h2 h2 <;> simp_all <;> omega]
  exact fourier_integral (n - m) |>.trans (by
    split_ifs with h1 h2 h2 <;> simp_all <;> omega)

/-!
## Part II: The Weierstrass lacunary function
-/

/-- The geometric ratio r = 2^{-α}. For 0 < α, we have 0 < r < 1. -/
private def geomRatio (α : ℝ) : ℝ := (2 : ℝ)^(-α)

private theorem geomRatio_pos (α : ℝ) : 0 < geomRatio α :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem geomRatio_lt_one (α : ℝ) (hα : 0 < α) : geomRatio α < 1 := by
  unfold geomRatio
  rw [Real.rpow_neg (by norm_num)]
  exact inv_lt_one (by rwa [show (1:ℝ) = (2:ℝ)^(0:ℝ) from by simp;
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hα])

/-- The Weierstrass lacunary function f(x) = ∑_{k:ℕ} r^k • fourier(2^k)(x). -/
private def wFunc (α : ℝ) : AddCircle T → ℂ :=
  fun x => ∑' k : ℕ, (geomRatio α)^k • fourier ((2:ℤ)^k) x

/-- Each term in the series has norm ≤ r^k (since ‖fourier(n)(x)‖ = 1). -/
private theorem wFunc_term_norm (α : ℝ) (k : ℕ) (x : AddCircle T) :
    ‖(geomRatio α)^k • fourier ((2:ℤ)^k) x‖ ≤ (geomRatio α)^k := by
  rw [norm_smul]
  simp only [Real.norm_rpow_of_nonneg (by norm_num), Real.norm_ofNat]
  rw [FourierDecayInfra.fourier_norm_eq_one]
  simp [mul_one, norm_pow, Real.norm_of_nonneg (geomRatio_pos α).le]

/-- The series defining wFunc is uniformly convergent (summable). -/
private theorem wFunc_summable (α : ℝ) (hα : 0 < α) (x : AddCircle T) :
    Summable (fun k : ℕ => (geomRatio α)^k • fourier ((2:ℤ)^k) x) := by
  apply Summable.of_norm_bounded (fun k => (geomRatio α)^k)
  · exact summable_geometric_of_lt_one (geomRatio_pos α).le (geomRatio_lt_one α hα)
  · exact fun k => wFunc_term_norm α k x

/-- The norm-summable bound for use in integral_tsum. -/
private theorem wFunc_norm_tsum_ne_top (α : ℝ) (hα : 0 < α) (n : ℤ) :
    ∑' k : ℕ, ∫⁻ x : AddCircle T,
      ‖fourier (-n) x • ((geomRatio α)^k • fourier ((2:ℤ)^k) x)‖ₑ ∂haarAddCircle ≠ ⊤ := by
  apply ne_of_lt
  have hbound : ∀ k : ℕ, ∫⁻ x : AddCircle T,
      ‖fourier (-n) x • ((geomRatio α)^k • fourier ((2:ℤ)^k) x)‖ₑ ∂haarAddCircle ≤
      ENNReal.ofReal ((geomRatio α)^k) := by
    intro k
    calc ∫⁻ x : AddCircle T, ‖fourier (-n) x • ((geomRatio α)^k • fourier ((2:ℤ)^k) x)‖ₑ ∂haarAddCircle
        ≤ ∫⁻ _ : AddCircle T, ENNReal.ofReal ((geomRatio α)^k) ∂haarAddCircle := by
          apply lintegral_mono_ae; apply Filter.Eventually.of_forall; intro x
          show ‖fourier (-n) x • ((geomRatio α : ℝ)^k • fourier ((2:ℤ)^k) x)‖ₑ ≤
            ENNReal.ofReal ((geomRatio α)^k)
          rw [enorm_le_ofReal (by positivity), norm_smul, norm_smul,
              FourierDecayInfra.fourier_norm_eq_one,
              Real.norm_rpow_of_nonneg (by norm_num), Real.norm_ofNat,
              FourierDecayInfra.fourier_norm_eq_one,
              Real.norm_of_nonneg (geomRatio_pos α).le]
          ring_nf; linarith [pow_nonneg (geomRatio_pos α).le k]
      _ = ENNReal.ofReal ((geomRatio α)^k) := by
          rw [lintegral_const, measure_univ, ENNReal.one_toReal, one_mul]
  calc ∑' k : ℕ, ∫⁻ x : AddCircle T,
      ‖fourier (-n) x • ((geomRatio α)^k • fourier ((2:ℤ)^k) x)‖ₑ ∂haarAddCircle
      ≤ ∑' k : ℕ, ENNReal.ofReal ((geomRatio α)^k) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (∑' k : ℕ, (geomRatio α)^k) := by
        rw [ENNReal.ofReal_tsum_of_nonneg
          (fun k => pow_nonneg (geomRatio_pos α).le k)
          (summable_geometric_of_lt_one (geomRatio_pos α).le (geomRatio_lt_one α hα))]
    _ < ⊤ := ENNReal.ofReal_lt_top

/-!
## Part III: Fourier coefficient computation
-/

/-- The Fourier coefficient of wFunc along the lacunary sequence: ĉ_{2^k₀}(f) = r^{k₀}. -/
private theorem wFunc_fourierCoeff (α : ℝ) (hα : 0 < α) (k₀ : ℕ) :
    fourierCoeff (wFunc α (T := T)) ((2:ℤ)^k₀) = (geomRatio α : ℂ)^k₀ := by
  -- Unfold definition
  simp only [fourierCoeff, wFunc, smul_eq_mul]
  -- Interchange integral and tsum
  rw [show (fun x => fourier (-(2:ℤ)^k₀) x *
        ∑' k : ℕ, (geomRatio α : ℝ)^k • fourier ((2:ℤ)^k) x) =
      fun x => ∑' k : ℕ, fourier (-(2:ℤ)^k₀) x * ((geomRatio α : ℝ)^k • fourier ((2:ℤ)^k) x)
    from funext fun x => by rw [mul_comm, ← tsum_mul_left]; congr 1; ext k; ring]
  rw [integral_tsum
    (fun k => (((fourier (-(2:ℤ)^k₀)).continuous.mul
      ((continuous_const.smul (fourier ((2:ℤ)^k)).continuous))).aestronglyMeasurable))
    (wFunc_norm_tsum_ne_top α hα _)]
  -- Simplify each integral: fourier(-2^k₀)(x) * r^k * fourier(2^k)(x)
  --   = r^k * fourier(2^k + (-(2^k₀)))(x)  [character multiplication]
  simp_rw [smul_eq_mul]
  have h_orth : ∀ k : ℕ,
      ∫ x : AddCircle T, fourier (-(2:ℤ)^k₀) x * ((geomRatio α : ℝ)^k * fourier ((2:ℤ)^k) x)
        ∂haarAddCircle =
      (geomRatio α : ℂ)^k * (if (2:ℤ)^k = (2:ℤ)^k₀ then 1 else 0) := by
    intro k
    have h_mul : ∀ x : AddCircle T,
        fourier (-(2:ℤ)^k₀) x * ((geomRatio α : ℝ)^k * fourier ((2:ℤ)^k) x) =
        (geomRatio α : ℂ)^k * fourier ((2:ℤ)^k + (-(2:ℤ)^k₀)) x := by
      intro x
      rw [← fourier_add]
      push_cast; ring
    simp_rw [h_mul, integral_mul_left]
    rw [fourier_integral]
    simp only [add_neg_eq_zero]
  simp_rw [h_orth]
  -- The tsum picks out k = k₀
  have h_inj : ∀ k : ℕ, (2:ℤ)^k = (2:ℤ)^k₀ ↔ k = k₀ := by
    intro k
    constructor
    · intro h; exact_mod_cast Nat.pow_right_injective (by norm_num) (by exact_mod_cast h)
    · intro h; subst h; rfl
  simp_rw [h_inj]
  rw [tsum_ite_eq_extract (summable_geometric_of_lt_one
    (by exact_mod_cast pow_nonneg (geomRatio_pos α).le k₀)
    (by push_cast; exact pow_lt_one (geomRatio_pos α).le (geomRatio_lt_one α hα) (by omega))
    |>.mul_right _)]
  simp

/-!
## Part IV: Hölder continuity of wFunc

We prove ‖wFunc α x - wFunc α y‖ ≤ K * dist x y ^ α
using the split-sum argument:
- Low terms (k < p₀): Lipschitz bound from FourierDecayInfra
- High terms (k ≥ p₀): trivial bound ‖e_n(x) - e_n(y)‖ ≤ 2

where p₀ = Nat.log 2 ⌈T / dist x y⌉.
-/

/-- Partial geometric sum bound: ∑_{k<p} s^k ≤ s^p / (s-1) for s > 1. -/
private theorem geom_partial_sum_le {s : ℝ} (hs : 1 < s) (p : ℕ) :
    ∑ k in Finset.range p, s^k ≤ s^p / (s - 1) := by
  induction p with
  | zero => simp; positivity
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc ∑ k in Finset.range n, s^k + s^n
        ≤ s^n / (s-1) + s^n := by linarith
      _ = s^(n+1) / (s-1) := by
          rw [pow_succ]; field_simp; ring

/-- The geometric tail sum: ∑_{k≥p₀} r^k = r^{p₀} / (1-r). -/
private theorem geom_tail_sum {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (p₀ : ℕ) :
    ∑' k : ℕ, r^(k + p₀) = r^p₀ / (1 - r) := by
  rw [tsum_geometric_of_lt_one hr0.le hr1 |>.symm ▸ rfl]
  rw [show (fun k : ℕ => r^(k + p₀)) = fun k => r^p₀ * r^k from funext fun k => by
    rw [pow_add, mul_comm]]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
  ring

/-- Main Hölder bound for wFunc. -/
private theorem wFunc_holder_bound (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1)
    (x y : AddCircle T) :
    ‖wFunc α (T := T) x - wFunc α y‖ ≤
      ((2 * Real.pi * (2 * T)^(1-α)) / (T * ((2:ℝ)^(1-α) - 1)) +
       (2 * (4:ℝ)^α) / (T^α * (1 - (2:ℝ)^(-α)))) *
      dist x y ^ α := by
  set r := geomRatio α with hr_def
  set s := (2:ℝ)^(1-α) with hs_def
  have hr_pos : 0 < r := geomRatio_pos α
  have hr_lt1 : r < 1 := geomRatio_lt_one α hα_pos
  have hs_gt1 : 1 < s := by
    unfold_let s; rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) from by simp]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hs_pos : 0 < s - 1 := by linarith
  have hT_pos := hT.out
  -- Handle trivial case d = 0
  set d := dist x y
  by_cases hd : d = 0
  · simp [hd, hd ▸ dist_eq_zero |>.mp hd]
  have hd_pos : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
  -- Choose split index p₀ = Nat.log 2 ⌈T/d⌉
  set n₀ : ℕ := Nat.ceil (T / d) with hn₀_def
  have hn₀_pos : 0 < n₀ := by
    rw [hn₀_def]; apply Nat.ceil_pos.mpr; positivity
  set p₀ : ℕ := Nat.log 2 n₀ with hp₀_def
  -- Key bounds: 2^{p₀} ≤ n₀ ≤ 2T/d, and T/d ≤ n₀ < 2^{p₀+1}
  have h_pow_le : (2:ℝ)^p₀ ≤ 2 * T / d := by
    calc (2:ℝ)^p₀ = ((2:ℕ)^p₀ : ℕ) := by push_cast; rfl
      _ ≤ (n₀ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 n₀
      _ ≤ 2 * T / d := by
          rw [hn₀_def]; calc (Nat.ceil (T/d) : ℝ)
            ≤ T/d + 1 := Nat.ceil_le_add_one_iff (by positivity) |>.le |>.trans_eq (by ring) |>.le
            _ ≤ 2 * T / d := by rw [div_add_eq_add_div, div_le_div_iff hd_pos hd_pos]; linarith
  have h_pow_gt : T / d < (2:ℝ)^(p₀+1) := by
    calc T / d ≤ (n₀ : ℝ) := by
          rw [hn₀_def]; exact Nat.le_ceil _
      _ < (2:ℝ)^(p₀+1) := by
          exact_mod_cast Nat.lt_pow_succ_log_self (by omega) n₀
  -- Key rpow bounds
  have h_s_bound : s^p₀ ≤ (2 * T / d)^(1-α) := by
    unfold_let s
    calc (2:ℝ)^(p₀ * (1-α))
        = ((2:ℝ)^p₀)^(1-α) := by rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
      _ ≤ (2 * T / d)^(1-α) := by
          apply Real.rpow_le_rpow (by positivity) h_pow_le; linarith
  have h_r_bound : r^p₀ < (4 * d / T)^α := by
    unfold_let r geomRatio
    calc (2:ℝ)^(-(p₀ * α))
        = ((2:ℝ)^(p₀+1))^(-α) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; ring_nf
      _ < (T/d)^(-α) := by
          apply Real.rpow_lt_rpow_of_exponent_gt (by positivity) h_pow_gt
          linarith [Real.rpow_pos_of_pos (by norm_num : (0:ℝ) < 2) (p₀+1 : ℝ)]
      _ = (d/T)^α := by rw [Real.rpow_neg (by positivity)]; simp [Real.rpow_neg]
      _ ≤ (4 * d / T)^α := by
          apply Real.rpow_le_rpow (by positivity)
          · linarith [hd_pos, hT_pos]
          · linarith
  -- The difference f(x) - f(y) = ∑' k, r^k • (fourier(2^k)(x) - fourier(2^k)(y))
  have h_diff : wFunc α x - wFunc α y =
      ∑' k : ℕ, (r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)) := by
    unfold_let wFunc
    simp_rw [← smul_sub]
    rw [← tsum_sub (wFunc_summable α hα_pos x) (wFunc_summable α hα_pos y)]
  rw [h_diff]
  -- Summability of norms
  have h_summ_norm : Summable (fun k : ℕ => r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖) :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => by rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hr_pos.le _)]; exact le_refl _)
      ((summable_geometric_of_lt_one hr_pos.le hr_lt1).mul_right 2 |>.of_nonneg_of_le
        (fun k => by positivity) (fun k => by
          apply mul_le_mul_of_nonneg_left (FourierDecayInfra.fourier_sub_norm_le_two _ _ _)
          exact pow_nonneg hr_pos.le _))
  -- Norm bound via triangle inequality
  have h_tri : ‖∑' k : ℕ, r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖ ≤
      ∑' k : ℕ, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ := by
    calc ‖∑' k, r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖
        ≤ ∑' k, ‖r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖ :=
          norm_tsum_le_tsum_norm h_summ_norm.of_norm_bounded_eventually (by
            apply Filter.Eventually.of_forall; intro k; rw [norm_smul, Real.norm_of_nonneg
              (pow_nonneg hr_pos.le _)])
      _ = _ := by congr 1; ext k; rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hr_pos.le _)]
  -- Split the tsum at p₀
  have h_split : ∑' k : ℕ, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ ≤
      (∑ k in Finset.range p₀, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖) +
      ∑' k : ℕ, r^(k + p₀) * 2 := by
    rw [← h_summ_norm.sum_add_tsum_nat_add p₀]
    apply add_le_add_left
    apply Summable.tsum_le_tsum _ (h_summ_norm.nat_add p₀)
      ((summable_geometric_of_lt_one hr_pos.le hr_lt1).mul_right 2 |>.nat_add p₀)
    intro k
    apply mul_le_mul_of_nonneg_left (FourierDecayInfra.fourier_sub_norm_le_two _ _ _)
    exact pow_nonneg hr_pos.le _
  -- Low sum bound: Lipschitz
  have h_low : ∑ k in Finset.range p₀, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ ≤
      (2 * Real.pi * (2 * T)^(1-α)) / (T * ((2:ℝ)^(1-α) - 1)) * d^α := by
    calc ∑ k in Finset.range p₀, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖
        ≤ ∑ k in Finset.range p₀, r^k * (2 * Real.pi * (2:ℝ)^k / T * d) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr_pos.le _)
          calc ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖
              ≤ 2 * Real.pi * |(↑((2:ℤ)^k) : ℝ)| / T * d :=
                FourierDecayInfra.fourier_lipschitz_bound _ _ _
            _ = 2 * Real.pi * (2:ℝ)^k / T * d := by
                congr 2; simp [abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) k)]
      _ = (2 * Real.pi / T * d) * ∑ k in Finset.range p₀, (r * 2)^k := by
          simp_rw [← Finset.mul_sum]; congr 1; ext k; ring
      _ ≤ (2 * Real.pi / T * d) * (s^p₀ / (s - 1)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply geom_partial_sum_le hs_gt1
      _ ≤ (2 * Real.pi * (2 * T)^(1-α)) / (T * ((2:ℝ)^(1-α) - 1)) * d^α := by
          unfold_let s
          rw [div_mul_eq_mul_div, div_le_div_iff (by positivity) (by positivity)]
          calc (2 * Real.pi / T * d) * ((2:ℝ)^(p₀*(1-α)) / ((2:ℝ)^(1-α) - 1)) *
              (T * ((2:ℝ)^(1-α) - 1))
              = (2 * Real.pi * (2:ℝ)^(p₀*(1-α)) * d) / T := by ring
            _ ≤ (2 * Real.pi * (2*T/d)^(1-α) * d) / T := by
                apply div_le_div_of_nonneg_right _ hT_pos
                apply mul_le_mul_of_nonneg_left h_s_bound (by positivity)
            _ = 2 * Real.pi * (2*T)^(1-α) / T * d^α := by
                rw [Real.mul_rpow (by norm_num) (by positivity)]
                field_simp; ring
            _ = 2 * Real.pi * (2*T)^(1-α) / T * d^α * (T * ((2:ℝ)^(1-α) - 1)) /
                (T * ((2:ℝ)^(1-α) - 1)) := by
                  field_simp
  -- High sum bound: trivial
  have h_high : ∑' k : ℕ, r^(k + p₀) * 2 ≤
      (2 * (4:ℝ)^α) / (T^α * (1 - (2:ℝ)^(-α))) * d^α := by
    rw [show (fun k : ℕ => r^(k+p₀) * 2) = fun k => 2 * r^(k+p₀) from funext (fun k => by ring)]
    rw [tsum_mul_left, geom_tail_sum hr_pos hr_lt1]
    unfold_let r geomRatio
    rw [div_mul_eq_mul_div, mul_div_assoc']
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc 2 * (2:ℝ)^(-(p₀:ℝ) * α)
        < 2 * (4 * d / T)^α := by
          apply mul_lt_mul_of_pos_left h_r_bound (by norm_num)
      _ = 2 * (4:ℝ)^α * d^α / T^α := by
          rw [Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by norm_num) hd_pos.le]
          ring
      _ ≤ 2 * (4:ℝ)^α * d^α / T^α := le_refl _
  -- Combine
  calc ‖wFunc α (T := T) x - wFunc α y‖
      ≤ ∑' k : ℕ, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ := h_tri
    _ ≤ _ + ∑' k : ℕ, r^(k + p₀) * 2 := h_split
    _ ≤ _ := add_le_add h_low h_high

/-- wFunc is α-Hölder continuous. -/
private theorem wFunc_holderWith (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1) :
    ∃ (C : ℝ≥0), HolderWith C α.toNNReal (wFunc α (T := T)) := by
  set K : ℝ := (2 * Real.pi * (2 * T)^(1-α)) / (T * ((2:ℝ)^(1-α) - 1)) +
               (2 * (4:ℝ)^α) / (T^α * (1 - (2:ℝ)^(-α)))
  have hK_pos : 0 < K := by
    unfold_let K
    apply add_pos
    · apply div_pos (by positivity)
      apply mul_pos hT.out
      linarith [show (1:ℝ) < (2:ℝ)^(1-α) from by
        rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) from by simp]
        exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)]
    · apply div_pos (by positivity)
      apply mul_pos (Real.rpow_pos_of_pos hT.out _)
      linarith [geomRatio_lt_one α hα_pos]
  refine ⟨⟨K, hK_pos.le⟩, FourierDecayInfra.holderWith_of_dist_bound fun x y => ?_⟩
  simp only [NNReal.coe_mk, Real.coe_toNNReal α hα_pos.le]
  exact wFunc_holder_bound α hα_pos hα_lt x y

/-!
## Part V: Main Theorem
-/

/-- The frequency sequence n_k = 2^k has strictly increasing natAbs. -/
private theorem lacunary_strictMono :
    StrictMono (fun k => ((2:ℤ)^k).natAbs) := by
  intro a b hab
  simp only [Int.natAbs_pow, Int.natAbs_ofNat]
  exact Nat.pow_lt_pow_right (by norm_num) hab

/-- The Fourier coefficient bound: 1 / (2^k)^α = r^k. -/
private theorem coeff_bound (α : ℝ) (hα : 0 < α) (k : ℕ) :
    (1:ℝ) / (|(((2:ℤ)^k : ℤ) : ℝ)| ^ α) = (geomRatio α)^k := by
  simp only [Int.cast_pow, Int.cast_ofNat, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  unfold geomRatio
  rw [← Real.rpow_natCast, ← Real.rpow_natCast (2:ℝ), ← Real.rpow_mul (by norm_num)]
  simp [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]

/-- **Optimality**: For 0 < α < 1, there exists an α-Hölder function with
    Fourier coefficients ≥ 1/|n_k|^α along the lacunary sequence n_k = 2^k. -/
theorem holder_decay_is_optimal_seq_proof :
    ∀ (α : ℝ), 0 < α → α < 1 →
    ∃ (C : ℝ≥0) (f : AddCircle T → ℂ),
      HolderWith C α.toNNReal f ∧
      ∃ (c : ℝ), 0 < c ∧
      ∃ (ns : ℕ → ℤ), StrictMono (fun k => (ns k).natAbs) ∧
        ∀ k, c / |(ns k : ℝ)| ^ α ≤ ‖fourierCoeff f (ns k)‖ := by
  intro α hα_pos hα_lt
  -- Obtain Hölder constant
  obtain ⟨C, hC⟩ := wFunc_holderWith α hα_pos hα_lt (T := T)
  refine ⟨C, wFunc α, hC, 1, one_pos, fun k => (2:ℤ)^k, lacunary_strictMono, fun k => ?_⟩
  -- Prove: 1 / |(2^k : ℝ)|^α ≤ ‖fourierCoeff (wFunc α) (2^k)‖
  rw [wFunc_fourierCoeff α hα_pos k, coeff_bound α hα_pos k]
  simp [norm_pow, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (geomRatio_pos α).le _)]

end WeierstrassOptimality

end
