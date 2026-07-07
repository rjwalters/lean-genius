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
    rw [integral_const]
    simp [measureReal_def, measure_univ]
  · exact integral_eq_zero_of_add_right_eq_neg (fourier_add_half_inv_index hm hT.out)

/-- The Fourier coefficient of a Fourier mode: ĉ_m(fourier n) = if n = m then 1 else 0. -/
private theorem fourierCoeff_fourier_mode (n m : ℤ) :
    fourierCoeff (fourier n : AddCircle T → ℂ) m = if n = m then 1 else 0 := by
  simp only [fourierCoeff, smul_eq_mul]
  -- Rewrite: fourier(-m)(x) * fourier(n)(x) = fourier(n - m)(x)
  have h_prod : ∀ x : AddCircle T, fourier (-m) x * fourier n x = fourier (n - m) x := by
    intro x; rw [← fourier_add]; congr 1; ring
  simp_rw [h_prod]
  -- Now ∫ x, fourier(n - m)(x) ∂μ = if n = m then 1 else 0
  rw [fourier_integral (n - m)]
  split_ifs with h1 h2 h2 <;> first | rfl | (exfalso; omega)

/-!
## Part II: The Weierstrass lacunary function
-/

/-- The geometric ratio r = 2^{-α}. For 0 < α, we have 0 < r < 1. -/
private def geomRatio (α : ℝ) : ℝ := (2 : ℝ)^(-α)

private theorem geomRatio_pos (α : ℝ) : 0 < geomRatio α :=
  Real.rpow_pos_of_pos (by norm_num) _

private theorem geomRatio_lt_one (α : ℝ) (hα : 0 < α) : geomRatio α < 1 := by
  unfold geomRatio
  rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) from by simp]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)

/-- The Weierstrass lacunary function f(x) = ∑_{k:ℕ} r^k • fourier(2^k)(x). -/
private def wFunc (α : ℝ) : AddCircle T → ℂ :=
  fun x => ∑' k : ℕ, (geomRatio α)^k • fourier ((2:ℤ)^k) x

/-- Each term in the series has norm ≤ r^k (since ‖fourier(n)(x)‖ = 1). -/
private theorem wFunc_term_norm (α : ℝ) (k : ℕ) (x : AddCircle T) :
    ‖(geomRatio α)^k • fourier ((2:ℤ)^k) x‖ ≤ (geomRatio α)^k := by
  rw [norm_smul, FourierDecayInfra.fourier_norm_eq_one,
      Real.norm_of_nonneg (pow_nonneg (geomRatio_pos α).le _), mul_one]

/-- The series defining wFunc is uniformly convergent (summable). -/
private theorem wFunc_summable (α : ℝ) (hα : 0 < α) (x : AddCircle T) :
    Summable (fun k : ℕ => (geomRatio α)^k • fourier ((2:ℤ)^k) x) := by
  exact Summable.of_norm_bounded
    (summable_geometric_of_lt_one (geomRatio_pos α).le (geomRatio_lt_one α hα))
    (fun k => wFunc_term_norm α k x)

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
          have hnorm : ‖fourier (-n) x • ((geomRatio α : ℝ)^k • fourier ((2:ℤ)^k) x)‖ ≤
              (geomRatio α)^k := by
            rw [norm_smul, norm_smul, FourierDecayInfra.fourier_norm_eq_one,
                FourierDecayInfra.fourier_norm_eq_one,
                Real.norm_of_nonneg (pow_nonneg (geomRatio_pos α).le _)]
            simp
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal hnorm
      _ = ENNReal.ofReal ((geomRatio α)^k) := by
          rw [lintegral_const, measure_univ, mul_one]
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
    from funext fun x => by rw [← tsum_mul_left]]
  rw [integral_tsum
    (fun k => (((fourier (-(2:ℤ)^k₀)).continuous.mul
      ((continuous_const.smul (fourier ((2:ℤ)^k)).continuous))).aestronglyMeasurable))
    (wFunc_norm_tsum_ne_top α hα _)]
  -- Simplify each integral: fourier(-2^k₀)(x) * r^k * fourier(2^k)(x)
  --   = r^k * fourier(2^k + (-(2^k₀)))(x)  [character multiplication]
  simp_rw [Complex.real_smul, Complex.ofReal_pow]
  have h_orth : ∀ k : ℕ,
      ∫ x : AddCircle T, fourier (-(2:ℤ)^k₀) x * (((geomRatio α : ℂ))^k * fourier ((2:ℤ)^k) x)
        ∂haarAddCircle =
      (geomRatio α : ℂ)^k * (if (2:ℤ)^k = (2:ℤ)^k₀ then 1 else 0) := by
    intro k
    have h_mul : ∀ x : AddCircle T,
        fourier (-(2:ℤ)^k₀) x * ((geomRatio α : ℂ)^k * fourier ((2:ℤ)^k) x) =
        (geomRatio α : ℂ)^k * fourier ((2:ℤ)^k + (-(2:ℤ)^k₀)) x := by
      intro x
      rw [show fourier (-(2:ℤ)^k₀) x * ((geomRatio α : ℂ)^k * fourier ((2:ℤ)^k) x) =
            (geomRatio α : ℂ)^k * (fourier ((2:ℤ)^k) x * fourier (-(2:ℤ)^k₀) x) from by ring,
          ← fourier_add]
    simp_rw [h_mul, integral_const_mul]
    rw [fourier_integral]
    simp only [add_neg_eq_zero]
  simp_rw [h_orth]
  -- The tsum picks out k = k₀
  have h_inj : ∀ k : ℕ, (2:ℤ)^k = (2:ℤ)^k₀ ↔ k = k₀ := by
    intro k
    constructor
    · intro h
      have hnat : (2:ℕ)^k = (2:ℕ)^k₀ := by exact_mod_cast h
      exact Nat.pow_right_injective (le_refl 2) hnat
    · intro h; subst h; rfl
  simp_rw [h_inj, mul_ite, mul_one, mul_zero]
  rw [tsum_ite_eq k₀]

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
    ∑ k ∈ Finset.range p, s^k ≤ s^p / (s - 1) := by
  have hs1_pos : 0 < s - 1 := by linarith
  induction p with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, pow_zero]
      exact div_nonneg zero_le_one hs1_pos.le
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc ∑ k ∈ Finset.range n, s^k + s^n
        ≤ s^n / (s-1) + s^n := by linarith
      _ = s^(n+1) / (s-1) := by
          have hne : s - 1 ≠ 0 := hs1_pos.ne'
          rw [pow_succ]; field_simp; ring

/-- The geometric tail sum: ∑_{k≥p₀} r^k = r^{p₀} / (1-r). -/
private theorem geom_tail_sum {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (p₀ : ℕ) :
    ∑' k : ℕ, r^(k + p₀) = r^p₀ / (1 - r) := by
  rw [show (fun k : ℕ => r^(k + p₀)) = fun k => r^p₀ * r^k from funext fun k => by
    rw [pow_add, mul_comm]]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0.le hr1]
  ring

/-- The diameter bound on `AddCircle T`: any two points are within `T/2`.
    Follows from `AddCircle.norm_eq` (`‖z‖ = |z.val - round (z.val/T)·T|`) and
    `abs_sub_round` (`|w - round w| ≤ 1/2`) applied to `w = (x - y)/T`. -/
private theorem dist_le_half_period (x y : AddCircle T) : dist x y ≤ T / 2 := by
  have hT_pos := hT.out
  -- Lift to real representatives
  induction x using QuotientAddGroup.induction_on with | _ x =>
  induction y using QuotientAddGroup.induction_on with | _ y =>
  have hT_ne : T ≠ 0 := hT_pos.ne'
  have h_dist : dist (↑x : AddCircle T) (↑y) =
      |x - y - round (T⁻¹ * (x - y)) * T| := by
    rw [dist_eq_norm, show (↑x : AddCircle T) - ↑y = ↑(x - y) from
      (map_sub (QuotientAddGroup.mk' (AddSubgroup.zmultiples T)) x y).symm,
      AddCircle.norm_eq]
  rw [h_dist]
  -- |x - y - k·T| = T · |(x-y)/T - round((x-y)/T)| ≤ T · (1/2) = T/2
  set k : ℤ := round (T⁻¹ * (x - y)) with hk_def
  have hround : |T⁻¹ * (x - y) - ↑k| ≤ 1 / 2 := abs_sub_round _
  have hrw : x - y - ↑k * T = T * (T⁻¹ * (x - y) - ↑k) := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos hT_pos]
  calc T * |T⁻¹ * (x - y) - ↑k| ≤ T * (1 / 2) := by
        apply mul_le_mul_of_nonneg_left hround hT_pos.le
    _ = T / 2 := by ring

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
    rw [hs_def]; rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) from by simp]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have hs_pos : 0 < s - 1 := by linarith
  have hT_pos := hT.out
  -- Handle trivial case d = 0
  set d := dist x y with hd_def
  by_cases hd : d = 0
  · have hxy : x = y := dist_eq_zero.mp hd
    subst hxy
    have hα_ne : α ≠ 0 := ne_of_gt hα_pos
    simp [hd, Real.zero_rpow hα_ne]
  have hd_pos : 0 < d := lt_of_le_of_ne dist_nonneg (Ne.symm hd)
  -- Choose split index p₀ = Nat.log 2 ⌈T/d⌉
  set n₀ : ℕ := Nat.ceil (T / d) with hn₀_def
  have hn₀_pos : 0 < n₀ := by
    rw [hn₀_def]; apply Nat.ceil_pos.mpr; positivity
  set p₀ : ℕ := Nat.log 2 n₀ with hp₀_def
  -- Key bounds: 2^{p₀} ≤ n₀ ≤ 2T/d, and T/d ≤ n₀ < 2^{p₀+1}
  have h_pow_le : (2:ℝ)^p₀ ≤ 2 * T / d := by
    calc (2:ℝ)^p₀ = ((2:ℕ)^p₀ : ℕ) := by push_cast; rfl
      _ ≤ (n₀ : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hn₀_pos.ne'
      _ ≤ 2 * T / d := by
          rw [hn₀_def]
          have hd_le_T : d ≤ T := le_trans (dist_le_half_period x y) (by linarith)
          have hTd_ge_one : (1:ℝ) ≤ T / d := (one_le_div hd_pos).mpr hd_le_T
          calc (Nat.ceil (T/d) : ℝ)
            ≤ T/d + 1 := (Nat.ceil_lt_add_one (by positivity)).le
            _ ≤ 2 * T / d := by
                rw [mul_div_assoc]; linarith
  have h_pow_gt : T / d < (2:ℝ)^(p₀+1) := by
    calc T / d ≤ (n₀ : ℝ) := by
          rw [hn₀_def]; exact Nat.le_ceil _
      _ < (2:ℝ)^(p₀+1) := by
          exact_mod_cast Nat.lt_pow_succ_log_self (by omega) n₀
  -- Key rpow bounds
  have h_s_bound : s^p₀ ≤ (2 * T / d)^(1-α) := by
    rw [hs_def]
    have hconv : ((2:ℝ)^(1-α))^p₀ = ((2:ℝ)^p₀)^(1-α) := by
      rw [← Real.rpow_natCast ((2:ℝ)^(1-α)) p₀, ← Real.rpow_natCast (2:ℝ) p₀,
          ← Real.rpow_mul (by norm_num), ← Real.rpow_mul (by norm_num), mul_comm]
    rw [hconv]
    apply Real.rpow_le_rpow (by positivity) h_pow_le; linarith
  -- Convert h_pow_gt to rpow exponent form for use below.
  have h_pow_gt' : T / d < (2:ℝ)^((p₀:ℝ)+1) := by
    rw [show ((p₀:ℝ)+1) = ((p₀+1 : ℕ):ℝ) from by push_cast; ring, Real.rpow_natCast]
    exact h_pow_gt
  have h_r_bound : r^p₀ < (4 * d / T)^α := by
    rw [hr_def]; unfold geomRatio
    -- (2^(-α))^p₀ = 2^α · (2^(p₀+1))^(-α)
    have hlhs : ((2:ℝ)^(-α))^p₀ = (2:ℝ)^α * ((2:ℝ)^((p₀:ℝ)+1))^(-α) := by
      rw [← Real.rpow_natCast ((2:ℝ)^(-α)) p₀, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
      congr 1; ring
    rw [hlhs]
    have hTd_pos : 0 < T / d := by positivity
    calc (2:ℝ)^α * ((2:ℝ)^((p₀:ℝ)+1))^(-α)
        < (2:ℝ)^α * ((T/d)^(-α)) := by
          apply mul_lt_mul_of_pos_left _ (Real.rpow_pos_of_pos (by norm_num) _)
          exact Real.rpow_lt_rpow_of_neg hTd_pos h_pow_gt' (by linarith)
      _ = (2:ℝ)^α * ((d/T)^α) := by
          rw [Real.rpow_neg hTd_pos.le,
              show (d/T) = (T/d)⁻¹ from by rw [inv_div],
              Real.inv_rpow hTd_pos.le]
      _ = (2 * (d / T))^α := by rw [Real.mul_rpow (by norm_num) (by positivity)]
      _ ≤ (4 * d / T)^α := by
          apply Real.rpow_le_rpow (by positivity) _ hα_pos.le
          rw [mul_div_assoc]; apply mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  -- The difference f(x) - f(y) = ∑' k, r^k • (fourier(2^k)(x) - fourier(2^k)(y))
  have h_diff : wFunc α x - wFunc α y =
      ∑' k : ℕ, (r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)) := by
    unfold wFunc
    rw [← Summable.tsum_sub (wFunc_summable α hα_pos x) (wFunc_summable α hα_pos y)]
    simp_rw [← smul_sub, ← hr_def]
  rw [h_diff]
  -- Summability of norms
  have h_summ_norm : Summable (fun k : ℕ => r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖) := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((summable_geometric_of_lt_one hr_pos.le hr_lt1).mul_right 2)
    apply mul_le_mul_of_nonneg_left (FourierDecayInfra.fourier_sub_norm_le_two _ _ _)
    exact pow_nonneg hr_pos.le _
  -- Norm bound via triangle inequality
  have h_norm_eq : ∀ k : ℕ, ‖r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖ =
      r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ := fun k => by
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hr_pos.le _)]
  have h_summ_norm' : Summable (fun k : ℕ => ‖r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖) := by
    simp_rw [h_norm_eq]; exact h_summ_norm
  have h_tri : ‖∑' k : ℕ, r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖ ≤
      ∑' k : ℕ, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ := by
    calc ‖∑' k, r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖
        ≤ ∑' k, ‖r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖ :=
          norm_tsum_le_tsum_norm h_summ_norm'
      _ = _ := by simp_rw [h_norm_eq]
  -- Split the tsum at p₀
  have h_split : ∑' k : ℕ, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ ≤
      (∑ k ∈ Finset.range p₀, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖) +
      ∑' k : ℕ, r^(k + p₀) * 2 := by
    rw [← h_summ_norm.sum_add_tsum_nat_add p₀]
    refine add_le_add (le_refl _) ?_
    have hf : Summable (fun k : ℕ => r^(k + p₀) * ‖fourier ((2:ℤ)^(k+p₀)) x - fourier ((2:ℤ)^(k+p₀)) y‖) :=
      (summable_nat_add_iff p₀).2 h_summ_norm
    have hg : Summable (fun k : ℕ => r^(k + p₀) * 2) :=
      (summable_nat_add_iff p₀).2 ((summable_geometric_of_lt_one hr_pos.le hr_lt1).mul_right 2)
    refine Summable.tsum_le_tsum (fun k => ?_) hf hg
    apply mul_le_mul_of_nonneg_left (FourierDecayInfra.fourier_sub_norm_le_two _ _ _)
    exact pow_nonneg hr_pos.le _
  -- Low sum bound: Lipschitz
  have h_low : ∑ k ∈ Finset.range p₀, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ ≤
      (2 * Real.pi * (2 * T)^(1-α)) / (T * ((2:ℝ)^(1-α) - 1)) * d^α := by
    calc ∑ k ∈ Finset.range p₀, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖
        ≤ ∑ k ∈ Finset.range p₀, r^k * (2 * Real.pi * (2:ℝ)^k / T * d) := by
          apply Finset.sum_le_sum; intro k _
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hr_pos.le _)
          calc ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖
              ≤ 2 * Real.pi * |(↑((2:ℤ)^k) : ℝ)| / T * d :=
                FourierDecayInfra.fourier_lipschitz_bound _ _ _
            _ = 2 * Real.pi * (2:ℝ)^k / T * d := by
                congr 2; simp [abs_of_pos (pow_pos (by norm_num : (0:ℝ) < 2) k)]
      _ = (2 * Real.pi / T * d) * ∑ k ∈ Finset.range p₀, (r * 2)^k := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro k _
          rw [mul_pow]; ring
      _ ≤ (2 * Real.pi / T * d) * (s^p₀ / (s - 1)) := by
          have hrs : r * 2 = s := by
            rw [hr_def, hs_def]; unfold geomRatio
            rw [show (1:ℝ) - α = -α + 1 from by ring, Real.rpow_add (by norm_num),
                Real.rpow_one]
          rw [hrs]
          apply mul_le_mul_of_nonneg_left (geom_partial_sum_le hs_gt1 p₀) (by positivity)
      _ ≤ (2 * Real.pi * (2 * T)^(1-α)) / (T * ((2:ℝ)^(1-α) - 1)) * d^α := by
          -- Bound s^p₀ ≤ (2T/d)^(1-α), then split (2T/d)^(1-α) = (2T)^(1-α) / d^(1-α).
          have hsm1_pos : 0 < s - 1 := hs_pos
          have hcoef_nonneg : 0 ≤ 2 * Real.pi / T * d := by positivity
          have hstep : (2 * Real.pi / T * d) * (s^p₀ / (s - 1)) ≤
              (2 * Real.pi / T * d) * ((2*T/d)^(1-α) / (s - 1)) := by
            gcongr
          refine hstep.trans (le_of_eq ?_)
          rw [hs_def]
          -- (2T/d)^(1-α) = (2T)^(1-α) · d^(α-1); combine with d and simplify.
          have hd_ne : d ≠ 0 := hd_pos.ne'
          have hexp : (2*T/d)^(1-α) = (2*T)^(1-α) * d^(α - 1) := by
            rw [Real.div_rpow (by positivity) hd_pos.le, div_eq_mul_inv,
                ← Real.rpow_neg hd_pos.le, show -(1-α) = α - 1 from by ring]
          rw [hexp]
          have hdpow : d^α = d^(α - 1) * d := by
            nth_rewrite 1 [show d^α = d^((α - 1) + 1) from by congr 1; ring]
            rw [Real.rpow_add hd_pos, Real.rpow_one]
          have hden_ne : (2:ℝ)^(1-α) - 1 ≠ 0 := by
            have h1 : (1:ℝ) < (2:ℝ)^(1-α) := by rw [← hs_def]; exact hs_gt1
            linarith
          have hT_ne : T ≠ 0 := hT_pos.ne'
          -- Substitute d^α = d^(α-1)·d on the RHS; everything is then rational in atoms.
          rw [hdpow]
          field_simp
          try ring
  -- High sum bound: trivial
  have h_high : ∑' k : ℕ, r^(k + p₀) * 2 ≤
      (2 * (4:ℝ)^α) / (T^α * (1 - (2:ℝ)^(-α))) * d^α := by
    rw [show (fun k : ℕ => r^(k+p₀) * 2) = fun k => 2 * r^(k+p₀) from funext (fun k => by ring)]
    rw [tsum_mul_left, geom_tail_sum hr_pos hr_lt1]
    -- Goal: 2 * (r^p₀ / (1 - r)) ≤ (2·4^α)/(T^α·(1-2^(-α)))·d^α
    have h1mr_pos : 0 < 1 - r := by linarith
    have hr_eq : (1:ℝ) - r = 1 - (2:ℝ)^(-α) := by rw [hr_def]; rfl
    have hden_pos : 0 < 1 - (2:ℝ)^(-α) := by rw [← hr_eq]; exact h1mr_pos
    -- (4d/T)^α = 4^α · d^α / T^α
    have hexp : (4 * d / T)^α = (4:ℝ)^α * d^α / T^α := by
      rw [show (4 * d / T) = 4 * d * T⁻¹ from by ring,
          Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by norm_num) hd_pos.le, Real.inv_rpow hT_pos.le]
      ring
    -- Rewrite both sides over the common denominator (1 - 2^(-α)).
    rw [hr_eq, show (2 : ℝ) * (r^p₀ / (1 - (2:ℝ)^(-α))) = (2 * r^p₀) / (1 - (2:ℝ)^(-α)) from by
          rw [mul_div_assoc],
        show (2 * (4:ℝ)^α) / (T^α * (1 - (2:ℝ)^(-α))) * d^α
            = (2 * ((4:ℝ)^α * d^α / T^α)) / (1 - (2:ℝ)^(-α)) from by
          rw [mul_comm (T^α) (1 - (2:ℝ)^(-α)), ← div_div, div_mul_eq_mul_div]; ring]
    gcongr (?_ / (1 - (2:ℝ)^(-α)))
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left (le_of_lt h_r_bound) (by norm_num)
  -- Combine
  rw [add_mul, hs_def]
  calc ‖∑' k : ℕ, r^k • (fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y)‖
      ≤ ∑' k : ℕ, r^k * ‖fourier ((2:ℤ)^k) x - fourier ((2:ℤ)^k) y‖ := h_tri
    _ ≤ _ + ∑' k : ℕ, r^(k + p₀) * 2 := h_split
    _ ≤ _ := add_le_add h_low h_high

/-- wFunc is α-Hölder continuous. -/
private theorem wFunc_holderWith (α : ℝ) (hα_pos : 0 < α) (hα_lt : α < 1) :
    ∃ (C : ℝ≥0), HolderWith C α.toNNReal (wFunc α (T := T)) := by
  set K : ℝ := (2 * Real.pi * (2 * T)^(1-α)) / (T * ((2:ℝ)^(1-α) - 1)) +
               (2 * (4:ℝ)^α) / (T^α * (1 - (2:ℝ)^(-α))) with hK_def
  have hT_pos := hT.out
  have h2_gt1 : (1:ℝ) < (2:ℝ)^(1-α) := by
    rw [show (1:ℝ) = (2:ℝ)^(0:ℝ) from by simp]
    exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  have h2negα_lt1 : (2:ℝ)^(-α) < 1 := by
    have := geomRatio_lt_one α hα_pos; unfold geomRatio at this; exact this
  have hK_pos : 0 < K := by
    rw [hK_def]
    apply add_pos
    · apply div_pos
      · have : (0:ℝ) < (2 * T)^(1-α) := Real.rpow_pos_of_pos (by positivity) _
        positivity
      · apply mul_pos hT_pos; linarith
    · apply div_pos
      · have : (0:ℝ) < (4:ℝ)^α := Real.rpow_pos_of_pos (by norm_num) _
        positivity
      · apply mul_pos (Real.rpow_pos_of_pos hT_pos _); linarith
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
  have h2 : (2 : ℤ).natAbs = 2 := rfl
  simp only [Int.natAbs_pow, h2]
  exact Nat.pow_lt_pow_right (by norm_num) hab

/-- The Fourier coefficient bound: 1 / (2^k)^α = r^k. -/
private theorem coeff_bound (α : ℝ) (_hα : 0 < α) (k : ℕ) :
    (1:ℝ) / (|(((2:ℤ)^k : ℤ) : ℝ)| ^ α) = (geomRatio α)^k := by
  simp only [Int.cast_pow, Int.cast_ofNat, abs_pow, abs_of_pos (by norm_num : (0:ℝ) < 2)]
  unfold geomRatio
  rw [one_div, ← Real.rpow_natCast (2:ℝ) k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), ← Real.rpow_natCast ((2:ℝ)^(-α)) k,
      ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1; ring

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
  refine le_of_eq ?_
  rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (geomRatio_pos α).le]

end WeierstrassOptimality

end
