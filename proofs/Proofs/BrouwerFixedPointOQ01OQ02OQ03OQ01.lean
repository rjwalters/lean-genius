import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Proofs.BrouwerFixedPoint

open Set Metric Real
open scoped RealInnerProductSpace

namespace BrouwerOQ01OQ02OQ03OQ01

variable {n : ℕ}

-- ============================================================
-- PART 1: Ball Clamping
-- ============================================================

-- Project any point onto the closed unit ball
noncomputable def ballClamp (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (max 1 ‖x‖)⁻¹ • x

private lemma ballClamp_denom_pos (x : EuclideanSpace ℝ (Fin n)) : 0 < max 1 ‖x‖ :=
  lt_of_lt_of_le one_pos (le_max_left 1 ‖x‖)

lemma ballClamp_norm_le (x : EuclideanSpace ℝ (Fin n)) : ‖ballClamp x‖ ≤ 1 := by
  have hd := ballClamp_denom_pos x
  simp only [ballClamp, norm_smul, norm_inv, Real.norm_of_nonneg hd.le]
  rw [inv_mul_le_iff₀ hd]
  exact le_max_right 1 ‖x‖

lemma ballClamp_mem_closedBall (x : EuclideanSpace ℝ (Fin n)) :
    ballClamp x ∈ Brouwer.ClosedBall n :=
  Metric.mem_closedBall_zero_iff.mpr (ballClamp_norm_le x)

lemma ballClamp_eq_of_mem (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Brouwer.ClosedBall n) :
    ballClamp x = x := by
  have hx' : ‖x‖ ≤ 1 := Metric.mem_closedBall_zero_iff.mp hx
  simp [ballClamp, max_eq_left hx']

lemma ballClamp_continuous : Continuous (ballClamp (n := n)) := by
  unfold ballClamp
  apply Continuous.smul
  · apply Continuous.inv₀
    · exact continuous_const.max continuous_norm
    · intro x; exact (ballClamp_denom_pos x).ne'
  · exact continuous_id

-- ============================================================
-- PART 2: Extended map has no fixed points anywhere
-- ============================================================

lemma gClamp_mem (f : Brouwer.SelfMap n) (x : EuclideanSpace ℝ (Fin n)) :
    f.toFun (ballClamp x) ∈ Brouwer.ClosedBall n :=
  f.maps_ball _ (ballClamp_mem_closedBall x)

lemma gClamp_norm_le (f : Brouwer.SelfMap n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖f.toFun (ballClamp x)‖ ≤ 1 :=
  Metric.mem_closedBall_zero_iff.mp (gClamp_mem f x)

lemma gClamp_ne_id (f : Brouwer.SelfMap n) (h : ¬Brouwer.HasFixedPoint n f)
    (x : EuclideanSpace ℝ (Fin n)) : f.toFun (ballClamp x) ≠ x := by
  by_cases hx : x ∈ Brouwer.ClosedBall n
  · rw [ballClamp_eq_of_mem x hx]
    exact fun heq => h ⟨x, hx, heq⟩
  · simp only [Brouwer.ClosedBall, Metric.mem_closedBall_zero_iff, not_le] at hx
    intro heq
    have : ‖f.toFun (ballClamp x)‖ ≤ 1 := gClamp_norm_le f x
    linarith [heq ▸ this]

-- ============================================================
-- PART 3: Quadratic formula for ray-sphere intersection
-- ============================================================

private lemma norm_sq_lin (v w : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ‖v + t • w‖ ^ 2 = ‖v‖ ^ 2 + 2 * t * ⟪v, w⟫_ℝ + t ^ 2 * ‖w‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, sq_abs]
  ring

-- The larger root of ‖v + t·w‖² = 1
noncomputable def tPlus (v w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  let b := ⟪v, w⟫_ℝ
  let disc := b ^ 2 + ‖w‖ ^ 2 * (1 - ‖v‖ ^ 2)
  (-b + Real.sqrt disc) / ‖w‖ ^ 2

private lemma disc_nonneg (v w : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) :
    ⟪v, w⟫_ℝ ^ 2 + ‖w‖ ^ 2 * (1 - ‖v‖ ^ 2) ≥ 0 := by
  apply add_nonneg (sq_nonneg _)
  apply mul_nonneg (sq_nonneg _)
  nlinarith [norm_nonneg v]

private lemma tPlus_sphere (v w : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) (hw : w ≠ 0) :
    ‖v + tPlus v w • w‖ ^ 2 = 1 := by
  set b := ⟪v, w⟫_ℝ
  set a := ‖w‖ ^ 2
  set disc := b ^ 2 + a * (1 - ‖v‖ ^ 2)
  set s := Real.sqrt disc
  have ha : 0 < a := by positivity
  have hs2 : s ^ 2 = disc := Real.sq_sqrt (disc_nonneg v w hv)
  have htP : tPlus v w = (-b + s) / a := by simp [tPlus, s, b, a, disc]
  rw [htP, norm_sq_lin]
  field_simp [ha.ne']
  nlinarith [hs2, sq_nonneg s, sq_nonneg b, disc_nonneg v w hv,
             sq_nonneg (s - b), sq_nonneg (s + b)]

private lemma tPlus_one_on_sphere (v w : EuclideanSpace ℝ (Fin n))
    (hv : ‖v‖ ≤ 1) (hvw : ‖v + w‖ = 1) (hw : w ≠ 0) : tPlus v w = 1 := by
  set b := ⟪v, w⟫_ℝ
  set a := ‖w‖ ^ 2
  set disc := b ^ 2 + a * (1 - ‖v‖ ^ 2)
  have ha : 0 < a := by positivity
  have h_vw_sq : ‖v + w‖ ^ 2 = 1 := by rw [hvw]; norm_num
  have h_expand : ‖v + w‖ ^ 2 = ‖v‖ ^ 2 + 2 * b + a := by
    have := norm_sq_lin v w 1
    simp only [one_smul, one_pow, mul_one] at this
    linarith
  have h_sum : a + 2 * b = 1 - ‖v‖ ^ 2 := by linarith
  have h_disc_eq : disc = (a + b) ^ 2 := by
    simp only [disc]
    nlinarith [h_sum, ha, sq_nonneg b]
  have hab : a + b ≥ 0 := by
    have step1 : a + b = ‖v + w‖ ^ 2 - ⟪v + w, v⟫_ℝ := by
      simp only [a, b, inner_add_left, real_inner_comm w v, real_inner_self_eq_norm_sq]
      ring
    have step2 : ⟪v + w, v⟫_ℝ ≤ 1 :=
      calc ⟪v + w, v⟫_ℝ
          ≤ |⟪v + w, v⟫_ℝ| := le_abs_self _
        _ ≤ ‖v + w‖ * ‖v‖ := abs_real_inner_le_norm _ _
        _ ≤ 1 * 1 := by rw [hvw]; exact mul_le_mul_of_nonneg_left hv (by norm_num)
        _ = 1 := one_mul _
    linarith [step1, h_vw_sq]
  have hsqrt : Real.sqrt disc = a + b := by
    rw [h_disc_eq]; exact Real.sqrt_sq hab
  simp only [tPlus, b, a, disc, hsqrt]
  field_simp [ha.ne']
  ring

-- ============================================================
-- PART 4: The retraction function
-- ============================================================

noncomputable def retractionFun (f : Brouwer.SelfMap n)
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  let v := f.toFun (ballClamp x)
  v + tPlus v (x - v) • (x - v)

lemma retractionFun_maps_to_sphere (f : Brouwer.SelfMap n) (h : ¬Brouwer.HasFixedPoint n f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Brouwer.ClosedBall n) :
    retractionFun f x ∈ Brouwer.UnitSphere n := by
  simp only [Brouwer.UnitSphere, Metric.mem_sphere_zero_iff_norm, retractionFun]
  set v := f.toFun (ballClamp x)
  set w := x - v
  have hv : ‖v‖ ≤ 1 := gClamp_norm_le f x
  have hw : w ≠ 0 := sub_ne_zero.mpr (gClamp_ne_id f h x)
  have hn2 : ‖v + tPlus v w • w‖ ^ 2 = 1 := tPlus_sphere v w hv hw
  nlinarith [norm_nonneg (v + tPlus v w • w), sq_nonneg (‖v + tPlus v w • w‖ - 1),
             sq_nonneg (‖v + tPlus v w • w‖ + 1)]

lemma retractionFun_fixes_sphere (f : Brouwer.SelfMap n) (h : ¬Brouwer.HasFixedPoint n f)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ Brouwer.UnitSphere n) :
    retractionFun f x = x := by
  simp only [Brouwer.UnitSphere, Metric.mem_sphere_zero_iff_norm] at hx
  simp only [retractionFun]
  set v := f.toFun (ballClamp x)
  set w := x - v
  have hv : ‖v‖ ≤ 1 := gClamp_norm_le f x
  have hvw : ‖v + w‖ = 1 := by simp [w, hx]
  have hw : w ≠ 0 := sub_ne_zero.mpr (gClamp_ne_id f h x)
  have ht1 : tPlus v w = 1 := tPlus_one_on_sphere v w hv hvw hw
  simp [ht1, w]

lemma retractionFun_continuous (f : Brouwer.SelfMap n) (h : ¬Brouwer.HasFixedPoint n f) :
    Continuous (retractionFun f) := by
  simp only [retractionFun]
  have hv_cts : Continuous (fun x => f.toFun (ballClamp x)) :=
    f.continuous'.comp ballClamp_continuous
  have hw_cts : Continuous (fun x : EuclideanSpace ℝ (Fin n) => x - f.toFun (ballClamp x)) :=
    continuous_id.sub hv_cts
  have ha_ne : ∀ x : EuclideanSpace ℝ (Fin n), ‖x - f.toFun (ballClamp x)‖ ^ 2 ≠ 0 := fun x =>
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (gClamp_ne_id f h x)))
  have ht_cts : Continuous (fun x =>
      tPlus (f.toFun (ballClamp x)) (x - f.toFun (ballClamp x))) := by
    unfold tPlus
    apply Continuous.div
    · apply Continuous.add
      · exact (hv_cts.inner hw_cts).neg
      · apply Real.continuous_sqrt.comp
        apply Continuous.add
        · exact (hv_cts.inner hw_cts).pow 2
        · exact (hw_cts.norm.pow 2).mul (continuous_const.sub (hv_cts.norm.pow 2))
    · exact hw_cts.norm.pow 2
    · exact ha_ne
  exact hv_cts.add (ht_cts.smul hw_cts)

-- ============================================================
-- PART 5: Main theorem — retraction_construction is provable
-- ============================================================

/-- The retraction construction axiom in BrouwerFixedPoint.lean can be proved:
    given a continuous self-map with no fixed point, the ray construction
    explicitly builds a retraction from the ball to the sphere. -/
theorem retraction_construction_theorem {n : ℕ} (f : Brouwer.SelfMap n)
    (h : ¬Brouwer.HasFixedPoint n f) : Brouwer.Retraction n where
  toFun := retractionFun f
  continuous' := retractionFun_continuous f h
  maps_to_sphere := fun x hx => retractionFun_maps_to_sphere f h hx
  fixes_sphere := fun x hx => retractionFun_fixes_sphere f h hx

/-- Brouwer fixed point theorem proved without the retraction_construction axiom. -/
theorem brouwer_fixed_point_explicit (hn : n ≥ 1) (f : Brouwer.SelfMap n) :
    Brouwer.HasFixedPoint n f := by
  by_contra h
  exact Brouwer.no_retraction hn ⟨retraction_construction_theorem f h, trivial⟩

end BrouwerOQ01OQ02OQ03OQ01
