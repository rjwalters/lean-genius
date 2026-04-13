/-
  Binary Entropy Strict Concavity

  Open Question (shannon-channel-coding-oq-04-oq-01):
  "Prove strict concavity of binary entropy h(p) = -p·log(p) - (1-p)·log(1-p) on (0,1)."

  Mathlib provides `strictConcaveOn_of_deriv2_neg` with signature:
    (hD : Convex ℝ D) (hf : ContinuousOn f D)
    (hf'' : ∀ x ∈ interior D, deriv^[2] f x < 0) : StrictConcaveOn ℝ D f

  We apply this with:
  - h'(p) = log(1-p) - log(p)  [via product rule + chain rule]
  - h''(p) = -1/(1-p) - 1/p < 0 on (0,1)

  References:
  - ShannonChannelCodingOQ04 for h definition and weak concavity
  - Mathlib.Analysis.Convex.Deriv for strictConcaveOn_of_deriv2_neg
-/
import Mathlib
import Proofs.ShannonChannelCodingOQ04

open Real Set Filter Topology

namespace InformationTheory.BinaryEntropy

-- ============================================================
-- Section 1: First Derivative of h
-- ============================================================

/-- h'(p) = log(1-p) - log(p) at any p ∈ (0,1). -/
lemma h_hasDerivAt (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt h (Real.log (1 - p) - Real.log p) p := by
  have h1p0 : (0:ℝ) < 1 - p := by linarith
  -- Derivative of x * log x at p
  have hd_xlogx : HasDerivAt (fun x => x * Real.log x) (Real.log p + 1) p := by
    have h := (hasDerivAt_id p).mul (Real.hasDerivAt_log (ne_of_gt hp0))
    simp only [id, one_mul] at h
    rwa [mul_inv_cancel₀ (ne_of_gt hp0)] at h
  -- Derivative of (1-x)*log(1-x) at p
  have hd_1xlog1x : HasDerivAt (fun x => (1 - x) * Real.log (1 - x))
      (-Real.log (1 - p) - 1) p := by
    have hd_at : HasDerivAt (fun y => y * Real.log y) (Real.log (1 - p) + 1) (1 - p) := by
      have h := (hasDerivAt_id (1-p)).mul (Real.hasDerivAt_log (ne_of_gt h1p0))
      simp only [id, one_mul] at h
      rwa [mul_inv_cancel₀ (ne_of_gt h1p0)] at h
    have hd_sub : HasDerivAt (fun x => 1 - x) (-1) p := by
      simpa [id, zero_sub] using (hasDerivAt_const p 1).sub (hasDerivAt_id p)
    have h := hd_at.comp p hd_sub
    convert h using 1; ring
  -- h = -(x*log x + (1-x)*log(1-x))
  unfold h
  convert (hd_xlogx.add hd_1xlog1x).neg using 1; ring

-- ============================================================
-- Section 2: Second Derivative of h
-- ============================================================

/-- The second derivative: d/dp[log(1-p) - log(p)] = -1/(1-p) - 1/p. -/
lemma h_hasDerivAt2 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    HasDerivAt (fun x => Real.log (1 - x) - Real.log x)
      (-1 / (1 - p) - 1 / p) p := by
  have h1p0 : (0:ℝ) < 1 - p := by linarith
  have hd_log1x : HasDerivAt (fun x => Real.log (1 - x)) (-1 / (1 - p)) p := by
    have hd_sub : HasDerivAt (fun x => 1 - x) (-1) p := by
      simpa [id, zero_sub] using (hasDerivAt_const p 1).sub (hasDerivAt_id p)
    have hd_log : HasDerivAt Real.log (1 - p)⁻¹ (1 - p) :=
      Real.hasDerivAt_log (ne_of_gt h1p0)
    have h := hd_log.comp p hd_sub
    have heq : (-1 / (1 - p) : ℝ) = (1 - p)⁻¹ * (-1) := by
      rw [div_eq_mul_inv]; ring
    rw [heq]; exact h
  have hd_logx : HasDerivAt Real.log (1 / p) p := by
    rw [one_div]
    exact Real.hasDerivAt_log (ne_of_gt hp0)
  exact hd_log1x.sub hd_logx

-- ============================================================
-- Section 3: Second Derivative is Negative
-- ============================================================

/-- h''(p) < 0 for all p ∈ (0,1). -/
lemma h_deriv2_neg (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    -1 / (1 - p) - 1 / p < 0 := by
  have h1p0 : (0:ℝ) < 1 - p := by linarith
  have h1 : 0 < 1 / (1 - p) := div_pos one_pos h1p0
  have h2 : 0 < 1 / p := div_pos one_pos hp0
  have heq : -1 / (1 - p) - 1 / p = -(1 / (1 - p) + 1 / p) := by ring
  rw [heq]; linarith [add_pos h1 h2]

-- ============================================================
-- Section 4: Main Theorem
-- ============================================================

/-- **Binary Entropy Strict Concavity** (shannon-channel-coding-oq-04-oq-01):
    h is strictly concave on the open interval (0,1).

    Proof: Apply `strictConcaveOn_of_deriv2_neg` using:
    - h is continuous on (0,1)
    - deriv^[2] h x = h''(x) = -1/(1-x) - 1/x < 0 on (0,1) -/
theorem h_strictConcaveOn : StrictConcaveOn ℝ (Ioo 0 1) h := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioo 0 1)
  · -- ContinuousOn h (Ioo 0 1)
    unfold h
    apply ContinuousOn.neg
    apply ContinuousOn.add
    · exact continuousOn_id.mul (continuousOn_id.log (fun x hx => ne_of_gt hx.1))
    · exact (continuousOn_const.sub continuousOn_id).mul
        ((continuousOn_const.sub continuousOn_id).log
          (fun x hx => ne_of_gt (by simp only [id_eq]; linarith [hx.2])))
  · intro x hx
    -- interior (Ioo 0 1) = Ioo 0 1
    rw [interior_Ioo] at hx
    have hx0 : (0:ℝ) < x := hx.1
    have hx1 : x < 1 := hx.2
    -- Unfold deriv^[2]
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp, id_eq]
    -- deriv h =ᶠ[𝓝 x] fun y => log(1-y) - log y
    have heq : deriv h =ᶠ[𝓝 x] (fun y => Real.log (1 - y) - Real.log y) := by
      apply Filter.eventually_of_mem (Ioo_mem_nhds hx0 hx1)
      intro y hy
      exact (h_hasDerivAt y hy.1 hy.2).deriv
    -- Reduce to second derivative of log(1-y) - log y at x
    rw [EventuallyEq.deriv_eq heq, (h_hasDerivAt2 x hx0 hx1).deriv]
    exact h_deriv2_neg x hx0 hx1

end InformationTheory.BinaryEntropy
