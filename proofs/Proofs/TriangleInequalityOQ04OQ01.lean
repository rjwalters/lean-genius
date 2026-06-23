/-
# Triangle Inequality for Geodesic Distances on Riemannian Manifolds (OQ-04-OQ-01)

S2a scaffolding: a **chart-local** Euclidean arc length, defined for paths
landing in a normed space `E`. The intended application: given a smooth manifold
`M`, a chart `(U, φ)` with `φ : U → E`, and a path `γ : ℝ → U`, the chart-local
arc length of `γ` is the integral of `‖(φ ∘ γ)'(t)‖` over the parameter interval.

For S2a we just expose `chartArcLength` on `ℝ → E` curves directly, prove the
trivial sanity lemmas (zero-length interval, constant path), and integral
nonnegativity. Subsequent iterations will add:

- S2b — additivity under path concatenation (`chartArcLength_trans`), via
  `intervalIntegral.integral_add_adjacent_intervals`.
- S2c — chart-local triangle inequality (`chartIntrinsicDist_triangle`),
  mirroring the parent `Proofs.TriangleInequalityOQ04.intrinsicDist_triangle`.

## Honest scope

This is a **chart-local** triangle inequality. The result depends on the chart
`φ` and is **not** the Riemannian distance. Mathlib v4.26.0 has no
`RiemannianMetric` typeclass; the chart-local definition is a foundation that
will lift to a chart-invariant Riemannian arc length via partition-of-unity
gluing once upstream lands the typeclass.

See `research/problems/triangle-inequality-oq-04-oq-01/` for the S1 OBSERVE
Mathlib survey and the four-path roadmap.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Data.Real.Archimedean

open MeasureTheory

namespace TriangleInequalityOQ04OQ01

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **chart-local Euclidean arc length** of a curve `γ : ℝ → E` on the
interval `[a, b]` is the integral of `‖γ'(t)‖` over `t ∈ [a, b]`.

When `γ` is the composition `φ ∘ γ̃` of a chart map `φ : U → E` with a path
`γ̃ : ℝ → U` on a smooth manifold `M`, this measures the Euclidean length of
the path's image in the chart. The result depends on the chart and is
chart-local, not Riemannian. -/
noncomputable def chartArcLength (γ : ℝ → E) (a b : ℝ) : ℝ :=
  ∫ t in a..b, ‖deriv γ t‖

/-- The arc length over a degenerate interval `[a, a]` is zero. -/
@[simp]
theorem chartArcLength_self (γ : ℝ → E) (a : ℝ) : chartArcLength γ a a = 0 := by
  simp [chartArcLength, intervalIntegral.integral_same]

/-- A constant curve has zero arc length on any interval. -/
@[simp]
theorem chartArcLength_const (c : E) (a b : ℝ) :
    chartArcLength (fun _ : ℝ => c) a b = 0 := by
  simp [chartArcLength, deriv_const']

/-- The arc length is nonnegative for `a ≤ b`, because the norm is. -/
theorem chartArcLength_nonneg (γ : ℝ → E) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ chartArcLength γ a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => norm_nonneg _)

/-- **Additivity under interval concatenation** (S2b): for any three parameter
points `a, b, c : ℝ` such that the speed `‖γ'(·)‖` is interval-integrable on
both `[a, b]` and `[b, c]`, the chart-local arc lengths over those two
intervals sum to the arc length over `[a, c]`.

The hypotheses are stated as `IntervalIntegrable` rather than the more
restrictive `a ≤ b ≤ c`, because `intervalIntegral.integral_add_adjacent_intervals`
handles the orientation-aware case (`∫_{a..b} + ∫_{b..c} = ∫_{a..c}` for any
ordering of `a, b, c`) via Mathlib's signed-interval-integral convention. This
matches the form needed for the S2c chart-local triangle inequality
(`chartIntrinsicDist_triangle`), where `b` is the intermediate endpoint of a
broken path. -/
theorem chartArcLength_trans (γ : ℝ → E) {a b c : ℝ}
    (hab : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume a b)
    (hbc : IntervalIntegrable (fun t => ‖deriv γ t‖) MeasureTheory.volume b c) :
    chartArcLength γ a b + chartArcLength γ b c = chartArcLength γ a c := by
  simp only [chartArcLength]
  exact intervalIntegral.integral_add_adjacent_intervals hab hbc

/-- The **chart-local intrinsic distance** between two points `p, q : E`: the
infimum of chart-local arc lengths over all continuous paths `γ : Path p q`
whose speed `‖deriv γ.extend (·)‖` is interval-integrable on `[0, 1]`.

The `IntervalIntegrable` side-hypothesis is essential: without restricting to
paths whose derivative is integrable, the value would collapse for pathological
reparametrisations whose speed is non-integrable (Mathlib's integral convention
returns `0` for non-strongly-measurable integrands). With it, every contributing
length is the genuine chart-local Euclidean arc length — non-negative by
`chartArcLength_nonneg` — and the infimum satisfies the triangle inequality
proved in the subsequent `chartIntrinsicDist_triangle`.

Mirrors `Proofs.TriangleInequalityOQ04.intrinsicDist`, but valued in `ℝ` (not
`ℝ≥0∞`) because `chartArcLength` is a Bochner `intervalIntegral`. The result
depends on the chart embedding and is **not** the Riemannian distance — see the
file header for the honest-scope disclaimer. -/
noncomputable def chartIntrinsicDist (p q : E) : ℝ :=
  ⨅ (γ : Path p q)
    (_ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1),
    chartArcLength γ.extend 0 1

/-- The chart-local intrinsic distance is non-negative: every contributing
`chartArcLength γ.extend 0 1` is non-negative (by `chartArcLength_nonneg` at
`0 ≤ 1`), and `Real.iInf_nonneg` lifts this through both layers of the
conditional infimum. The lemma holds unconditionally — in particular, even
when no `Path p q` satisfies the `IntervalIntegrable` side-hypothesis (in which
case the relevant `iInf` collapses to `0` via Mathlib's real-valued `sInf` of
the empty set). -/
theorem chartIntrinsicDist_nonneg (p q : E) : 0 ≤ chartIntrinsicDist p q := by
  unfold chartIntrinsicDist
  refine Real.iInf_nonneg (fun γ => ?_)
  refine Real.iInf_nonneg (fun _ => ?_)
  exact chartArcLength_nonneg γ.extend zero_le_one

/-- **Reparameterization adapter (left half)** (S3b): for `γ : ℝ → E`
differentiable on `[0, 1]`, the chart-local arc length of `γ ∘ (· * 2)` on
`[0, 1/2]` equals the chart-local arc length of `γ` on `[0, 1]`.

The proof chains three Mathlib bearers: (i) `deriv.scomp` (chain rule, giving
`deriv (γ ∘ (· * 2)) t = 2 • deriv γ (t * 2)`), (ii) `norm_smul` + `Real.norm_ofNat`
(extracting the positive scalar `‖(2 : ℝ)‖ = 2`), and (iii)
`intervalIntegral.smul_integral_comp_mul_right` (substitution `s = t * 2`,
collapsing the constant scalar and bounds in a single bearer application).

This is the left half of the broken path `Path.trans` used by the parent
`Proofs.TriangleInequalityOQ04.pathLength_trans`; together with the right half
(`chartArcLength_comp_mul_left_shift`) and additivity (`chartArcLength_trans`)
it yields concatenation additivity for `chartArcLength` along `Path.trans`. -/
private lemma chartArcLength_comp_mul_left {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2)) 0 (1 / 2) = chartArcLength γ 0 1 := by
  simp only [chartArcLength]
  have h_pointwise : Set.EqOn (fun t => ‖deriv (γ ∘ (· * 2)) t‖)
      (fun t => 2 * ‖deriv γ (t * 2)‖) (Set.uIcc (0 : ℝ) (1 / 2)) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    have ht01 : (t * 2) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hγt2 : DifferentiableAt ℝ γ (t * 2) := hγ _ ht01
    have hmul_has : HasDerivAt (fun x : ℝ => x * 2) 2 t := hasDerivAt_mul_const 2
    have hmul : DifferentiableAt ℝ (fun x : ℝ => x * 2) t := hmul_has.differentiableAt
    have h_deriv_mul : deriv (fun x : ℝ => x * 2) t = 2 := hmul_has.deriv
    show ‖deriv (γ ∘ (fun x : ℝ => x * 2)) t‖ = 2 * ‖deriv γ (t * 2)‖
    rw [deriv.scomp t hγt2 hmul, h_deriv_mul, norm_smul, Real.norm_ofNat]
  rw [intervalIntegral.integral_congr h_pointwise,
      intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_right
              (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
              (f := fun s => ‖deriv γ s‖) (c := 2)
  simp only [smul_eq_mul, zero_mul,
    show (1 / 2 : ℝ) * 2 = 1 from by norm_num] at h
  exact h

/-- **Reparameterization adapter (right half)** (S3b): for `γ : ℝ → E`
differentiable on `[0, 1]`, the chart-local arc length of `γ ∘ (· * 2 - 1)` on
`[1/2, 1]` equals the chart-local arc length of `γ` on `[0, 1]`.

Same three-bearer chain as `chartArcLength_comp_mul_left`, replacing the
substitution bearer with `intervalIntegral.smul_integral_comp_mul_sub`
(Option α from S3b PREP §4.2 — handles the affine shift `c * x - d` in a single
bearer application without decomposing into `integral_comp_add_right` +
`smul_integral_comp_mul_left`). -/
private lemma chartArcLength_comp_mul_left_shift {γ : ℝ → E}
    (hγ : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ γ t) :
    chartArcLength (γ ∘ (· * 2 - 1)) (1 / 2) 1 = chartArcLength γ 0 1 := by
  simp only [chartArcLength]
  have h_pointwise : Set.EqOn (fun t => ‖deriv (γ ∘ (· * 2 - 1)) t‖)
      (fun t => 2 * ‖deriv γ (t * 2 - 1)‖) (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    have ht01 : (t * 2 - 1) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hγst : DifferentiableAt ℝ γ (t * 2 - 1) := hγ _ ht01
    have hmul_has : HasDerivAt (fun x : ℝ => x * 2 - 1) 2 t :=
      (hasDerivAt_mul_const 2).sub_const 1
    have hmul : DifferentiableAt ℝ (fun x : ℝ => x * 2 - 1) t := hmul_has.differentiableAt
    have h_deriv_mul : deriv (fun x : ℝ => x * 2 - 1) t = 2 := hmul_has.deriv
    show ‖deriv (γ ∘ (fun x : ℝ => x * 2 - 1)) t‖ = 2 * ‖deriv γ (t * 2 - 1)‖
    rw [deriv.scomp t hγst hmul, h_deriv_mul, norm_smul, Real.norm_ofNat]
  rw [intervalIntegral.integral_congr h_pointwise,
      intervalIntegral.integral_const_mul]
  -- Bring `t * 2 - 1` into the `c * x - d` form expected by
  -- `smul_integral_comp_mul_sub` via pointwise `mul_comm`.
  have h_swap : Set.EqOn (fun t : ℝ => ‖deriv γ (t * 2 - 1)‖)
      (fun t => ‖deriv γ (2 * t - 1)‖) (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t _
    show ‖deriv γ (t * 2 - 1)‖ = ‖deriv γ (2 * t - 1)‖
    rw [mul_comm t 2]
  rw [intervalIntegral.integral_congr h_swap]
  have h := intervalIntegral.smul_integral_comp_mul_sub
              (a := (1 / 2 : ℝ)) (b := (1 : ℝ))
              (f := fun s => ‖deriv γ s‖) (c := 2) (d := 1)
  simp only [smul_eq_mul,
    show (2 : ℝ) * (1 / 2) - 1 = 0 from by norm_num,
    show (2 : ℝ) * 1 - 1 = 1 from by norm_num] at h
  exact h

omit [NormedSpace ℝ E] in
/-- On the open interval `(0, 1/2)`, the concatenated path `f.trans g`
agrees with `f.extend ∘ (· * 2)`. Stated on the *open* `Ioo` (not the closed
`Icc` of the parent's `eqOn_first`) because S3c only needs interior agreement:
each `t ∈ (0, 1/2)` has a neighborhood inside `(0, 1/2)`, which upgrades this
pointwise agreement to `Filter.EventuallyEq` and hence to a `deriv` identity. -/
private lemma eqOn_trans_first {p q r : E} (f : Path p q) (g : Path q r) :
    Set.EqOn (f.trans g).extend (f.extend ∘ (· * 2)) (Set.Ioo (0 : ℝ) (1 / 2)) := by
  intro t ht
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, by linarith [ht.2]⟩
  have h2t : t * 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  simp only [Function.comp_apply]
  rw [Path.extend_apply _ ht01, Path.trans_apply]
  simp only [dif_pos ht.2.le]
  rw [Path.extend_apply f h2t]
  congr 1; ext; ring

omit [NormedSpace ℝ E] in
/-- On the open interval `(1/2, 1)`, the concatenated path `f.trans g` agrees
with `g.extend ∘ (· * 2 - 1)`. Open-interval analogue of the parent's
`eqOn_second`, sidestepping the `t = 1/2` midpoint case entirely. -/
private lemma eqOn_trans_second {p q r : E} (f : Path p q) (g : Path q r) :
    Set.EqOn (f.trans g).extend (g.extend ∘ (· * 2 - 1)) (Set.Ioo (1 / 2 : ℝ) 1) := by
  intro t ht
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], ht.2.le⟩
  have h2t : t * 2 - 1 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hnotle : ¬ t ≤ 1 / 2 := by linarith [ht.1]
  simp only [Function.comp_apply]
  rw [Path.extend_apply _ ht01, Path.trans_apply, dif_neg hnotle, Path.extend_apply g h2t]
  congr 1; ext; ring

/-- **Concatenation additivity for `chartArcLength` along `Path.trans`** (S3c).

For paths `f : Path p q` and `g : Path q r` whose chart maps `f.extend`,
`g.extend` are differentiable on `[0, 1]`, and whose concatenated speed is
interval-integrable on `[0, 1/2]` and `[1/2, 1]`, the chart-local arc length of
`f.trans g` over `[0, 1]` is the sum of the arc lengths of `f` and `g`.

Proof: split `[0, 1]` at the midpoint via `chartArcLength_trans`; on each half
the concatenated speed agrees a.e. with the reparametrised single-path speed
(equal on the open interior by `eqOn_trans_first`/`eqOn_trans_second`, lifted to
a `deriv` identity through `Filter.EventuallyEq`, and the lone boundary point
`1/2` is Lebesgue-null), reducing each half to the adapters
`chartArcLength_comp_mul_left` / `chartArcLength_comp_mul_left_shift`. -/
theorem chartArcLength_pathTrans {p q r : E} (f : Path p q) (g : Path q r)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ f.extend t)
    (hg : ∀ t ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ g.extend t)
    (hint_left : IntervalIntegrable (fun t => ‖deriv (f.trans g).extend t‖)
      MeasureTheory.volume 0 (1 / 2))
    (hint_right : IntervalIntegrable (fun t => ‖deriv (f.trans g).extend t‖)
      MeasureTheory.volume (1 / 2) 1) :
    chartArcLength (f.trans g).extend 0 1
      = chartArcLength f.extend 0 1 + chartArcLength g.extend 0 1 := by
  rw [← chartArcLength_trans (f.trans g).extend hint_left hint_right]
  have hleft : chartArcLength (f.trans g).extend 0 (1 / 2) = chartArcLength f.extend 0 1 := by
    rw [← chartArcLength_comp_mul_left hf]
    simp only [chartArcLength]
    apply intervalIntegral.integral_congr_ae
    have key : ∀ t ∈ Set.Ioo (0 : ℝ) (1 / 2),
        ‖deriv (f.trans g).extend t‖ = ‖deriv (f.extend ∘ (· * 2)) t‖ := fun t ht => by
      have hEv : (f.trans g).extend =ᶠ[nhds t] (f.extend ∘ (· * 2)) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (eqOn_trans_first f g)
      rw [hEv.deriv_eq]
    rw [MeasureTheory.ae_iff]
    have hnull : MeasureTheory.volume ({(1 / 2 : ℝ)} : Set ℝ) = 0 := by simp
    refine measure_mono_null ?_ hnull
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    push_neg at ht
    obtain ⟨htmem, htne⟩ := ht
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at htmem
    rcases lt_or_eq_of_le htmem.2 with hlt | heq
    · exact absurd (key t ⟨htmem.1, hlt⟩) htne
    · exact heq
  have hright : chartArcLength (f.trans g).extend (1 / 2) 1 = chartArcLength g.extend 0 1 := by
    rw [← chartArcLength_comp_mul_left_shift hg]
    simp only [chartArcLength]
    apply intervalIntegral.integral_congr_ae
    have key : ∀ t ∈ Set.Ioo (1 / 2 : ℝ) 1,
        ‖deriv (f.trans g).extend t‖ = ‖deriv (g.extend ∘ (· * 2 - 1)) t‖ := fun t ht => by
      have hEv : (f.trans g).extend =ᶠ[nhds t] (g.extend ∘ (· * 2 - 1)) :=
        Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (eqOn_trans_second f g)
      rw [hEv.deriv_eq]
    rw [MeasureTheory.ae_iff]
    have hnull : MeasureTheory.volume ({(1 : ℝ)} : Set ℝ) = 0 := by simp
    refine measure_mono_null ?_ hnull
    intro t ht
    simp only [Set.mem_setOf_eq] at ht
    push_neg at ht
    obtain ⟨htmem, htne⟩ := ht
    rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at htmem
    rcases lt_or_eq_of_le htmem.2 with hlt | heq
    · exact absurd (key t ⟨htmem.1, hlt⟩) htne
    · exact heq
  rw [hleft, hright]

end TriangleInequalityOQ04OQ01
