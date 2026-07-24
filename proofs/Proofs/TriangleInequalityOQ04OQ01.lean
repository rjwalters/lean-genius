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

/-- **Unconditional chain rule for the dilation `· * 2`** (S3d): the identity
`deriv (γ ∘ (· * 2)) t = 2 • deriv γ (t * 2)` holds for EVERY curve `γ`, with no
differentiability hypothesis. When `γ` is differentiable at `t * 2` this is the
chain rule (`deriv.scomp`); otherwise both sides are Mathlib's junk value `0`:
the right by `deriv_zero_of_not_differentiableAt` directly, the left because a
differentiable `γ ∘ (· * 2)` would transport back through the inverse dilation
`· * (1/2)` and make `γ` differentiable at `t * 2` — contradiction.

This unconditional form is what lets the S3d triangle inequality range over
*all* integrable-speed paths (the infimum class of `chartIntrinsicDist`), not
just everywhere-differentiable ones. -/
private lemma deriv_comp_mul_two (γ : ℝ → E) (t : ℝ) :
    deriv (γ ∘ (· * 2)) t = (2 : ℝ) • deriv γ (t * 2) := by
  by_cases hγ : DifferentiableAt ℝ γ (t * 2)
  · have hmul_has : HasDerivAt (fun x : ℝ => x * 2) 2 t := hasDerivAt_mul_const 2
    rw [deriv.scomp t hγ hmul_has.differentiableAt, hmul_has.deriv]
  · have hcomp : ¬ DifferentiableAt ℝ (γ ∘ (· * 2)) t := by
      intro h
      apply hγ
      have hg : γ = (γ ∘ (· * 2)) ∘ (· * (1 / 2 : ℝ)) := by
        funext s
        simp only [Function.comp_apply]
        congr 1
        ring
      have h' : DifferentiableAt ℝ (γ ∘ (· * 2)) (t * 2 * (1 / 2 : ℝ)) := by
        rw [show t * 2 * (1 / 2 : ℝ) = t from by ring]
        exact h
      rw [hg]
      exact DifferentiableAt.comp (t * 2) h'
        (hasDerivAt_mul_const (1 / 2 : ℝ)).differentiableAt
    rw [deriv_zero_of_not_differentiableAt hcomp,
      deriv_zero_of_not_differentiableAt hγ, smul_zero]

/-- **Unconditional chain rule for the affine map `· * 2 - 1`** (S3d): companion
of `deriv_comp_mul_two` for the right-half reparameterization; same junk-value
bilateral argument through the inverse affine map `(· + 1) * (1/2)`. -/
private lemma deriv_comp_mul_two_sub (γ : ℝ → E) (t : ℝ) :
    deriv (γ ∘ (· * 2 - 1)) t = (2 : ℝ) • deriv γ (t * 2 - 1) := by
  by_cases hγ : DifferentiableAt ℝ γ (t * 2 - 1)
  · have hmul_has : HasDerivAt (fun x : ℝ => x * 2 - 1) 2 t :=
      (hasDerivAt_mul_const 2).sub_const 1
    rw [deriv.scomp t hγ hmul_has.differentiableAt, hmul_has.deriv]
  · have hcomp : ¬ DifferentiableAt ℝ (γ ∘ (· * 2 - 1)) t := by
      intro h
      apply hγ
      have hg : γ = (γ ∘ (· * 2 - 1)) ∘ (fun s : ℝ => (s + 1) * (1 / 2)) := by
        funext s
        simp only [Function.comp_apply]
        congr 1
        ring
      have h' : DifferentiableAt ℝ (γ ∘ (· * 2 - 1)) ((t * 2 - 1 + 1) * (1 / 2 : ℝ)) := by
        rw [show (t * 2 - 1 + 1) * (1 / 2 : ℝ) = t from by ring]
        exact h
      rw [hg]
      refine DifferentiableAt.comp (t * 2 - 1) h' ?_
      exact (((hasDerivAt_id _).add_const 1).mul_const (1 / 2 : ℝ)).differentiableAt
    rw [deriv_zero_of_not_differentiableAt hcomp,
      deriv_zero_of_not_differentiableAt hγ, smul_zero]

/-- **Reparameterization adapter (left half)** (S3b, strengthened at S3d): for
EVERY curve `γ : ℝ → E` — no differentiability hypothesis — the chart-local arc
length of `γ ∘ (· * 2)` on `[0, 1/2]` equals the chart-local arc length of `γ`
on `[0, 1]`.

The proof chains three Mathlib bearers: (i) the unconditional
`deriv_comp_mul_two` (chain rule with junk-value bilateral fallback), (ii)
`norm_smul` + `Real.norm_ofNat` (extracting the positive scalar `‖(2 : ℝ)‖ = 2`),
and (iii) `intervalIntegral.smul_integral_comp_mul_right` (substitution
`s = t * 2`, collapsing the constant scalar and bounds in a single bearer
application).

This is the left half of the broken path `Path.trans` used by the parent
`Proofs.TriangleInequalityOQ04.pathLength_trans`; together with the right half
(`chartArcLength_comp_mul_left_shift`) and additivity (`chartArcLength_trans`)
it yields concatenation additivity for `chartArcLength` along `Path.trans`. -/
private lemma chartArcLength_comp_mul_left (γ : ℝ → E) :
    chartArcLength (γ ∘ (· * 2)) 0 (1 / 2) = chartArcLength γ 0 1 := by
  simp only [chartArcLength]
  have h_pointwise : Set.EqOn (fun t => ‖deriv (γ ∘ (· * 2)) t‖)
      (fun t => 2 * ‖deriv γ (t * 2)‖) (Set.uIcc (0 : ℝ) (1 / 2)) := by
    intro t _
    show ‖deriv (γ ∘ (· * 2)) t‖ = 2 * ‖deriv γ (t * 2)‖
    rw [deriv_comp_mul_two, norm_smul, Real.norm_ofNat]
  rw [intervalIntegral.integral_congr h_pointwise,
      intervalIntegral.integral_const_mul]
  have h := intervalIntegral.smul_integral_comp_mul_right
              (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
              (f := fun s => ‖deriv γ s‖) (c := 2)
  simp only [smul_eq_mul, zero_mul,
    show (1 / 2 : ℝ) * 2 = 1 from by norm_num] at h
  exact h

/-- **Reparameterization adapter (right half)** (S3b, strengthened at S3d): for
EVERY curve `γ : ℝ → E` — no differentiability hypothesis — the chart-local arc
length of `γ ∘ (· * 2 - 1)` on `[1/2, 1]` equals the chart-local arc length of
`γ` on `[0, 1]`.

Same three-bearer chain as `chartArcLength_comp_mul_left` (via the unconditional
`deriv_comp_mul_two_sub`), replacing the substitution bearer with
`intervalIntegral.smul_integral_comp_mul_sub` (Option α from S3b PREP §4.2 —
handles the affine shift `c * x - d` in a single bearer application without
decomposing into `integral_comp_add_right` + `smul_integral_comp_mul_left`). -/
private lemma chartArcLength_comp_mul_left_shift (γ : ℝ → E) :
    chartArcLength (γ ∘ (· * 2 - 1)) (1 / 2) 1 = chartArcLength γ 0 1 := by
  simp only [chartArcLength]
  have h_pointwise : Set.EqOn (fun t => ‖deriv (γ ∘ (· * 2 - 1)) t‖)
      (fun t => 2 * ‖deriv γ (t * 2 - 1)‖) (Set.uIcc (1 / 2 : ℝ) 1) := by
    intro t _
    show ‖deriv (γ ∘ (· * 2 - 1)) t‖ = 2 * ‖deriv γ (t * 2 - 1)‖
    rw [deriv_comp_mul_two_sub, norm_smul, Real.norm_ofNat]
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

/-- **Concatenation additivity for `chartArcLength` along `Path.trans`** (S3c,
strengthened at S3d: no differentiability hypotheses).

For ANY paths `f : Path p q` and `g : Path q r` whose concatenated speed is
interval-integrable on `[0, 1/2]` and `[1/2, 1]`, the chart-local arc length of
`f.trans g` over `[0, 1]` is the sum of the arc lengths of `f` and `g`.

Proof: split `[0, 1]` at the midpoint via `chartArcLength_trans`; on each half
the concatenated speed agrees a.e. with the reparametrised single-path speed
(equal on the open interior by `eqOn_trans_first`/`eqOn_trans_second`, lifted to
a `deriv` identity through `Filter.EventuallyEq`, and the lone boundary point
`1/2` is Lebesgue-null), reducing each half to the adapters
`chartArcLength_comp_mul_left` / `chartArcLength_comp_mul_left_shift`. -/
theorem chartArcLength_pathTrans {p q r : E} (f : Path p q) (g : Path q r)
    (hint_left : IntervalIntegrable (fun t => ‖deriv (f.trans g).extend t‖)
      MeasureTheory.volume 0 (1 / 2))
    (hint_right : IntervalIntegrable (fun t => ‖deriv (f.trans g).extend t‖)
      MeasureTheory.volume (1 / 2) 1) :
    chartArcLength (f.trans g).extend 0 1
      = chartArcLength f.extend 0 1 + chartArcLength g.extend 0 1 := by
  rw [← chartArcLength_trans (f.trans g).extend hint_left hint_right]
  have hleft : chartArcLength (f.trans g).extend 0 (1 / 2) = chartArcLength f.extend 0 1 := by
    rw [← chartArcLength_comp_mul_left f.extend]
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
    rw [← chartArcLength_comp_mul_left_shift g.extend]
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

/-! ### S3d: the chart-local triangle inequality

The remaining assembly. Two genuine subtleties absent from the S3 PREP estimate:

1. **The infimum class carries no differentiability**, so the S3b/S3c chain had
   to be strengthened to unconditional form (`deriv_comp_mul_two` and friends —
   done above).
2. **The ℝ-valued double-binder infimum collapses**: for a path `γ` whose speed
   is NOT interval-integrable, the inner `⨅ _ : (… : Prop), …` ranges over an
   empty index and equals `Real.sInf ∅ = 0`. Hence `chartIntrinsicDist p q = 0`
   as soon as one inadmissible path exists. The triangle inequality is still
   TRUE, but the proof needs a case analysis: if either side's factor is
   inadmissible, concatenating it with a straight-line witness produces an
   inadmissible `p → r` path, collapsing the LEFT side to `0` as well. The
   integrability-transport iffs below carry that argument in both directions. -/

/-- Transport of speed-integrability between the left half of a concatenation
and its first factor. Needed as an **iff**: forwards to assemble admissible
concatenations, backwards for the collapse analysis. -/
private lemma intervalIntegrable_trans_left_iff {p q r : E} (f : Path p q) (g : Path q r) :
    IntervalIntegrable (fun t => ‖deriv (f.trans g).extend t‖)
        MeasureTheory.volume 0 (1 / 2) ↔
      IntervalIntegrable (fun t => ‖deriv f.extend t‖) MeasureTheory.volume 0 1 := by
  have h1 : Set.EqOn (fun t => ‖deriv (f.trans g).extend t‖)
      (fun t => 2 * ‖deriv f.extend (t * 2)‖) (Set.uIoo (0 : ℝ) (1 / 2)) := by
    intro t ht
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
    have hEv : (f.trans g).extend =ᶠ[nhds t] (f.extend ∘ (· * 2)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (eqOn_trans_first f g)
    show ‖deriv (f.trans g).extend t‖ = 2 * ‖deriv f.extend (t * 2)‖
    rw [hEv.deriv_eq, deriv_comp_mul_two, norm_smul, Real.norm_ofNat]
  rw [intervalIntegrable_congr_uIoo h1]
  have hiff : IntervalIntegrable (fun x => ‖deriv f.extend (2 * x)‖)
      MeasureTheory.volume 0 (1 / 2) ↔
      IntervalIntegrable (fun t => ‖deriv f.extend t‖) MeasureTheory.volume 0 1 := by
    have h := IntervalIntegrable.comp_mul_left_iff
      (f := fun s => ‖deriv f.extend s‖) (a := 0) (b := 1) (c := 2) (by norm_num)
    rwa [show (0 : ℝ) / 2 = 0 from by norm_num] at h
  constructor
  · intro h
    have h2 : IntervalIntegrable (fun x => ‖deriv f.extend (2 * x)‖)
        MeasureTheory.volume 0 (1 / 2) := by
      refine (h.const_mul (1 / 2 : ℝ)).congr fun t _ => ?_
      show (1 / 2 : ℝ) * (2 * ‖deriv f.extend (t * 2)‖) = ‖deriv f.extend (2 * t)‖
      rw [mul_comm t 2]; ring
    exact hiff.mp h2
  · intro h
    refine ((hiff.mpr h).const_mul (2 : ℝ)).congr fun t _ => ?_
    show (2 : ℝ) * ‖deriv f.extend (2 * t)‖ = 2 * ‖deriv f.extend (t * 2)‖
    rw [mul_comm 2 t]

/-- Transport of speed-integrability between the right half of a concatenation
and its second factor (iff; chained affine substitution `· - 1` then `2 * ·`). -/
private lemma intervalIntegrable_trans_right_iff {p q r : E} (f : Path p q) (g : Path q r) :
    IntervalIntegrable (fun t => ‖deriv (f.trans g).extend t‖)
        MeasureTheory.volume (1 / 2) 1 ↔
      IntervalIntegrable (fun t => ‖deriv g.extend t‖) MeasureTheory.volume 0 1 := by
  have h1 : Set.EqOn (fun t => ‖deriv (f.trans g).extend t‖)
      (fun t => 2 * ‖deriv g.extend (t * 2 - 1)‖) (Set.uIoo (1 / 2 : ℝ) 1) := by
    intro t ht
    rw [Set.uIoo_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
    have hEv : (f.trans g).extend =ᶠ[nhds t] (g.extend ∘ (· * 2 - 1)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) (eqOn_trans_second f g)
    show ‖deriv (f.trans g).extend t‖ = 2 * ‖deriv g.extend (t * 2 - 1)‖
    rw [hEv.deriv_eq, deriv_comp_mul_two_sub, norm_smul, Real.norm_ofNat]
  rw [intervalIntegrable_congr_uIoo h1]
  have hsub : IntervalIntegrable (fun x => ‖deriv g.extend (x - 1)‖)
      MeasureTheory.volume 1 2 ↔
      IntervalIntegrable (fun t => ‖deriv g.extend t‖) MeasureTheory.volume 0 1 := by
    have h := IntervalIntegrable.comp_sub_right_iff
      (f := fun s => ‖deriv g.extend s‖) (a := 0) (b := 1) (c := 1)
    rwa [show (0 : ℝ) + 1 = 1 from by norm_num, show (1 : ℝ) + 1 = 2 from by norm_num] at h
  have hmul : IntervalIntegrable (fun x => ‖deriv g.extend (2 * x - 1)‖)
      MeasureTheory.volume (1 / 2) 1 ↔
      IntervalIntegrable (fun x => ‖deriv g.extend (x - 1)‖) MeasureTheory.volume 1 2 := by
    have h := IntervalIntegrable.comp_mul_left_iff
      (f := fun x => ‖deriv g.extend (x - 1)‖) (a := 1) (b := 2) (c := 2) (by norm_num)
    rwa [show (2 : ℝ) / 2 = 1 from by norm_num] at h
  constructor
  · intro h
    have h2 : IntervalIntegrable (fun x => ‖deriv g.extend (2 * x - 1)‖)
        MeasureTheory.volume (1 / 2) 1 := by
      refine (h.const_mul (1 / 2 : ℝ)).congr fun t _ => ?_
      show (1 / 2 : ℝ) * (2 * ‖deriv g.extend (t * 2 - 1)‖) = ‖deriv g.extend (2 * t - 1)‖
      rw [mul_comm t 2]; ring
    exact hsub.mp (hmul.mp h2)
  · intro h
    refine ((hmul.mpr (hsub.mpr h)).const_mul (2 : ℝ)).congr fun t _ => ?_
    show (2 : ℝ) * ‖deriv g.extend (2 * t - 1)‖ = 2 * ‖deriv g.extend (t * 2 - 1)‖
    rw [mul_comm 2 t]

/-- The straight-line path `t ↦ p + t • (q - p)` from `p` to `q`: the witness
making every admissible-path class nonempty. -/
noncomputable def straightPath (p q : E) : Path p q where
  toFun t := p + (t : ℝ) • (q - p)
  continuous_toFun := continuous_const.add (continuous_subtype_val.smul continuous_const)
  source' := by simp
  target' := by simp

private lemma straightPath_deriv {p q : E} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    deriv (straightPath p q).extend t = q - p := by
  have hEv : (straightPath p q).extend =ᶠ[nhds t] (fun s => p + s • (q - p)) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) fun s hs => ?_
    rw [Path.extend_apply _ ⟨hs.1.le, hs.2.le⟩]
    rfl
  rw [hEv.deriv_eq]
  simpa using (((hasDerivAt_id t).smul_const (q - p)).const_add p).deriv

/-- The straight-line path is admissible: its chart speed agrees with the
constant `‖q - p‖` on the open unit interval, hence is interval-integrable. -/
lemma straightPath_integrable (p q : E) :
    IntervalIntegrable (fun t => ‖deriv (straightPath p q).extend t‖)
      MeasureTheory.volume 0 1 := by
  have h : Set.EqOn (fun _ : ℝ => ‖q - p‖)
      (fun t => ‖deriv (straightPath p q).extend t‖) (Set.uIoo (0 : ℝ) 1) := by
    intro t ht
    rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    show ‖q - p‖ = ‖deriv (straightPath p q).extend t‖
    rw [straightPath_deriv ht]
  exact IntervalIntegrable.congr_uIoo (intervalIntegrable_const (c := ‖q - p‖)) h

/-- The inner conditional infimum of `chartIntrinsicDist`: the arc length of
`γ` when its speed is integrable, `0` (`= Real.sInf ∅`) otherwise. -/
private noncomputable def innerLength {p q : E} (γ : Path p q) : ℝ :=
  ⨅ _ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1,
    chartArcLength γ.extend 0 1

private lemma chartIntrinsicDist_eq (p q : E) :
    chartIntrinsicDist p q = ⨅ γ : Path p q, innerLength γ := rfl

private lemma innerLength_nonneg {p q : E} (γ : Path p q) : 0 ≤ innerLength γ :=
  Real.iInf_nonneg fun _ => chartArcLength_nonneg γ.extend zero_le_one

private lemma innerLength_of_integrable {p q : E} {γ : Path p q}
    (h : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1) :
    innerLength γ = chartArcLength γ.extend 0 1 := by
  haveI : Nonempty (IntervalIntegrable (fun t => ‖deriv γ.extend t‖)
    MeasureTheory.volume 0 1) := ⟨h⟩
  exact ciInf_const

private lemma innerLength_of_not_integrable {p q : E} {γ : Path p q}
    (h : ¬ IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1) :
    innerLength γ = 0 := by
  haveI : IsEmpty (IntervalIntegrable (fun t => ‖deriv γ.extend t‖)
    MeasureTheory.volume 0 1) := ⟨h⟩
  rw [innerLength, iInf, Set.range_eq_empty, Real.sInf_empty]

private lemma bddBelow_innerLength (p q : E) :
    BddBelow (Set.range fun γ : Path p q => innerLength γ) := by
  refine ⟨0, ?_⟩
  rintro x ⟨γ, rfl⟩
  exact innerLength_nonneg γ

/-- Every admissible path bounds the chart-local intrinsic distance. -/
theorem chartIntrinsicDist_le_chartArcLength {p q : E} (γ : Path p q)
    (hγ : IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1) :
    chartIntrinsicDist p q ≤ chartArcLength γ.extend 0 1 := by
  rw [chartIntrinsicDist_eq]
  exact le_trans (ciInf_le (bddBelow_innerLength p q) γ)
    (le_of_eq (innerLength_of_integrable hγ))

/-- **Degeneracy of the ℝ-valued definition**: one inadmissible path collapses
the distance to `0` (its inner infimum is `Real.sInf ∅ = 0`). Recorded as an
explicit lemma because the triangle inequality's proof must route around it. -/
theorem chartIntrinsicDist_eq_zero_of_not_integrable {p q : E} (γ : Path p q)
    (hγ : ¬ IntervalIntegrable (fun t => ‖deriv γ.extend t‖) MeasureTheory.volume 0 1) :
    chartIntrinsicDist p q = 0 := by
  refine le_antisymm ?_ (chartIntrinsicDist_nonneg p q)
  rw [chartIntrinsicDist_eq]
  exact le_trans (ciInf_le (bddBelow_innerLength p q) γ)
    (le_of_eq (innerLength_of_not_integrable hγ))

/-- **Concatenation bound**: for admissible `f : p → q` and `g : q → r`, the
distance `p → r` is at most the sum of the two arc lengths. This is the
mathematically load-bearing half of the triangle inequality: glue the paths,
transport integrability to the halves, and apply `chartArcLength_pathTrans`. -/
theorem chartIntrinsicDist_le_add {p q r : E} (f : Path p q) (g : Path q r)
    (hf : IntervalIntegrable (fun t => ‖deriv f.extend t‖) MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable (fun t => ‖deriv g.extend t‖) MeasureTheory.volume 0 1) :
    chartIntrinsicDist p r ≤ chartArcLength f.extend 0 1 + chartArcLength g.extend 0 1 := by
  have hl := (intervalIntegrable_trans_left_iff f g).mpr hf
  have hr := (intervalIntegrable_trans_right_iff f g).mpr hg
  calc chartIntrinsicDist p r ≤ chartArcLength (f.trans g).extend 0 1 :=
        chartIntrinsicDist_le_chartArcLength (f.trans g) (hl.trans hr)
    _ = chartArcLength f.extend 0 1 + chartArcLength g.extend 0 1 :=
        chartArcLength_pathTrans f g hl hr

private lemma chartIntrinsicDist_eq_zero_of_left {p q : E} (r : E) (f : Path p q)
    (hf : ¬ IntervalIntegrable (fun t => ‖deriv f.extend t‖) MeasureTheory.volume 0 1) :
    chartIntrinsicDist p r = 0 := by
  refine chartIntrinsicDist_eq_zero_of_not_integrable
    (f.trans (straightPath q r)) fun h => hf ?_
  refine (intervalIntegrable_trans_left_iff f (straightPath q r)).mp (h.mono_set ?_)
  exact Set.uIcc_subset_uIcc (by norm_num [Set.mem_uIcc]) (by norm_num [Set.mem_uIcc])

private lemma chartIntrinsicDist_eq_zero_of_right {q r : E} (p : E) (g : Path q r)
    (hg : ¬ IntervalIntegrable (fun t => ‖deriv g.extend t‖) MeasureTheory.volume 0 1) :
    chartIntrinsicDist p r = 0 := by
  refine chartIntrinsicDist_eq_zero_of_not_integrable
    ((straightPath p q).trans g) fun h => hg ?_
  refine (intervalIntegrable_trans_right_iff (straightPath p q) g).mp (h.mono_set ?_)
  exact Set.uIcc_subset_uIcc (by norm_num [Set.mem_uIcc]) (by norm_num [Set.mem_uIcc])

/-- **The chart-local triangle inequality** (S3d — closes the S2–S3 program).

`chartIntrinsicDist p r ≤ chartIntrinsicDist p q + chartIntrinsicDist q r`.

Proof: for admissible factors, glue and use `chartIntrinsicDist_le_add`; if a
factor is inadmissible, its side collapses to `0` — but so does the left side,
because concatenating the inadmissible factor with a straight-line witness
produces an inadmissible `p → r` path (integrability transport, backwards).
The infimum plumbing is elementary `ciInf_le` / `le_ciInf` over the nonempty
path types (witnessed by `straightPath`). -/
theorem chartIntrinsicDist_triangle (p q r : E) :
    chartIntrinsicDist p r ≤ chartIntrinsicDist p q + chartIntrinsicDist q r := by
  have key : ∀ (f : Path p q) (g : Path q r),
      chartIntrinsicDist p r ≤ innerLength f + innerLength g := by
    intro f g
    by_cases hf : IntervalIntegrable (fun t => ‖deriv f.extend t‖) MeasureTheory.volume 0 1
    · by_cases hg : IntervalIntegrable (fun t => ‖deriv g.extend t‖) MeasureTheory.volume 0 1
      · rw [innerLength_of_integrable hf, innerLength_of_integrable hg]
        exact chartIntrinsicDist_le_add f g hf hg
      · rw [chartIntrinsicDist_eq_zero_of_right p g hg]
        exact add_nonneg (innerLength_nonneg f) (innerLength_nonneg g)
    · rw [chartIntrinsicDist_eq_zero_of_left r f hf]
      exact add_nonneg (innerLength_nonneg f) (innerLength_nonneg g)
  haveI : Nonempty (Path p q) := ⟨straightPath p q⟩
  haveI : Nonempty (Path q r) := ⟨straightPath q r⟩
  have h2 : ∀ f : Path p q,
      chartIntrinsicDist p r - innerLength f ≤ chartIntrinsicDist q r := by
    intro f
    rw [chartIntrinsicDist_eq q r]
    exact le_ciInf fun g => by linarith [key f g]
  have h3 : chartIntrinsicDist p r - chartIntrinsicDist q r ≤ chartIntrinsicDist p q := by
    rw [chartIntrinsicDist_eq p q]
    exact le_ciInf fun f => by linarith [h2 f]
  linarith

end TriangleInequalityOQ04OQ01
