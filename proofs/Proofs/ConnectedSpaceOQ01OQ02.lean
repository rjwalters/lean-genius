import Mathlib

/-!
# The topologist's sine curve is connected

The parent entry `ConnectedSpaceOQ01.lean` proves that connectedness is stable under
closure — and, sharper, that *any* set wedged between a connected set and its closure is
connected (`connected_of_subset_closure`: if `s` is connected and `s ⊆ t ⊆ closure s`,
then `t` is connected). Its open question asks to **use that "bark and tree" corollary on a
concrete space built from a dense connected skeleton.**

This entry supplies the canonical example: the **topologist's sine curve**

`T = { (x, sin x⁻¹) : x > 0 } ∪ ( {0} × [−1, 1] )`,

the textbook witness of a space that is connected but not path-connected. We formalize the
connectedness half — exactly the consequence the parent's corollary delivers.

## Strategy

* `sineCurve = (fun x => (x, sin x⁻¹)) '' Ioi 0` is the graph over the positive reals. It is
  the continuous image of the connected set `Ioi 0`, hence **connected**
  (`isConnected_sineCurve`).
* The limit segment `{0} × [−1, 1]` lies in the **closure** of the graph
  (`limitSegment_subset_closure`): given `y ∈ [−1, 1]`, the points
  `(aₙ⁻¹, sin aₙ)` with `aₙ = arcsin y + n·2π` satisfy `sin aₙ = y` (periodicity +
  `sin (arcsin y) = y`) and `aₙ⁻¹ → 0`, so `(0, y)` is a limit of graph points.
* Therefore `sineCurve ⊆ T ⊆ closure sineCurve`, and the parent's "bark and tree" corollary
  (here `IsConnected.subset_closure`) gives `IsConnected T` (`isConnected_topologistSineCurve`).

Path-connectedness *fails* for `T` (no path joins the segment to the oscillating graph); that
is recorded as a follow-up question, not formalized here.

No axioms, no `native_decide`, no sorries.
-/

namespace ConnectedSpaceOQ01OQ02

open Set Topology Real

/-- The graph of `x ↦ sin x⁻¹` over the positive reals — the oscillating part of the curve. -/
def sineCurve : Set (ℝ × ℝ) := (fun x : ℝ => (x, Real.sin x⁻¹)) '' Set.Ioi 0

/-- The limit segment `{0} × [−1, 1]` that the graph accumulates onto. -/
def limitSegment : Set (ℝ × ℝ) := {0} ×ˢ Set.Icc (-1) 1

/-- The **topologist's sine curve**: the graph together with its limit segment. -/
def topologistSineCurve : Set (ℝ × ℝ) := sineCurve ∪ limitSegment

/-- The parametrization `x ↦ (x, sin x⁻¹)` is continuous on `Ioi 0` (away from the
singularity of `x⁻¹` at `0`). -/
theorem continuousOn_param :
    ContinuousOn (fun x : ℝ => (x, Real.sin x⁻¹)) (Set.Ioi 0) := by
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Ioi 0) :=
    continuousOn_id.inv₀ (fun x hx => ne_of_gt (Set.mem_Ioi.mp hx))
  exact continuousOn_id.prodMk (Real.continuous_sin.comp_continuousOn hinv)

/-- **The graph is connected**, being the continuous image of the connected set `Ioi 0`. -/
theorem isConnected_sineCurve : IsConnected sineCurve :=
  isConnected_Ioi.image _ continuousOn_param

/-- **The limit segment lies in the closure of the graph.** For `(0, y)` with `y ∈ [−1, 1]`,
the graph points `(aₙ⁻¹, sin aₙ)` with `aₙ = arcsin y + n·2π` have second coordinate `y`
(periodicity of `sin` plus `sin (arcsin y) = y`) and first coordinate `aₙ⁻¹ → 0`. -/
theorem limitSegment_subset_closure : limitSegment ⊆ closure sineCurve := by
  rintro p hp
  obtain ⟨hp1, hp2⟩ := hp
  rw [Set.mem_singleton_iff] at hp1
  obtain ⟨hy1, hy2⟩ := hp2
  rw [Metric.mem_closure_iff]
  intro ε hε
  set θ := Real.arcsin p.2 with hθ
  have hθlb : -(π / 2) ≤ θ := (Real.arcsin_mem_Icc p.2).1
  have hpi : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((ε⁻¹ + π / 2 + 1) / (2 * π))
  rw [div_lt_iff₀ hpi] at hn
  set a := θ + (n : ℝ) * (2 * π) with ha_def
  have ha_big : ε⁻¹ < a := by rw [ha_def]; linarith [hθlb, hn]
  have ha_pos : 0 < a := lt_trans (inv_pos.mpr hε) ha_big
  have hx_pos : 0 < a⁻¹ := inv_pos.mpr ha_pos
  refine ⟨(a⁻¹, Real.sin (a⁻¹)⁻¹), ⟨a⁻¹, Set.mem_Ioi.mpr hx_pos, rfl⟩, ?_⟩
  have hsin : Real.sin (a⁻¹)⁻¹ = p.2 := by
    rw [inv_inv, ha_def, Real.sin_add_nat_mul_two_pi, hθ, Real.sin_arcsin hy1 hy2]
  rw [hsin, Prod.dist_eq]
  have h1 : dist p.1 a⁻¹ = a⁻¹ := by
    rw [hp1, Real.dist_eq, zero_sub, abs_neg, abs_of_pos hx_pos]
  rw [h1, dist_self, max_eq_left (le_of_lt hx_pos)]
  exact (inv_lt_comm₀ ha_pos hε).mpr ha_big

/-- **The topologist's sine curve is connected.** It is sandwiched between the connected
graph and the graph's closure, so the parent's "bark and tree" corollary applies. -/
theorem isConnected_topologistSineCurve : IsConnected topologistSineCurve := by
  have hsub : topologistSineCurve ⊆ closure sineCurve := by
    unfold topologistSineCurve
    rw [union_subset_iff]
    exact ⟨subset_closure, limitSegment_subset_closure⟩
  have hsk : sineCurve ⊆ topologistSineCurve := Set.subset_union_left
  exact isConnected_sineCurve.subset_closure hsk hsub

/-- The topologist's sine curve is in particular **preconnected**. -/
theorem isPreconnected_topologistSineCurve : IsPreconnected topologistSineCurve :=
  isConnected_topologistSineCurve.isPreconnected

end ConnectedSpaceOQ01OQ02
