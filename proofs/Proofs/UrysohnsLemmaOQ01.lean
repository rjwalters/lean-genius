import Mathlib

/-!
# Urysohn's lemma and the explicit metric Urysohn function

**Urysohn's lemma** (Urysohn 1925) is the cornerstone separation theorem of point-set
topology: in a normal space any two disjoint closed sets are *functionally separated* by a
continuous real-valued function. Mathlib proves the abstract statement

* `exists_continuous_zero_one_of_isClosed` — in a `NormalSpace`, disjoint closed sets `s`,
  `t` admit a continuous `f : C(X, ℝ)` with `f = 0` on `s`, `f = 1` on `t`, `0 ≤ f ≤ 1`,

and the locally-compact-Hausdorff variant `exists_continuous_zero_one_of_isCompact`. This
file re-exports those headline results (hence the `mathlib` badge) and then supplies the
genuine content absent from Mathlib: the **explicit Urysohn function on a metric space**.

For disjoint nonempty closed sets `s`, `t` in a metric space the textbook witness is
$$ f(x) \;=\; \frac{d(x,s)}{d(x,s) + d(x,t)}, $$
built from the distance-to-a-set function `Metric.infDist`. We construct it as
`urysohnFn s t` and prove, with no appeal to the abstract Urysohn machinery, that it is

* continuous (`continuous_urysohnFn`), the denominator never vanishing
  (`infDist_add_pos`);
* identically `0` on `s` (`urysohnFn_eq_zero`) and `1` on `t` (`urysohnFn_eq_one`);
* valued in `[0, 1]` (`urysohnFn_mem_Icc`),

then package it as the bundled separator `urysohn_metric`. We also record that the abstract
lemma applies verbatim in a metric space (every metric space is normal,
`urysohn_metric_of_normalSpace`), the consequence that a point can be separated from a
disjoint closed set in a normal `T1` space (`urysohn_point_isClosed`), and a concrete
evaluation of the explicit function (`urysohnFn_half_at_midpoint`).

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

namespace UrysohnsLemmaOQ01

open Set Metric

/-! ## Part (a): the abstract lemma in a normal space

These are direct re-exports of Mathlib's Urysohn lemma; they carry the `mathlib` badge.
-/

section Abstract

variable {X : Type*} [TopologicalSpace X]

/-- **Urysohn's lemma.** In a normal space, two disjoint closed sets `s`, `t` are separated
by a continuous function `f : X → ℝ` with `f = 0` on `s`, `f = 1` on `t`, and `0 ≤ f ≤ 1`. -/
theorem urysohn_normal [NormalSpace X] {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  exists_continuous_zero_one_of_isClosed hs ht hd

/-- **Urysohn's lemma, locally compact Hausdorff form.** In a regular locally compact space,
a compact set `s` and a disjoint closed set `t` are separated by a continuous `f : X → ℝ`
with `f = 0` on `s`, `f = 1` on `t`, `0 ≤ f ≤ 1`. This is the version behind the Riesz
representation theorem and partitions of unity. -/
theorem urysohn_locallyCompact [RegularSpace X] [LocallyCompactSpace X] {s t : Set X}
    (hs : IsCompact s) (ht : IsClosed t) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  exists_continuous_zero_one_of_isCompact hs ht hd

/-- **Functional separation of a point from a closed set.** In a normal `T1` space a point
`x₀` outside a closed set `t` is separated from it by a continuous `f` with `f x₀ = 0`,
`f = 1` on `t`, `0 ≤ f ≤ 1`. This is the gateway to complete regularity. -/
theorem urysohn_point_isClosed [T1Space X] [NormalSpace X] {t : Set X} {x₀ : X}
    (ht : IsClosed t) (hx₀ : x₀ ∉ t) :
    ∃ f : C(X, ℝ), f x₀ = 0 ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨f, hfs, hft, hficc⟩ :=
    urysohn_normal (isClosed_singleton (x := x₀)) ht (disjoint_singleton_left.mpr hx₀)
  exact ⟨f, by simpa using hfs (show x₀ ∈ ({x₀} : Set X) from rfl), hft, hficc⟩

end Abstract

/-! ## Part (b): the explicit Urysohn function on a metric space

The construction `f(x) = d(x,s) / (d(x,s) + d(x,t))` separates disjoint nonempty closed
sets, built entirely from the `Metric.infDist` API and independent of the abstract Urysohn
machinery. This explicit function is not a named result in Mathlib.
-/

section Metric

variable {X : Type*} [MetricSpace X]

/-- The explicit Urysohn function separating two sets in a metric space:
`x ↦ d(x, s) / (d(x, s) + d(x, t))`. -/
noncomputable def urysohnFn (s t : Set X) (x : X) : ℝ :=
  infDist x s / (infDist x s + infDist x t)

/-- For disjoint nonempty closed sets, the denominator `d(x,s) + d(x,t)` is strictly
positive everywhere: a point with both distances zero would lie in `s ∩ t`. -/
theorem infDist_add_pos {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hsne : s.Nonempty) (htne : t.Nonempty) (hd : Disjoint s t) (x : X) :
    0 < infDist x s + infDist x t := by
  rcases (infDist_nonneg : (0 : ℝ) ≤ infDist x s).eq_or_lt with hxs | hpos
  · -- `infDist x s = 0`, so `x ∈ s`, hence `x ∉ t`, hence `infDist x t > 0`.
    have hmem : x ∈ s := (hs.mem_iff_infDist_zero hsne).2 hxs.symm
    have hnt : x ∉ t := Set.disjoint_left.1 hd hmem
    have htpos : 0 < infDist x t := (ht.notMem_iff_infDist_pos htne).1 hnt
    rw [← hxs, zero_add]; exact htpos
  · exact add_pos_of_pos_of_nonneg hpos infDist_nonneg

/-- The explicit Urysohn function is continuous: a quotient of the continuous
distance-to-a-set functions with a nowhere-vanishing denominator. -/
theorem continuous_urysohnFn {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hsne : s.Nonempty) (htne : t.Nonempty) (hd : Disjoint s t) :
    Continuous (urysohnFn s t) := by
  unfold urysohnFn
  exact (continuous_infDist_pt s).div
    ((continuous_infDist_pt s).add (continuous_infDist_pt t))
    (fun x => (infDist_add_pos hs ht hsne htne hd x).ne')

/-- The explicit Urysohn function vanishes on `s` (its distance to `s` is zero there). -/
theorem urysohnFn_eq_zero {s t : Set X} {x : X} (hx : x ∈ s) : urysohnFn s t x = 0 := by
  unfold urysohnFn
  rw [infDist_zero_of_mem hx, zero_div]

/-- The explicit Urysohn function equals `1` on `t`: its distance to `t` is zero there, and
(by disjointness with the closed nonempty `s`) its distance to `s` is positive. -/
theorem urysohnFn_eq_one {s t : Set X} (hs : IsClosed s) (hsne : s.Nonempty)
    (hd : Disjoint s t) {x : X} (hx : x ∈ t) : urysohnFn s t x = 1 := by
  have hxs : x ∉ s := Set.disjoint_right.1 hd hx
  have hpos : 0 < infDist x s := (hs.notMem_iff_infDist_pos hsne).1 hxs
  unfold urysohnFn
  rw [infDist_zero_of_mem hx, add_zero, div_self hpos.ne']

/-- The explicit Urysohn function is valued in `[0, 1]`. -/
theorem urysohnFn_mem_Icc {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hsne : s.Nonempty) (htne : t.Nonempty) (hd : Disjoint s t) (x : X) :
    urysohnFn s t x ∈ Icc (0 : ℝ) 1 := by
  have hpos := infDist_add_pos hs ht hsne htne hd x
  unfold urysohnFn
  refine ⟨div_nonneg infDist_nonneg hpos.le, ?_⟩
  rw [div_le_one hpos]
  exact le_add_of_nonneg_right infDist_nonneg

/-- **Metric Urysohn lemma (explicit witness).** Disjoint nonempty closed sets in a metric
space are separated by the explicit function `urysohnFn s t`, packaged as a bundled
continuous map. -/
theorem urysohn_metric {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hsne : s.Nonempty) (htne : t.Nonempty) (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨⟨urysohnFn s t, continuous_urysohnFn hs ht hsne htne hd⟩, ?_, ?_, ?_⟩
  · intro x hx; simpa using urysohnFn_eq_zero (t := t) hx
  · intro x hx; simpa using urysohnFn_eq_one hs hsne hd hx
  · intro x; simpa using urysohnFn_mem_Icc hs ht hsne htne hd x

/-- Every metric space is normal, so the abstract Urysohn lemma applies to it verbatim
(no nonemptiness hypotheses needed). -/
theorem urysohn_metric_of_normalSpace {s t : Set X} (hs : IsClosed s) (ht : IsClosed t)
    (hd : Disjoint s t) :
    ∃ f : C(X, ℝ), EqOn f 0 s ∧ EqOn f 1 t ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 :=
  exists_continuous_zero_one_of_isClosed hs ht hd

end Metric

/-! ## Part (c): a concrete evaluation -/

/-- On `ℝ`, the explicit Urysohn function separating `{0}` and `{1}` takes the value `1/2`
at the midpoint `1/2`, as it must by symmetry. -/
theorem urysohnFn_half_at_midpoint :
    urysohnFn ({0} : Set ℝ) {1} (1 / 2) = 1 / 2 := by
  unfold urysohnFn
  rw [infDist_singleton, infDist_singleton, Real.dist_eq, Real.dist_eq]
  norm_num

end UrysohnsLemmaOQ01
