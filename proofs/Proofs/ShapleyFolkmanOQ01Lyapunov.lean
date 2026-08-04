/-
  Shapley–Folkman OQ-01 — S3-A: Lyapunov convexity in dimension one
  (Sierpiński's intermediate-value theorem for atomless measures on ℝ).

  Companion file to `proofs/Proofs/ShapleyFolkmanOQ01.lean` (the completed
  negative answer) and `proofs/Proofs/ShapleyFolkman.lean` (parent, verified).

  Context. OQ-01 asked whether the `[FiniteDimensional ℝ E]` hypothesis of
  `shapley_folkman` can be dropped. The answer is NO (machine-verified in
  `ShapleyFolkmanOQ01.lean`): the excess-index bound `Module.finrank ℝ E` is
  attained with equality for every `N` and is unbounded in `ℓ²`. The *correct*
  infinite-dimensional replacement is the Aumann (1965) / Lyapunov (1940)
  circle of ideas: integration over an atomless continuum convexifies EXACTLY
  (zero excess), instead of "up to a dimension-bounded number of exceptional
  summands". Formalizing that positive analog is the S3 programme, previously
  blocked on "Lyapunov's convexity theorem is not in Mathlib".

  This file is the first rung (S3-A): **Lyapunov's convexity theorem in
  dimension one**. For an atomless measure `μ` on ℝ and a measurable set `s`
  of finite measure, the set of values `μ t` over measurable `t ⊆ s` is
  EXACTLY the interval `[0, μ s]` — convex and compact. The engine is
  Sierpiński's (1922) intermediate-value theorem for atomless measures,
  genuinely absent from Mathlib (whose `NoAtoms` is the weak singleton-null
  notion, with an in-file TODO about the strong splitting notion; on ℝ the
  weak notion suffices, because atoms of a Borel-type measure on ℝ would be
  point masses, and `NoAtoms` makes the cumulative function
  `t ↦ μ (s ∩ Iic t)` genuinely continuous).

  Contrast with the parent theorem: with finitely many summands, the
  convexity defect of a Minkowski sum is bounded by `dim E`, and that bound
  is achieved (`tight_excess_count` in `ShapleyFolkmanOQ01.lean`). Over an
  atomless continuum the defect vanishes: the value range is already convex,
  with NO excess. This is the `d = 1` case of Lyapunov's range theorem; the
  `ℝᵈ` case (S3-B) is the next rung.

  Everything in this file is sorry-free and axiom-free.
-/

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Convex.Basic

namespace ShapleyFolkman.Lyapunov

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {μ : Measure ℝ} {s : Set ℝ}

/-- The cumulative function `t ↦ μ (s ∩ Iic t)` of a measure is monotone. -/
lemma monotone_measure_inter_Iic (μ : Measure ℝ) (s : Set ℝ) :
    Monotone fun t => μ (s ∩ Iic t) := fun _ _ hab =>
  measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hab))

/-- **Continuity of the cumulative function of an atomless measure.**

    For `μ` atomless (`NoAtoms`) and `s` measurable of finite measure, the
    monotone function `F t = μ (s ∩ Iic t)` is continuous:

    * right-continuity is continuity from above of `μ` along
      `s ∩ Iic (x + 1/(n+1)) ↓ s ∩ Iic x` (needs finiteness);
    * left-continuity is continuity from below along
      `s ∩ Iic (x - 1/(n+1)) ↑ s ∩ Iio x` together with
      `μ (s ∩ Iio x) = μ (s ∩ Iic x)`, which is exactly atomlessness
      (`Iio_ae_eq_Iic`).

    This is the analytic heart of the one-dimensional Lyapunov theorem. -/
lemma continuous_measure_inter_Iic [NoAtoms μ] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Continuous fun t => μ (s ∩ Iic t) := by
  rw [continuous_iff_continuousAt]
  intro x
  refine tendsto_order.2 ⟨fun c hc => ?_, fun c hc => ?_⟩
  · -- values just below `F x` are exceeded near `x` (left-continuity side)
    have hio : μ (s ∩ Iio x) = μ (s ∩ Iic x) :=
      measure_congr ((ae_eq_refl _).inter Iio_ae_eq_Iic)
    have hU : (⋃ n : ℕ, s ∩ Iic (x - 1 / ((n : ℝ) + 1))) = s ∩ Iio x := by
      rw [← inter_iUnion]
      congr 1
      ext y
      simp only [mem_iUnion, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨n, hn⟩
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hy)
        exact ⟨n, by linarith⟩
    have hmono : Monotone fun n : ℕ => s ∩ Iic (x - 1 / ((n : ℝ) + 1)) := by
      intro n m hnm
      refine inter_subset_inter_right _ (Iic_subset_Iic.2 ?_)
      have h1 : ((n : ℝ) + 1) ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) h1
      linarith
    have htendsto := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU] at htendsto
    have hc' : c < μ (s ∩ Iio x) := by rw [hio]; exact hc
    obtain ⟨n, hn⟩ := (htendsto.eventually_const_lt hc').exists
    filter_upwards [eventually_gt_nhds (show x - 1 / ((n : ℝ) + 1) < x by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)] with y hy
    exact lt_of_lt_of_le hn
      (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hy.le)))
  · -- values just above `F x` dominate near `x` (right-continuity side)
    have hI : (⋂ n : ℕ, s ∩ Iic (x + 1 / ((n : ℝ) + 1))) = s ∩ Iic x := by
      rw [← inter_iInter]
      congr 1
      ext y
      simp only [mem_iInter, mem_Iic]
      constructor
      · intro h
        by_contra hxy
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 (not_le.1 hxy))
        have := h n
        linarith
      · intro h n
        have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hanti : Antitone fun n : ℕ => s ∩ Iic (x + 1 / ((n : ℝ) + 1)) := by
      intro n m hnm
      refine inter_subset_inter_right _ (Iic_subset_Iic.2 ?_)
      have h1 : ((n : ℝ) + 1) ≤ (m : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hnm
      have h2 : 1 / ((m : ℝ) + 1) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) h1
      linarith
    have hfin : ∃ n : ℕ, μ (s ∩ Iic (x + 1 / ((n : ℝ) + 1))) ≠ ∞ :=
      ⟨0, ne_top_of_le_ne_top hμs (measure_mono inter_subset_left)⟩
    have htendsto := tendsto_measure_iInter_atTop (μ := μ)
      (fun _ => (hs.inter measurableSet_Iic).nullMeasurableSet) hanti hfin
    rw [hI] at htendsto
    have hc' : μ (s ∩ Iic x) < c := hc
    obtain ⟨n, hn⟩ := (htendsto.eventually_lt_const hc').exists
    filter_upwards [eventually_lt_nhds (show x < x + 1 / ((n : ℝ) + 1) by
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)] with y hy
    exact lt_of_le_of_lt
      (measure_mono (inter_subset_inter_right _ (Iic_subset_Iic.2 hy.le))) hn

/-- **Sierpiński's intermediate-value theorem for atomless measures on ℝ**
    (1922). If `μ` is atomless, `s` is measurable with `μ s < ∞`, and
    `r ≤ μ s`, then some measurable `t ⊆ s` has `μ t = r` exactly.

    The witness is an initial slice `t = s ∩ Iic x`: the cumulative function
    `F t = μ (s ∩ Iic t)` is continuous (`continuous_measure_inter_Iic`),
    tends to `0` at `-∞` and to `μ s` at `+∞`, so the intermediate value
    theorem on the preconnected space ℝ produces the exact level `r`.

    This statement is absent from Mathlib (which has only
    `exists_subset_measure_lt_top`); it is the `d = 1` Lyapunov theorem. -/
theorem exists_subset_measure_eq [NoAtoms μ] (hs : MeasurableSet s) (hμs : μ s ≠ ∞)
    {r : ℝ≥0∞} (hr : r ≤ μ s) :
    ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ t = r := by
  rcases eq_or_lt_of_le hr with rfl | hr'
  · exact ⟨s, hs, subset_rfl, rfl⟩
  rcases eq_or_ne r 0 with rfl | hr0
  · exact ⟨∅, MeasurableSet.empty, empty_subset _, measure_empty⟩
  -- main case: `0 < r < μ s`
  have hcont := continuous_measure_inter_Iic hs hμs
  have hbot : Tendsto (fun t : ℝ => μ (s ∩ Iic t)) atBot (𝓝 0) := by
    have hInt : (⋂ i : ℝ, s ∩ Iic i) = ∅ := by
      apply eq_empty_iff_forall_notMem.2
      intro y hy
      have h1 := (mem_iInter.1 hy (y - 1)).2
      simp only [mem_Iic] at h1
      linarith
    have h := tendsto_measure_iInter_atBot (μ := μ) (s := fun i : ℝ => s ∩ Iic i)
      (fun _ => (hs.inter measurableSet_Iic).nullMeasurableSet)
      (fun _ _ hab => inter_subset_inter_right _ (Iic_subset_Iic.2 hab))
      ⟨0, ne_top_of_le_ne_top hμs (measure_mono inter_subset_left)⟩
    rwa [hInt, measure_empty] at h
  have htop : Tendsto (fun t : ℝ => μ (s ∩ Iic t)) atTop (𝓝 (μ s)) := by
    have hU : (⋃ i : ℝ, s ∩ Iic i) = s := by
      rw [← inter_iUnion, iUnion_Iic, inter_univ]
    have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun i : ℝ => s ∩ Iic i)
      (fun _ _ hab => inter_subset_inter_right _ (Iic_subset_Iic.2 hab))
    rwa [hU] at h
  have hr0' : (0 : ℝ≥0∞) < r := lt_of_le_of_ne zero_le (Ne.symm hr0)
  have h₁ : ∃ a, μ (s ∩ Iic a) ≤ r := by
    obtain ⟨a, ha⟩ := (hbot.eventually_lt_const hr0').exists
    exact ⟨a, ha.le⟩
  have h₂ : ∃ b, r ≤ μ (s ∩ Iic b) := by
    obtain ⟨b, hb⟩ := (htop.eventually_const_lt hr').exists
    exact ⟨b, hb.le⟩
  obtain ⟨x, hx⟩ := mem_range_of_exists_le_of_exists_ge hcont h₁ h₂
  exact ⟨s ∩ Iic x, hs.inter measurableSet_Iic, inter_subset_left, hx⟩

/-- **The value range of an atomless measure is a full interval** (`ℝ≥0∞`
    form). Over measurable subsets of a finite-measure set `s`, the attained
    measures are exactly `Icc 0 (μ s)` — no gaps. -/
theorem setOf_measure_subset_eq_Icc [NoAtoms μ] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    {r : ℝ≥0∞ | ∃ t, MeasurableSet t ∧ t ⊆ s ∧ μ t = r} = Icc 0 (μ s) := by
  ext r
  simp only [mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨t, _, hts, rfl⟩
    exact ⟨zero_le, measure_mono hts⟩
  · rintro ⟨-, hrs⟩
    exact exists_subset_measure_eq hs hμs hrs

/-- **Lyapunov's convexity theorem in dimension one** (range form, real
    values). The range of the real-valued set function `t ↦ (μ t).toReal`
    over measurable subsets of `s` is the compact convex interval
    `[0, (μ s).toReal]`. This is the `d = 1` case of "the range of an
    atomless vector measure is convex and compact" (Lyapunov 1940). -/
theorem lyapunov_range_eq_Icc [NoAtoms μ] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    {r : ℝ | ∃ t, MeasurableSet t ∧ t ⊆ s ∧ (μ t).toReal = r} = Icc 0 (μ s).toReal := by
  ext r
  simp only [mem_setOf_eq, mem_Icc]
  constructor
  · rintro ⟨t, _, hts, rfl⟩
    exact ⟨ENNReal.toReal_nonneg, ENNReal.toReal_mono hμs (measure_mono hts)⟩
  · rintro ⟨hr0, hrs⟩
    obtain ⟨t, ht, hts, htr⟩ := exists_subset_measure_eq hs hμs
      ((ENNReal.ofReal_le_iff_le_toReal hμs).2 hrs)
    exact ⟨t, ht, hts, by rw [htr, ENNReal.toReal_ofReal hr0]⟩

/-- The dimension-one Lyapunov range is **convex** — the exact-convexification
    phenomenon that replaces the Shapley–Folkman excess bound over an
    atomless continuum (zero excess, versus `Module.finrank ℝ E` excess
    summands in the finite-dimensional discrete case). -/
theorem lyapunov_range_convex [NoAtoms μ] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    Convex ℝ {r : ℝ | ∃ t, MeasurableSet t ∧ t ⊆ s ∧ (μ t).toReal = r} := by
  rw [lyapunov_range_eq_Icc hs hμs]
  exact convex_Icc _ _

/-- The dimension-one Lyapunov range is **compact**. Together with
    `lyapunov_range_convex` this is the full `d = 1` Lyapunov statement:
    the range of an atomless finite measure is convex and compact. -/
theorem lyapunov_range_isCompact [NoAtoms μ] (hs : MeasurableSet s) (hμs : μ s ≠ ∞) :
    IsCompact {r : ℝ | ∃ t, MeasurableSet t ∧ t ⊆ s ∧ (μ t).toReal = r} := by
  rw [lyapunov_range_eq_Icc hs hμs]
  exact isCompact_Icc

/-- **Non-vacuity witness**: Lebesgue measure on `[0, 1]` is atomless of
    finite measure, so every level `r ≤ 1` is attained exactly by a
    measurable subset of the unit interval. The hypotheses of the theorems
    above are satisfiable — this rung carries real content. -/
theorem exists_subset_unitInterval_volume_eq {r : ℝ≥0∞} (hr : r ≤ 1) :
    ∃ t, MeasurableSet t ∧ t ⊆ Icc (0 : ℝ) 1 ∧ volume t = r := by
  have h1 : volume (Icc (0 : ℝ) 1) = 1 := by
    rw [Real.volume_Icc]
    norm_num
  exact exists_subset_measure_eq measurableSet_Icc
    (by rw [h1]; exact ENNReal.one_ne_top) (by rw [h1]; exact hr)

end ShapleyFolkman.Lyapunov
