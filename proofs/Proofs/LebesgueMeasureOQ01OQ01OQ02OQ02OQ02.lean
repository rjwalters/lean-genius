/-
# The Dirichlet Function is Nowhere Continuous — the Baire-Category Antipode of Thomae

## Open Question (lebesgue-measure-oq-01-oq-01-oq-02-oq-02-oq-02)

The Dirichlet function `D = 𝟙_ℚ : ℝ → ℝ` takes the value `1` on the rationals and
`0` on the irrationals.  The parent entry `LebesgueMeasureOQ01OQ01OQ02OQ02` proves
that *Thomae's* (popcorn) function is continuous exactly on the irrationals — a dense
`Gδ`, comeagre set — and discontinuous only on the meagre set `ℚ`.  Thomae is "mostly
continuous".

This entry formalizes the **exact opposite**: the Dirichlet function is continuous at
**no** point of `ℝ`.  Because both `ℚ` and `ℝ \ ℚ` are dense, every neighbourhood of
every real number contains a point where `D = 1` and a point where `D = 0`, so `D`
jumps by a full unit everywhere and cannot be continuous anywhere.

We prove the three-part dichotomy:

  1. `dirichlet_not_continuousAt`            : `¬ ContinuousAt D x` for every `x`;
  2. `dirichlet_continuitySet_eq_empty` /
     `dirichlet_discontinuitySet_eq_univ`    : continuity set `= ∅`, discontinuity set `= ℝ`;
  3. `dirichlet_oscillation_eq_one`          : the oscillation `ω_D(x) = 1` at every `x`
     (sharp quantitative form, contrasting Thomae's pointwise oscillation `1/q`).

and the **Baire-category antipode** framing: the continuity set of Thomae is a dense
`Gδ` (comeagre), whereas Dirichlet's continuity set `∅` is *not dense*
(`dirichlet_continuitySet_not_dense`) — so the two functions realize opposite ends of
the continuity-set theory.

The key uniform device is that *every* point admits both a rational sequence (where
`D = 1`) and an irrational sequence (where `D = 0`) converging to it; continuity would
force `D x = 1` and `D x = 0` simultaneously.

Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Set Filter Topology Metric
open scoped ENNReal

namespace LebesgueMeasureOQ01OQ01OQ02OQ02OQ02

/-- The **Dirichlet function** `𝟙_ℚ`: `1` on the rationals, `0` on the irrationals. -/
noncomputable def dirichlet : ℝ → ℝ := Set.indicator (Set.range ((↑) : ℚ → ℝ)) 1

/-- `D` is `1` at every rational. -/
theorem dirichlet_rat (q : ℚ) : dirichlet (q : ℝ) = 1 := by
  rw [dirichlet, Set.indicator_of_mem (Set.mem_range_self q)]; rfl

/-- `D` is `0` at every irrational. -/
theorem dirichlet_irrational {x : ℝ} (h : Irrational x) : dirichlet x = 0 := by
  rw [dirichlet, Set.indicator_of_notMem h]

/-- `D` takes only the values `0` and `1`. -/
theorem dirichlet_zero_or_one (x : ℝ) : dirichlet x = 0 ∨ dirichlet x = 1 := by
  by_cases hx : x ∈ Set.range ((↑) : ℚ → ℝ)
  · exact Or.inr (by rw [dirichlet, Set.indicator_of_mem hx]; rfl)
  · exact Or.inl (by rw [dirichlet, Set.indicator_of_notMem hx])

/-! ## Sequential approach to every point through rationals and irrationals -/

/-- Every real is the limit of a sequence of rationals (along which `D = 1`). -/
theorem exists_rat_seq_tendsto (x : ℝ) :
    ∃ u : ℕ → ℝ, (∀ n, u n ∈ Set.range ((↑) : ℚ → ℝ)) ∧ Tendsto u atTop (𝓝 x) :=
  mem_closure_iff_seq_limit.mp (Rat.denseRange_cast x)

/-- Every real is the limit of a sequence of irrationals (along which `D = 0`). -/
theorem exists_irrational_seq_tendsto (x : ℝ) :
    ∃ u : ℕ → ℝ, (∀ n, Irrational (u n)) ∧ Tendsto u atTop (𝓝 x) :=
  mem_closure_iff_seq_limit.mp (dense_irrational x)

/-! ## The Dirichlet function is nowhere continuous -/

/-- **The Dirichlet function is continuous at no point of `ℝ`.** Approaching `x` through
rationals forces the limit to be `1`; approaching through irrationals forces it to be
`0`; uniqueness of limits then gives `1 = 0`. -/
theorem dirichlet_not_continuousAt (x : ℝ) : ¬ ContinuousAt dirichlet x := by
  intro h
  obtain ⟨u, hu, hlim⟩ := exists_rat_seq_tendsto x
  obtain ⟨v, hv, vlim⟩ := exists_irrational_seq_tendsto x
  -- Along rationals `D = 1`, so `D x = 1`.
  have h1 : Tendsto (fun n => dirichlet (u n)) atTop (𝓝 (dirichlet x)) := h.tendsto.comp hlim
  have h1c : (fun n => dirichlet (u n)) = fun _ => (1 : ℝ) := by
    funext n; obtain ⟨q, hq⟩ := hu n; rw [← hq]; exact dirichlet_rat q
  rw [h1c] at h1
  have hx1 : (1 : ℝ) = dirichlet x := tendsto_nhds_unique tendsto_const_nhds h1
  -- Along irrationals `D = 0`, so `D x = 0`.
  have h0 : Tendsto (fun n => dirichlet (v n)) atTop (𝓝 (dirichlet x)) := h.tendsto.comp vlim
  have h0c : (fun n => dirichlet (v n)) = fun _ => (0 : ℝ) :=
    funext fun n => dirichlet_irrational (hv n)
  rw [h0c] at h0
  have hx0 : (0 : ℝ) = dirichlet x := tendsto_nhds_unique tendsto_const_nhds h0
  exact one_ne_zero (hx1.trans hx0.symm)

/-- **The continuity set of the Dirichlet function is empty.** -/
theorem dirichlet_continuitySet_eq_empty :
    {x : ℝ | ContinuousAt dirichlet x} = (∅ : Set ℝ) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  exact dirichlet_not_continuousAt x

/-- **The discontinuity set of the Dirichlet function is all of `ℝ`.** -/
theorem dirichlet_discontinuitySet_eq_univ :
    {x : ℝ | ¬ ContinuousAt dirichlet x} = (Set.univ : Set ℝ) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact dirichlet_not_continuousAt x

/-! ## The oscillation is identically one -/

/-- A neighbourhood of `x` contains a rational, where `D = 1`. -/
theorem exists_rat_mem_of_nhds {x : ℝ} {N : Set ℝ} (hN : N ∈ 𝓝 x) :
    ∃ y ∈ N, dirichlet y = 1 := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨q, hq⟩ := exists_rat_near x hδ
  refine ⟨(q : ℝ), hsub ?_, dirichlet_rat q⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
  exact hq

/-- A neighbourhood of `x` contains an irrational, where `D = 0`. -/
theorem exists_irrational_mem_of_nhds {x : ℝ} {N : Set ℝ} (hN : N ∈ 𝓝 x) :
    ∃ y ∈ N, dirichlet y = 0 := by
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp hN
  obtain ⟨r, hr, hxr, hrδ⟩ := exists_irrational_btwn (show x < x + δ by linarith)
  refine ⟨r, hsub ?_, dirichlet_irrational hr⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]
  linarith

/-- `edist (1 : ℝ) 0 = 1`. -/
private theorem edist_one_zero : edist (1 : ℝ) (0 : ℝ) = 1 := by
  rw [edist_dist, Real.dist_eq]; norm_num

/-- **The oscillation of the Dirichlet function equals `1` at every point.** This is the
sharp quantitative form of nowhere-continuity: the function fluctuates by a full unit in
every neighbourhood of every point.  Contrast Thomae, whose oscillation is `1/q` at the
rational `p/q` and `0` at every irrational. -/
theorem dirichlet_oscillation_eq_one (x : ℝ) : oscillation dirichlet x = 1 := by
  refine le_antisymm ?_ ?_
  · -- `≤ 1`: the image filter contains `range D ⊆ {0,1}`, of diameter `≤ 1`.
    have hmem : Set.range dirichlet ∈ (𝓝 x).map dirichlet := by
      rw [Filter.mem_map, Set.preimage_range]; exact Filter.univ_mem
    refine (biInf_le EMetric.diam hmem).trans ?_
    refine EMetric.diam_le ?_
    rintro a ⟨s, rfl⟩ b ⟨t, rfl⟩
    rw [edist_dist, Real.dist_eq]
    have hab : |dirichlet s - dirichlet t| ≤ 1 := by
      rcases dirichlet_zero_or_one s with hs | hs <;>
        rcases dirichlet_zero_or_one t with ht | ht <;>
        rw [hs, ht] <;> norm_num
    calc ENNReal.ofReal |dirichlet s - dirichlet t| ≤ ENNReal.ofReal 1 :=
          ENNReal.ofReal_le_ofReal hab
      _ = 1 := by simp
  · -- `≥ 1`: every set in the image filter contains both `0` and `1`, so has diameter `≥ 1`.
    refine le_iInf₂ fun S hS => ?_
    rw [Filter.mem_map] at hS
    obtain ⟨y, hy, hy1⟩ := exists_rat_mem_of_nhds hS
    obtain ⟨z, hz, hz0⟩ := exists_irrational_mem_of_nhds hS
    have h1S : (1 : ℝ) ∈ S := hy1 ▸ hy
    have h0S : (0 : ℝ) ∈ S := hz0 ▸ hz
    calc (1 : ℝ≥0∞) = edist (1 : ℝ) 0 := edist_one_zero.symm
      _ ≤ EMetric.diam S := EMetric.edist_le_diam_of_mem h1S h0S

/-! ## The Baire-category antipode of Thomae -/

/-- **The Dirichlet continuity set is not dense.** Whereas Thomae's continuity set is a
*dense* `Gδ` (the irrationals), Dirichlet's continuity set is empty, hence not dense in
`ℝ`.  This is the Baire-category antipode: Thomae realizes the irrationals as a continuity
set, Dirichlet realizes `∅`. -/
theorem dirichlet_continuitySet_not_dense :
    ¬ Dense {x : ℝ | ContinuousAt dirichlet x} := by
  rw [dirichlet_continuitySet_eq_empty]
  simp [dense_iff_inter_open]
  exact ⟨Set.univ, isOpen_univ, ⟨0, Set.mem_univ 0⟩⟩

/-- **The discontinuity set of Dirichlet is comeagre (residual)** — indeed all of `ℝ`.
The sharp opposite of Thomae, whose discontinuity set `ℚ` is meagre. -/
theorem dirichlet_discontinuitySet_residual :
    {x : ℝ | ¬ ContinuousAt dirichlet x} ∈ residual ℝ := by
  rw [dirichlet_discontinuitySet_eq_univ]
  exact Filter.univ_mem

end LebesgueMeasureOQ01OQ01OQ02OQ02OQ02
