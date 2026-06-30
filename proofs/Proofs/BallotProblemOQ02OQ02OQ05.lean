/-
# First Passage as a Stopping Time: Measurability of the Hitting Event (OQ-02-OQ-02-OQ-05)

## Research Question

The sibling `BallotProblemOQ02OQ02.lean` proves the pointwise characterization
`{ω | firstPassageTime bm a ω ≤ T} = maxEvent bm a T` (under nonemptiness), where

  `maxEvent bm a T = {ω | ∃ s ∈ [0,T], a ≤ W s ω}`

is the event "the path reaches level `a` by time `T`". For `firstPassageTime` to be a
genuine **stopping time** with respect to a filtration `ℱ` carrying the information of the
process, the hitting event must be *observable by time `T`*: it must lie in `ℱ T`.

This file proves exactly that.

## What is new

Mathlib's hitting-time API (`MeasureTheory.hittingBtwn`, `hittingBtwn_isStoppingTime`) is
restricted to **discrete / well-founded** index types (`[WellFoundedLT ι]`): it does not apply
to the continuous time line `ι = ℝ` of Brownian motion, where the Début theorem is needed.
Nothing in Mathlib records the continuous-time fact that, for a process with continuous paths
and time-slices adapted to a filtration, the first-passage event is `ℱ T`-measurable.

The crux is a **continuity ⟹ countability** reduction. The defining event ranges over the
*uncountable* index set `[0,T]`; we replace it by a countable rational grid:

  `maxEvent bm a T = ⋂ₖ ⋃_{q ∈ ℚ ∩ [0,T]} {ω | a − 1/(k+1) < W q ω}`   (`maxEvent_eq_iInter_approxEvent`)

Each set on the right is a preimage of an open ray under a single time-slice `W q`, hence
`ℱ T`-measurable by adaptedness (`ℱ q ≤ ℱ T` for `q ≤ T`); a countable intersection of
countable unions of such sets is `ℱ T`-measurable.

## Method

* `⊆` uses continuity of `t ↦ W t ω` and density of `ℚ ∩ [0,T]` in `[0,T]` (built here,
  handling both endpoints via `exists_rat_btwn`): a witness `s₀` with `W s₀ ω ≥ a` is
  approximated to within any tolerance `1/(k+1)` by a rational time `q`.
* `⊇` uses sequential compactness of `[0,T]` (`IsCompact.tendsto_subseq`): rational witnesses
  `q_k` with `W q_k ω > a − 1/(k+1)` accumulate at some `s* ∈ [0,T]`, and continuity forces
  `W s* ω ≥ a` in the limit (`le_of_tendsto_of_tendsto'`).

From the identity, `measurableSet_maxEvent` reads off `ℱ T`-measurability under adaptedness,
and `firstPassage_measurableSet` transports it to the first-passage event `{ω | τ ≤ T}` via the
sibling's characterization (under the standing nonemptiness hypothesis that makes `τ ≤ T`
genuinely equivalent to hitting — recall `sInf ∅ = 0` makes the raw inequality degenerate).

## References

* Mathlib: `Mathlib/Probability/Process/HittingTime.lean` (discrete-time hitting times),
  `Mathlib/Probability/Process/Filtration.lean`, `Mathlib/Topology/Sequences.lean`.
* Sibling: `Proofs/BallotProblemOQ02OQ02.lean` (`fpt_le_set_eq_maxEvent`).
* I. Karatzas, S. Shreve, *Brownian Motion and Stochastic Calculus*, §1.2 (first passage
  times as stopping times for continuous adapted processes).
-/
import Mathlib
import Proofs.BallotProblemOQ02OQ02

namespace BallotProblemOQ02OQ02OQ05

open Set MeasureTheory Filter Topology
open BallotFPT

variable {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-! ## The countable rational approximation of the hitting event -/

/-- The `k`-th rational approximation of the hitting event: there is a rational time
`q ∈ [0,T]` at which the path exceeds `a − 1/(k+1)`. As `k → ∞` these shrink down to the
exact hitting event. The union ranges over the countable set `ℚ`, so this set is built from
countably many time-slices. -/
def approxEvent (bm : BrownianMotion Ω μ) (a T : ℝ) (k : ℕ) : Set Ω :=
  ⋃ (q : ℚ) (_ : (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ T), {ω | a - 1 / (k + 1) < bm.W (q : ℝ) ω}

/-- **Density of the rational grid in `[0,T]`.** For `s₀ ∈ [0,T]` and any tolerance `ε > 0`,
there is a rational `q ∈ [0,T]` with `|q − s₀| < ε`. Endpoints are handled by approximating
from inside the interval. -/
theorem exists_rat_near_in_Icc {T s₀ ε : ℝ} (hT : 0 ≤ T) (hs₀ : s₀ ∈ Icc 0 T) (hε : 0 < ε) :
    ∃ q : ℚ, (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ T ∧ |(q : ℝ) - s₀| < ε := by
  obtain ⟨hs0, hsT⟩ := hs₀
  rcases eq_or_lt_of_le hT with hT0 | hTpos
  · -- T = 0, so s₀ = 0; take q = 0
    refine ⟨0, by norm_num, ?_, ?_⟩
    · rw [← hT0]; norm_num
    · have hs00 : s₀ = 0 := le_antisymm (by rw [← hT0] at hsT; exact hsT) hs0
      rw [hs00]; simpa using hε
  · -- T > 0: the open interval (max 0 (s₀-ε), min T (s₀+ε)) is nonempty; pick a rational in it
    set L : ℝ := max 0 (s₀ - ε) with hL
    set U : ℝ := min T (s₀ + ε) with hU
    have hLU : L < U := by
      rw [hL, hU, max_lt_iff, lt_min_iff, lt_min_iff]
      refine ⟨⟨hTpos, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    obtain ⟨q, hqL, hqU⟩ := exists_rat_btwn hLU
    have hq0 : (0 : ℝ) ≤ (q : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hqL)
    have hqT : (q : ℝ) ≤ T := le_of_lt (lt_of_lt_of_le hqU (min_le_left _ _))
    refine ⟨q, hq0, hqT, ?_⟩
    have h1 : s₀ - ε < (q : ℝ) := lt_of_le_of_lt (le_max_right _ _) hqL
    have h2 : (q : ℝ) < s₀ + ε := lt_of_lt_of_le hqU (min_le_right _ _)
    rw [abs_sub_lt_iff]
    constructor <;> linarith

/-- **The hitting event is the countable intersection of its rational approximations.** This is
the analytic heart of the file: continuity of the paths lets the uncountable existential over
`[0,T]` be tested on the countable rational grid. -/
theorem maxEvent_eq_iInter_approxEvent (bm : BrownianMotion Ω μ) (a T : ℝ) (hT : 0 ≤ T) :
    maxEvent bm a T = ⋂ k : ℕ, approxEvent bm a T k := by
  ext ω
  simp only [maxEvent, approxEvent, mem_setOf_eq, mem_iInter, mem_iUnion, exists_prop]
  constructor
  · -- forward: hit at s₀ ⟹ for each k a nearby rational exceeds a - 1/(k+1)
    rintro ⟨s₀, hs₀_Icc, hs₀_ge⟩ k
    have hcont : Continuous (fun t => bm.W t ω) := bm.path_continuous ω
    have hk : (0 : ℝ) < 1 / (k + 1) := by positivity
    -- by continuity, a δ-ball around s₀ keeps W within 1/(k+1) of W s₀ ω
    have := Metric.continuous_iff.mp hcont s₀ (1 / (k + 1)) hk
    obtain ⟨δ, hδ, hball⟩ := this
    obtain ⟨q, hq0, hqT, hqδ⟩ := exists_rat_near_in_Icc hT hs₀_Icc hδ
    refine ⟨q, ⟨hq0, hqT⟩, ?_⟩
    have hdist : dist (bm.W (q : ℝ) ω) (bm.W s₀ ω) < 1 / (k + 1) := by
      have : dist (q : ℝ) s₀ < δ := by rwa [Real.dist_eq]
      exact hball _ this
    rw [Real.dist_eq] at hdist
    have : bm.W s₀ ω - bm.W (q : ℝ) ω < 1 / (k + 1) :=
      lt_of_le_of_lt (le_abs_self _) (by rwa [abs_sub_comm] at hdist)
    linarith
  · -- backward: rational witnesses q_k accumulate at s*, continuity gives W s* ω ≥ a
    intro h
    choose q hq hWq using h
    -- the real points x k = q k ∈ [0,T] (compact)
    set x : ℕ → ℝ := fun k => (q k : ℝ) with hx
    have hx_mem : ∀ k, x k ∈ Icc 0 T := fun k => ⟨(hq k).1, (hq k).2⟩
    obtain ⟨s, hs_mem, φ, hφ_mono, hφ_tend⟩ :=
      (isCompact_Icc (a := (0 : ℝ)) (b := T)).tendsto_subseq hx_mem
    refine ⟨s, hs_mem, ?_⟩
    have hcont : Continuous (fun t => bm.W t ω) := bm.path_continuous ω
    -- W (x (φ j)) ω → W s ω
    have hWtend : Tendsto (fun j => bm.W (x (φ j)) ω) atTop (𝓝 (bm.W s ω)) :=
      ((hcont.tendsto s).comp hφ_tend)
    -- a - 1/(φ j + 1) → a
    have hφ_atTop : Tendsto φ atTop atTop := hφ_mono.tendsto_atTop
    have hlow : Tendsto (fun j => a - 1 / ((φ j : ℝ) + 1)) atTop (𝓝 a) := by
      have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have := (h0.comp hφ_atTop)
      simpa using (tendsto_const_nhds (x := a)).sub this
    -- pointwise a - 1/(φ j + 1) ≤ W (x (φ j)) ω
    have hle : ∀ j, a - 1 / ((φ j : ℝ) + 1) ≤ bm.W (x (φ j)) ω := by
      intro j
      have := hWq (φ j)
      simp only [hx]
      push_cast at this ⊢
      linarith
    exact le_of_tendsto_of_tendsto' hlow hWtend hle

/-! ## Measurability of the hitting event under a filtration -/

/-- **The first-passage event is observable by time `T`.** If each time-slice `W t` is
adapted to a filtration `ℱ` (so `W t` is `ℱ t`-measurable), then the hitting event
`{ω | ∃ s ∈ [0,T], a ≤ W s ω}` is `ℱ T`-measurable. This is the measurability content that
makes the first passage time a stopping time in continuous time. -/
theorem measurableSet_maxEvent (ℱ : Filtration ℝ m) (bm : BrownianMotion Ω μ)
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (bm.W t)) (a T : ℝ) (hT : 0 ≤ T) :
    MeasurableSet[ℱ T] (maxEvent bm a T) := by
  rw [maxEvent_eq_iInter_approxEvent bm a T hT]
  refine MeasurableSet.iInter (fun k => ?_)
  unfold approxEvent
  -- the union ranges over the countable set {q : ℚ | q ∈ [0,T]}
  refine MeasurableSet.biUnion (Set.to_countable {q : ℚ | (0 : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ T})
    (fun q hq => ?_)
  -- q ∈ [0,T]: W q is ℱ q-measurable, and ℱ q ≤ ℱ T, so the open-ray preimage is in ℱ T
  have hWq : Measurable[ℱ T] (bm.W (q : ℝ)) :=
    (hadapt (q : ℝ)).mono (ℱ.mono hq.2) le_rfl
  have hset : {ω | a - 1 / (k + 1) < bm.W (q : ℝ) ω}
      = bm.W (q : ℝ) ⁻¹' Ioi (a - 1 / (k + 1)) := by
    ext ω; simp [mem_Ioi]
  rw [hset]
  exact hWq measurableSet_Ioi

/-! ## First passage time is a stopping time -/

/-- **First passage is a stopping time.** Under adaptedness of the paths and the standing
nonemptiness hypothesis (every path actually reaches level `a`, so that `τ ≤ T` is genuinely the
hitting event rather than the degenerate `sInf ∅ = 0` value), the first-passage event
`{ω | firstPassageTime bm a ω ≤ T}` is `ℱ T`-measurable for every `T > 0`.

Combined with `firstPassageTime ≥ 0`, this is the stopping-time property: the event "the
process has hit level `a` by time `T`" is observable using only the information available at
time `T`. -/
theorem firstPassage_measurableSet (ℱ : Filtration ℝ m) (bm : BrownianMotion Ω μ)
    (hadapt : ∀ t : ℝ, Measurable[ℱ t] (bm.W t)) (a T : ℝ) (hT : 0 < T)
    (hne : ∀ ω, ({t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a}).Nonempty) :
    MeasurableSet[ℱ T] {ω | firstPassageTime bm a ω ≤ T} := by
  rw [fpt_le_set_eq_maxEvent bm a T hT hne]
  exact measurableSet_maxEvent ℱ bm hadapt a T (le_of_lt hT)

/-- The hitting event is monotone in the horizon `T`: more time can only help the path reach
level `a`. (A sanity companion to the measurability result: the family `T ↦ maxEvent bm a T` is
the increasing family of events whose `ℱ T`-measurability is the stopping-time property.) -/
theorem maxEvent_mono (bm : BrownianMotion Ω μ) (a : ℝ) {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) :
    maxEvent bm a T₁ ⊆ maxEvent bm a T₂ := by
  rintro ω ⟨s, ⟨hs0, hsT₁⟩, hsge⟩
  exact ⟨s, ⟨hs0, le_trans hsT₁ h⟩, hsge⟩

end BallotProblemOQ02OQ02OQ05
