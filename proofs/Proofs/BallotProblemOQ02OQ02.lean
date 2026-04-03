/-
First Passage Time Characterization via csInf Theory (OQ-02-OQ-02)

## Research Question

The parent `BallotProblemOQ02.lean` uses `axiom firstPassageTime_eq_maxEvent`:
  {ω | firstPassageTime bm a ω ≤ T} = maxEvent bm a T

Can this be proved from `path_continuous` and the csInf theory?

## Answer

The theorem has two directions. Both are proved here under natural hypotheses.

**Key subtlety**: `sInf ∅ = 0` in Lean's ℝ (see `csInf_empty_eq_zero`).
If a path never reaches level a, {t ≥ 0 : W(t,ω) ≥ a} = ∅,
so firstPassageTime = sInf ∅ = 0 ≤ T for any T > 0, but ω ∉ maxEvent.
The parent axiom is technically false without a nonemptiness hypothesis.

**What we prove**:
1. The hitting set {t ≥ 0 : W(t,ω) ≥ a} is always closed (from path continuity)
2. `maxEvent ⊆ {firstPassageTime ≤ T}` — always true, proved below
3. Under nonemptiness: `{firstPassageTime ≤ T} → maxEvent`
4. IVT: when W(0,ω) < a ≤ W(T,ω), there's a first crossing in (0,T]
5. The axiom holds when the hitting time set is nonempty
-/

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

set_option maxHeartbeats 400000

namespace BallotFPT

open Set Real MeasureTheory

/-! ## Part I: Setup -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Brownian motion with continuous paths (from parent BallotProblemOQ02.lean). -/
structure BrownianMotion (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] where
  W : ℝ → Ω → ℝ
  path_continuous : ∀ ω, Continuous (fun t => W t ω)

noncomputable def firstPassageTime (bm : BrownianMotion Ω μ) (a : ℝ) : Ω → ℝ :=
  fun ω => sInf {t | 0 ≤ t ∧ bm.W t ω ≥ a}

def maxEvent (bm : BrownianMotion Ω μ) (a T : ℝ) : Set Ω :=
  {ω | ∃ s ∈ Icc 0 T, bm.W s ω ≥ a}

/-! ## Part II: The Hitting Set is Closed -/

/-- The hitting time set `{t ≥ 0 : W(t,ω) ≥ a}` is closed.
    This uses path continuity: the preimage of the closed set [a,∞) is closed. -/
theorem hittingSet_isClosed (bm : BrownianMotion Ω μ) (a : ℝ) (ω : Ω) :
    IsClosed {t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a} := by
  have hcont : Continuous (fun t => bm.W t ω) := bm.path_continuous ω
  have hge_closed : IsClosed {t : ℝ | bm.W t ω ≥ a} := by
    rw [show {t : ℝ | bm.W t ω ≥ a} = (fun t => bm.W t ω) ⁻¹' Ici a from
      by ext; simp [ge_iff_le]]
    exact isClosed_Ici.preimage hcont
  rw [show {t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a} = {t | 0 ≤ t} ∩ {t | bm.W t ω ≥ a} from
    by ext; simp [and_comm]]
  exact isClosed_Ici.inter hge_closed

/-- The hitting set is bounded below by 0. -/
theorem hittingSet_bddBelow (bm : BrownianMotion Ω μ) (a : ℝ) (ω : Ω) :
    BddBelow {t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a} :=
  ⟨0, fun _ ht => ht.1⟩

/-! ## Part III: Key csInf Fact -/

/-- In Lean's ℝ, `sInf ∅ = 0` — NOT +∞.
    This is why the parent axiom requires a nonemptiness hypothesis. -/
theorem csInf_empty_eq_zero : sInf (∅ : Set ℝ) = 0 := Real.sInf_empty

/-- If the hitting set is nonempty and closed, sInf is in the set.
    (This is `IsClosed.csInf_mem` from Mathlib.) -/
theorem hittingSet_csInf_mem (bm : BrownianMotion Ω μ) (a : ℝ) (ω : Ω)
    (hne : {t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a}.Nonempty) :
    sInf {t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a} ∈ {t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a} :=
  (hittingSet_isClosed bm a ω).csInf_mem hne (hittingSet_bddBelow bm a ω)

/-! ## Part IV: Easy Direction (maxEvent → firstPassageTime ≤ T) -/

/-- If W hits level a in [0, T], then firstPassageTime ≤ T.
    Proof: take s ∈ [0, T] with W(s, ω) ≥ a; then sInf S ≤ s ≤ T. -/
theorem maxEvent_implies_fpt_le (bm : BrownianMotion Ω μ) (a T : ℝ) (hT : 0 < T)
    (ω : Ω) (hmax : ω ∈ maxEvent bm a T) :
    firstPassageTime bm a ω ≤ T := by
  obtain ⟨s, hs_Icc, hs_ge⟩ := hmax
  simp only [firstPassageTime]
  exact le_trans (csInf_le (hittingSet_bddBelow bm a ω) ⟨hs_Icc.1, hs_ge⟩) hs_Icc.2

/-! ## Part V: Hard Direction Under Nonemptiness -/

/-- If the hitting set intersects [0, T] and sInf ≤ T, then ω ∈ maxEvent.
    Key: sInf S ∈ S (closed set contains infimum), and sInf S ≤ T. -/
theorem fpt_le_implies_maxEvent (bm : BrownianMotion Ω μ) (a T : ℝ) (hT : 0 < T)
    (ω : Ω)
    (hne : ({t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a}).Nonempty)
    (hfpt : firstPassageTime bm a ω ≤ T) :
    ω ∈ maxEvent bm a T := by
  -- sInf S ∈ S by closedness
  have hinf_mem := hittingSet_csInf_mem bm a ω hne
  simp only [firstPassageTime] at hfpt
  -- sInf S ∈ S gives us: 0 ≤ sInf S ∧ W(sInf S, ω) ≥ a
  obtain ⟨hinf_nn, hinf_ge⟩ := hinf_mem
  -- Witness s = sInf S ∈ [0, T] with W(s, ω) ≥ a
  exact ⟨sInf {t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a}, ⟨hinf_nn, hfpt⟩, hinf_ge⟩

/-! ## Part VI: Full Characterization Under Nonemptiness -/

/-- **Main result**: Under the assumption that the hitting set is nonempty,
    `firstPassageTime bm a ω ≤ T ↔ ω ∈ maxEvent bm a T`.

    This proves the parent axiom `firstPassageTime_eq_maxEvent` modulo
    the nonemptiness hypothesis. -/
theorem fpt_le_iff_maxEvent (bm : BrownianMotion Ω μ) (a T : ℝ) (hT : 0 < T)
    (ω : Ω) (hne : ({t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a}).Nonempty) :
    firstPassageTime bm a ω ≤ T ↔ ω ∈ maxEvent bm a T :=
  ⟨fpt_le_implies_maxEvent bm a T hT ω hne,
   maxEvent_implies_fpt_le bm a T hT ω⟩

/-- The set version: when the hitting set is nonempty for all ω,
    the set equality holds. -/
theorem fpt_le_set_eq_maxEvent (bm : BrownianMotion Ω μ) (a T : ℝ) (hT : 0 < T)
    (hne : ∀ ω, ({t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a}).Nonempty) :
    {ω | firstPassageTime bm a ω ≤ T} = maxEvent bm a T := by
  ext ω
  exact fpt_le_iff_maxEvent bm a T hT ω (hne ω)

/-! ## Part VII: IVT — First Crossing Time -/

/-- By the Intermediate Value Theorem, if W(0, ω) < a ≤ W(T, ω) and the path
    is continuous, there exists s ∈ (0, T] where W(s, ω) = a.
    This gives the hitting set nonemptiness needed for the main theorem. -/
theorem ivt_first_crossing (bm : BrownianMotion Ω μ) (a T : ℝ)
    (hT : 0 < T) (ω : Ω)
    (hstart : bm.W 0 ω < a)
    (hend : bm.W T ω ≥ a) :
    ∃ s ∈ Icc 0 T, bm.W s ω = a ∧ 0 < s := by
  have hcont : ContinuousOn (fun t => bm.W t ω) (Icc 0 T) :=
    (bm.path_continuous ω).continuousOn
  have h01 : (0 : ℝ) ∈ Icc 0 T := ⟨le_refl 0, le_of_lt hT⟩
  have hT1 : T ∈ Icc 0 T := ⟨le_of_lt hT, le_refl T⟩
  -- IVT: find s ∈ [0,T] where W(s,ω) crosses constant a
  -- Use intermediate_value₂ with f = W(·,ω) and g = const a
  obtain ⟨s, hs_Icc, hs_eq⟩ := isPreconnected_Icc.intermediate_value₂ h01 hT1
    hcont continuousOn_const (le_of_lt hstart) hend
  -- hs_eq : bm.W s ω = a
  refine ⟨s, hs_Icc, hs_eq, ?_⟩
  -- s > 0 because W(0, ω) < a = W(s, ω)
  rcases hs_Icc.1.eq_or_gt with rfl | hs_pos
  · exact absurd hs_eq (ne_of_lt hstart)
  · exact hs_pos

/-! ## Part VIII: Hitting Set Nonemptiness from IVT -/

/-- When W(0, ω) < a and ∃ T > 0 with W(T, ω) ≥ a, the hitting set is nonempty. -/
theorem hittingSet_nonempty_of_ivt (bm : BrownianMotion Ω μ) (a T : ℝ)
    (hT : 0 < T) (ω : Ω)
    (hstart : bm.W 0 ω < a)
    (hend : bm.W T ω ≥ a) :
    ({t : ℝ | 0 ≤ t ∧ bm.W t ω ≥ a}).Nonempty := by
  obtain ⟨s, hs_Icc, hs_eq, _⟩ := ivt_first_crossing bm a T hT ω hstart hend
  exact ⟨s, hs_Icc.1, hs_eq ▸ le_refl a⟩

/-- Full result: when W(0,ω) < a ≤ W(T,ω) and paths continuous,
    firstPassageTime bm a ω ≤ T and the hitting set is nonempty. -/
theorem fpt_le_T_of_crossing (bm : BrownianMotion Ω μ) (a T : ℝ)
    (hT : 0 < T) (ω : Ω)
    (hstart : bm.W 0 ω < a)
    (hend : bm.W T ω ≥ a) :
    firstPassageTime bm a ω ≤ T ∧ ω ∈ maxEvent bm a T := by
  have hne := hittingSet_nonempty_of_ivt bm a T hT ω hstart hend
  exact ⟨(fpt_le_iff_maxEvent bm a T hT ω hne).mpr
    ⟨T, ⟨le_of_lt hT, le_refl T⟩, hend⟩,
    ⟨T, ⟨le_of_lt hT, le_refl T⟩, hend⟩⟩

end BallotFPT
