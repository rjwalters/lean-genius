import Mathlib
import Proofs.LebesgueMeasureOQ01OQ01OQ01

/-
# Thomae's Function and Baire Category — the continuity set is a dense Gδ

## Open Question (lebesgue-measure-oq-01-oq-01-oq-02-oq-02)

Thomae's (popcorn) function is continuous exactly at the irrationals and
discontinuous exactly at the rationals.  The green formalization
`lebesgue-measure-oq-01-oq-01-oq-01` (module `LebesgueMeasureOQ01OQ01OQ01`)
supplies `thomae`, `thomae_irrational`, `thomae_rat`, and the hard direction
`thomae_continuous_at_irrational`.  Here we first recover the complementary
direction `thomae_discontinuous_at_rat` (via an irrational sequence
`r + √2/(n+1) → r`), assemble the sharp characterization
`thomae_continuous_iff : ContinuousAt thomae x ↔ Irrational x`, and then turn to
the new content.  The measure-theoretic lineage established that the
discontinuity set ℚ is **null** (Lebesgue's criterion).  This entry records the
**Baire-category dual**, the other half of "ℚ is small":

  * the set of continuity points of Thomae equals the irrationals, a **dense Gδ**
    set, hence **comeagre** (residual);
  * the set of discontinuity points equals ℚ, which is **meagre** (first
    category) — and, sharply, is **not** a Gδ set.

The Gδ-ness of the irrationals is *exactly* what makes Thomae possible.  The
general principle is that the continuity set of *any* function `f : ℝ → ℝ` is a
Gδ (`IsGδ.setOf_continuousAt`).  Combined with the Baire-category fact that ℚ is
not a Gδ, we obtain the classical impossibility theorem:

  **No function `f : ℝ → ℝ` is continuous exactly at the rationals.**

So Thomae's irrational-continuity is not a coincidence that could be mirrored:
the rational mirror is forbidden by topology, while the irrational realisation
is permitted — and exhibited by Thomae.

## What is proved

* `thomae_discontinuous_at_rat`        : `¬ ContinuousAt thomae (r : ℝ)` for `r : ℚ`
* `thomae_continuous_iff`              : `ContinuousAt thomae x ↔ Irrational x`
* `thomae_continuitySet_eq_irrational` : `{x | ContinuousAt thomae x} = {x | Irrational x}`
* `thomae_continuitySet_isGδ`          : the continuity set is Gδ
* `thomae_continuitySet_dense`         : the continuity set is dense
* `thomae_continuitySet_residual`      : the continuity set is comeagre (residual)
* `thomae_discontinuitySet_eq_rat`     : `{x | ¬ ContinuousAt thomae x} = range ℚ`
* `thomae_discontinuitySet_isMeagre`   : the discontinuity set is meagre
* `not_isGδ_range_rat`                 : ℚ is not a Gδ subset of ℝ (Baire)
* `thomae_discontinuitySet_not_isGδ`   : the discontinuity set is not Gδ
* `no_continuousAt_setOf_eq_rat`       : no `f : ℝ → ℝ` is continuous exactly on ℚ
* `thomae_realizes_irrational_continuitySet` : Thomae realises the irrationals as a continuity set

No sorries, no axioms.
-/

open Set Filter Topology Real
open LebesgueMeasureOQ01OQ01OQ01

namespace LebesgueMeasureOQ01OQ01OQ02OQ02

/-! ## The sharp continuity characterization

The green base module proves continuity at the irrationals and
`{x | ¬ ContinuousAt thomae x} ⊆ range ℚ`.  To get the *exact* characterization
we add the rational direction: along the irrational sequence `r + √2/(n+1) → r`
Thomae is identically `0`, but `thomae r = 1/r.den > 0`, so it cannot be
continuous at `r`. -/

/-- **Thomae is discontinuous at every rational.** -/
theorem thomae_discontinuous_at_rat (r : ℚ) : ¬ ContinuousAt thomae (r : ℝ) := by
  intro h
  -- The sequence `yₙ = r + √2/(n+1)` tends to `r` and is irrational at every `n`.
  have h0 : Tendsto (fun n : ℕ => Real.sqrt 2 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have hmul := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (Real.sqrt 2)
    simp only [mul_one_div, mul_zero] at hmul
    exact hmul
  have hlim : Tendsto (fun n : ℕ => (r : ℝ) + Real.sqrt 2 / ((n : ℝ) + 1))
      atTop (𝓝 (r : ℝ)) := by
    have := h0.const_add (r : ℝ)
    rwa [add_zero] at this
  have hirr : ∀ n : ℕ, Irrational ((r : ℝ) + Real.sqrt 2 / ((n : ℝ) + 1)) := by
    intro n
    have hd : Irrational (Real.sqrt 2 / ((n : ℝ) + 1)) := by
      have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hcast]
      exact irrational_sqrt_two.div_natCast (Nat.succ_ne_zero n)
    rw [add_comm]
    exact irrational_add_ratCast_iff.mpr hd
  -- Compose continuity with the sequence: `thomae yₙ → thomae r`.
  have htend : Tendsto (fun n : ℕ => thomae ((r : ℝ) + Real.sqrt 2 / ((n : ℝ) + 1)))
      atTop (𝓝 (thomae (r : ℝ))) := h.tendsto.comp hlim
  -- But `thomae yₙ = 0` for every `n`.
  have hzero : (fun n : ℕ => thomae ((r : ℝ) + Real.sqrt 2 / ((n : ℝ) + 1)))
      = fun _ => (0 : ℝ) := funext fun n => thomae_irrational (hirr n)
  rw [hzero] at htend
  -- Uniqueness of limits forces `thomae r = 0`, contradicting `thomae r = 1/r.den > 0`.
  have hval : thomae (r : ℝ) = 0 := tendsto_nhds_unique htend tendsto_const_nhds
  rw [thomae_rat] at hval
  have hpos : (0 : ℝ) < 1 / (r.den : ℝ) := by positivity
  linarith

/-- **Thomae is continuous exactly at the irrationals.** -/
theorem thomae_continuous_iff (x : ℝ) : ContinuousAt thomae x ↔ Irrational x := by
  constructor
  · intro h
    by_contra hrat
    simp only [Irrational, not_not] at hrat
    obtain ⟨q, hq⟩ := hrat
    exact thomae_discontinuous_at_rat q (hq ▸ h)
  · exact thomae_continuous_at_irrational

/-! ## Meagreness of countable sets (Baire-category infrastructure)

A countable set in a perfect `T1` space is a countable union of nowhere-dense
singletons, hence meagre.  (Same elementary argument as the companion entry
`algebraic-numbers-countable-oq-02-oq-04`; reproduced here so this file is
self-contained.) -/

/-- A nowhere-dense set is meagre: it is covered by the one-element (hence
countable) family `{t}` of nowhere-dense sets. -/
theorem isMeagre_of_isNowhereDense {X : Type*} [TopologicalSpace X] {t : Set X}
    (ht : IsNowhereDense t) : IsMeagre t := by
  rw [isMeagre_iff_countable_union_isNowhereDense]
  refine ⟨{t}, ?_, Set.countable_singleton t, ?_⟩
  · intro u hu
    rwa [Set.mem_singleton_iff.mp hu]
  · exact (Set.sUnion_singleton t).ge

/-- In a `T1` perfect space a singleton is nowhere dense: it is closed, and its
interior is empty because the point is not isolated. -/
theorem isNowhereDense_singleton {X : Type*} [TopologicalSpace X] [T1Space X]
    [PerfectSpace X] (x : X) : IsNowhereDense ({x} : Set X) :=
  (isClosed_singleton.isNowhereDense_iff).mpr (interior_singleton x)

/-- **Countable sets are meagre in a perfect `T1` space** (e.g. `ℝ`). -/
theorem countable_isMeagre {X : Type*} [TopologicalSpace X] [T1Space X] [PerfectSpace X]
    {s : Set X} (hs : s.Countable) : IsMeagre s := by
  rw [← Set.biUnion_of_singleton s, Set.biUnion_eq_iUnion]
  haveI : Countable s := hs.to_subtype
  exact isMeagre_iUnion fun i => isMeagre_of_isNowhereDense (isNowhereDense_singleton (i : X))

/-! ## The continuity set of Thomae is a dense Gδ -/

/-- **Thomae is continuous exactly at the irrationals**, as a set equality.
(Repackages the parent's `thomae_continuous_iff`.) -/
theorem thomae_continuitySet_eq_irrational :
    {x : ℝ | ContinuousAt thomae x} = {x : ℝ | Irrational x} := by
  ext x; exact thomae_continuous_iff x

/-- The continuity set of Thomae is a Gδ: it equals the irrationals, the
complement of the countable set `range ℚ`. -/
theorem thomae_continuitySet_isGδ : IsGδ {x : ℝ | ContinuousAt thomae x} := by
  rw [thomae_continuitySet_eq_irrational]
  exact IsGδ.setOf_irrational

/-- The continuity set of Thomae is dense (the irrationals are dense). -/
theorem thomae_continuitySet_dense : Dense {x : ℝ | ContinuousAt thomae x} := by
  rw [thomae_continuitySet_eq_irrational]
  exact dense_irrational

/-- **The continuity set of Thomae is comeagre (residual).** A dense Gδ in the
Baire space `ℝ` is residual. -/
theorem thomae_continuitySet_residual :
    {x : ℝ | ContinuousAt thomae x} ∈ residual ℝ := by
  rw [thomae_continuitySet_eq_irrational]
  exact residual_of_dense_Gδ IsGδ.setOf_irrational dense_irrational

/-! ## The discontinuity set of Thomae is exactly ℚ, and is meagre -/

/-- **Thomae is discontinuous exactly at the rationals**: the discontinuity set
equals `range ℚ`.  (`Irrational x` is definitionally `x ∉ range ℚ`, so
`¬ Irrational x ↔ x ∈ range ℚ` by `not_not`.) -/
theorem thomae_discontinuitySet_eq_rat :
    {x : ℝ | ¬ ContinuousAt thomae x} = Set.range ((↑) : ℚ → ℝ) := by
  ext x
  rw [Set.mem_setOf_eq, thomae_continuous_iff]
  exact not_not

/-- The discontinuity set of Thomae is meagre: it is the countable set `range ℚ`. -/
theorem thomae_discontinuitySet_isMeagre :
    IsMeagre {x : ℝ | ¬ ContinuousAt thomae x} := by
  rw [thomae_discontinuitySet_eq_rat]
  exact countable_isMeagre (Set.countable_range _)

/-! ## ℚ is not a Gδ, and rational continuity sets are impossible -/

/-- **The rationals are not a Gδ subset of `ℝ`.** If `range ℚ` were Gδ it would
be a dense Gδ, hence non-meagre by Baire; but it is countable, hence meagre. -/
theorem not_isGδ_range_rat : ¬ IsGδ (Set.range ((↑) : ℚ → ℝ)) := by
  intro h
  exact not_isMeagre_of_isGδ_of_dense h Rat.denseRange_cast
    (countable_isMeagre (Set.countable_range _))

/-- The discontinuity set of Thomae is **not** a Gδ (it is exactly `range ℚ`).
This is the sharp asymmetry with the continuity set, which *is* a dense Gδ. -/
theorem thomae_discontinuitySet_not_isGδ :
    ¬ IsGδ {x : ℝ | ¬ ContinuousAt thomae x} := by
  rw [thomae_discontinuitySet_eq_rat]
  exact not_isGδ_range_rat

/-- **No function `f : ℝ → ℝ` is continuous exactly at the rationals.** The
continuity set of any function is a Gδ (`IsGδ.setOf_continuousAt`), but
`range ℚ` is not a Gδ. -/
theorem no_continuousAt_setOf_eq_rat :
    ¬ ∃ f : ℝ → ℝ, {x : ℝ | ContinuousAt f x} = Set.range ((↑) : ℚ → ℝ) := by
  rintro ⟨f, hf⟩
  exact not_isGδ_range_rat (hf ▸ IsGδ.setOf_continuousAt f)

/-- **Thomae realises the irrationals as a continuity set** — possible precisely
because the irrationals form a Gδ.  The mirror image (continuity exactly on ℚ)
is impossible by `no_continuousAt_setOf_eq_rat`. -/
theorem thomae_realizes_irrational_continuitySet :
    {x : ℝ | ContinuousAt thomae x} = {x : ℝ | Irrational x} ∧
      IsGδ {x : ℝ | ContinuousAt thomae x} :=
  ⟨thomae_continuitySet_eq_irrational, thomae_continuitySet_isGδ⟩

end LebesgueMeasureOQ01OQ01OQ02OQ02
