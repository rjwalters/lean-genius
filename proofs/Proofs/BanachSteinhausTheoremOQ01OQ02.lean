/-
# Banach–Steinhaus: the resonance set is comeagre (condensation of singularities)

The gallery entry `banach-steinhaus-theorem-oq-01` packages Mathlib's uniform
boundedness principle together with its *condensation of singularities*
contrapositive (`resonance`): if a family `g : ι → E →SL[σ₁₂] F` of continuous
linear maps out of a Banach space has unbounded operator norms, then there is a
*single* resonance point `x` at which the values `‖g i x‖` are unbounded.

That contrapositive only asserts the resonance set is *nonempty*. Its open
question asks for the **quantitative Baire-category strengthening**: the
resonance set

  `R = { x : E | ∀ C, ∃ i, C < ‖g i x‖ }`   (equivalently `⨆ i, ‖g i x‖ = ∞`)

is not merely nonempty but **comeagre** — it is a residual set, hence (since a
Banach space is a Baire space) *dense*. The set of points where the family
condenses its singularities is topologically generic.

This file proves that strengthening from scratch:

* `resonanceSet` — the set of resonance points;
* `sublevel_isClosed` — the sublevel sets `{x | ∀ i, ‖g i x‖ ≤ n}` are closed;
* `sublevel_interior_eq_empty` — under unbounded operator norms each sublevel
  set has empty interior (the only place Banach–Steinhaus itself is used: a
  sublevel set with nonempty interior would force pointwise — hence uniform —
  boundedness);
* `resonanceSet_comeagre` — **the main result**: `R` is residual (comeagre);
* `resonanceSet_compl_isMeagre` — equivalently, its complement is meagre;
* `resonanceSet_dense` — `R` is dense in a Banach space;
* `resonance_of_comeagre` — the comeagre statement recovers the parent's single
  resonance point, so this genuinely strengthens `resonance`.

All results are verified with no axioms and no `sorry`.
-/
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Tactic

open Filter Topology Set Metric

namespace BanachSteinhausResonance

variable {𝕜 𝕜₂ : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ₁₂]
  {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {ι : Type*}

/-- The **resonance set** of an operator family `g`: the points `x` at which the
values `‖g i x‖` are unbounded over `i` (equivalently `⨆ i, ‖g i x‖ = ∞`). -/
def resonanceSet (g : ι → E →SL[σ₁₂] F) : Set E :=
  {x | ∀ C : ℝ, ∃ i, C < ‖g i x‖}

set_option linter.unusedSectionVars false in
/-- The sublevel set `{x | ∀ i, ‖g i x‖ ≤ n}` is closed: it is an intersection of
the closed sets `{x | ‖g i x‖ ≤ n}`, each a sublevel set of the continuous map
`x ↦ ‖g i x‖`. -/
theorem sublevel_isClosed (g : ι → E →SL[σ₁₂] F) (n : ℝ) :
    IsClosed {x : E | ∀ i, ‖g i x‖ ≤ n} := by
  rw [setOf_forall]
  exact isClosed_iInter fun i =>
    isClosed_le (continuous_norm.comp (g i).continuous) continuous_const

/-- Under **unbounded operator norms**, every sublevel set `{x | ∀ i, ‖g i x‖ ≤ n}`
has empty interior. This is the heart of the Baire-category argument and the only
step that invokes Banach–Steinhaus: a sublevel set with nonempty interior would
contain a ball, and rescaling translates of that ball through the (semi)linear
maps would bound the values `‖g i x‖` at *every* point — pointwise boundedness,
which `banach_steinhaus` upgrades to a uniform bound, contradicting the
hypothesis. -/
theorem sublevel_interior_eq_empty [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ C : ℝ, ∃ i, C < ‖g i‖) (n : ℝ) :
    interior {x : E | ∀ i, ‖g i x‖ ≤ n} = ∅ := by
  by_contra hne
  -- A nonempty interior contains a ball `ball x₀ r ⊆ {x | ∀ i, ‖g i x‖ ≤ n}`.
  obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x₀ hx₀
  have hballV : ball x₀ r ⊆ {x : E | ∀ i, ‖g i x‖ ≤ n} := hball.trans interior_subset
  have hx0V : ∀ i, ‖g i x₀‖ ≤ n := interior_subset hx₀
  -- The family is pointwise bounded everywhere.
  have hpb : ∀ x : E, ∃ C, ∀ i, ‖g i x‖ ≤ C := by
    intro x
    -- Pick a small nonzero scalar `c` with `‖c‖ * (‖x‖ + 1) < r`.
    obtain ⟨c, hc_pos, hc_lt⟩ :=
      NormedField.exists_norm_lt 𝕜 (show (0:ℝ) < r / (‖x‖ + 1) by positivity)
    have hcx : ‖c‖ * (‖x‖ + 1) < r := (lt_div_iff₀ (by positivity)).mp hc_lt
    refine ⟨2 * n / ‖c‖, fun i => ?_⟩
    -- `x₀ + c • x` lies in the ball, hence in the sublevel set.
    have hnorm_cx : ‖c • x‖ < r := by
      rw [norm_smul]
      calc ‖c‖ * ‖x‖ ≤ ‖c‖ * (‖x‖ + 1) := by gcongr; linarith [norm_nonneg x]
        _ < r := hcx
    have hmem : ∀ j, ‖g j (x₀ + c • x)‖ ≤ n :=
      hballV (by rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hnorm_cx)
    -- `g i (c • x) = g i (x₀ + c • x) - g i x₀`, so its norm is `≤ 2 * n`.
    have hsplit : σ₁₂ c • g i x = g i (x₀ + c • x) - g i x₀ := by
      rw [map_add, map_smulₛₗ]; abel
    have hbound : ‖c‖ * ‖g i x‖ ≤ 2 * n := by
      have hle : ‖σ₁₂ c • g i x‖ ≤ 2 * n := by
        rw [hsplit]
        calc ‖g i (x₀ + c • x) - g i x₀‖
            ≤ ‖g i (x₀ + c • x)‖ + ‖g i x₀‖ := norm_sub_le _ _
          _ ≤ n + n := add_le_add (hmem i) (hx0V i)
          _ = 2 * n := by ring
      rwa [norm_smul, RingHomIsometric.norm_map] at hle
    -- Divide by `‖c‖ > 0`.
    rw [le_div_iff₀ hc_pos, mul_comm]
    exact hbound
  -- Pointwise bounded ⇒ uniformly bounded, contradicting unbounded norms.
  obtain ⟨C', hC'⟩ := banach_steinhaus hpb
  obtain ⟨i, hi⟩ := h C'
  exact absurd (hC' i) (not_le.mpr hi)

/-- **The resonance set is comeagre.** If the operator norms of a family of
continuous linear maps out of a Banach space are unbounded, then the set of
resonance points (where the values `‖g i x‖` are unbounded) is residual.

This is the Baire-category strengthening of the condensation-of-singularities
contrapositive: failure of uniform boundedness is witnessed not just at one
point, but on a topologically generic (comeagre) set. -/
theorem resonanceSet_comeagre [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ C : ℝ, ∃ i, C < ‖g i‖) : resonanceSet g ∈ residual E := by
  -- It suffices to show the complement is meagre.
  suffices hmeagre : IsMeagre (resonanceSet g)ᶜ by
    rwa [IsMeagre, compl_compl] at hmeagre
  -- The complement is contained in a countable union of sublevel sets.
  have hsub : (resonanceSet g)ᶜ ⊆ ⋃ n : ℕ, {x : E | ∀ i, ‖g i x‖ ≤ (n : ℝ)} := by
    intro x hx
    simp only [resonanceSet, mem_compl_iff, mem_setOf_eq, not_forall, not_exists,
      not_lt] at hx
    obtain ⟨C, hC⟩ := hx
    obtain ⟨n, hn⟩ := exists_nat_ge C
    exact mem_iUnion.mpr ⟨n, fun i => (hC i).trans hn⟩
  refine IsMeagre.mono hsub (isMeagre_iUnion fun n => ?_)
  -- Each sublevel set is closed with empty interior, hence nowhere dense, hence meagre.
  have hnwd : IsNowhereDense {x : E | ∀ i, ‖g i x‖ ≤ (n : ℝ)} :=
    (sublevel_isClosed g _).isNowhereDense_iff.mpr (sublevel_interior_eq_empty h _)
  rw [isMeagre_iff_countable_union_isNowhereDense]
  exact ⟨{{x : E | ∀ i, ‖g i x‖ ≤ (n : ℝ)}}, by simpa using hnwd, countable_singleton _,
    by simp⟩

/-- Equivalent phrasing of `resonanceSet_comeagre`: the complement of the
resonance set — the points where the family is pointwise bounded — is meagre. -/
theorem resonanceSet_compl_isMeagre [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ C : ℝ, ∃ i, C < ‖g i‖) : IsMeagre (resonanceSet g)ᶜ := by
  rw [IsMeagre, compl_compl]; exact resonanceSet_comeagre h

/-- **The resonance set is dense.** Since a Banach space is a Baire space, the
comeagre resonance set is dense: resonance points are not just generic, they are
arbitrarily close to every point of the space. -/
theorem resonanceSet_dense [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ C : ℝ, ∃ i, C < ‖g i‖) : Dense (resonanceSet g) :=
  dense_of_mem_residual (resonanceSet_comeagre h)

/-- The comeagre strengthening recovers the parent gallery entry's `resonance`
statement: a comeagre (in particular nonempty) resonance set yields a single
point at which the values `‖g i x‖` are unbounded. This shows the present result
genuinely strengthens the condensation-of-singularities contrapositive. -/
theorem resonance_of_comeagre [CompleteSpace E] {g : ι → E →SL[σ₁₂] F}
    (h : ∀ C : ℝ, ∃ i, C < ‖g i‖) : ∃ x : E, ∀ C : ℝ, ∃ i, C < ‖g i x‖ :=
  (resonanceSet_dense h).nonempty

end BanachSteinhausResonance
