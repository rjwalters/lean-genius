import Mathlib.MeasureTheory.Function.Egorov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-
# Egorov's Theorem is Sharp: the Finiteness Hypothesis is Essential

## What This Proves

**Egorov's theorem** says that on a set `s` of *finite* measure, almost-everywhere
convergence `fₙ → g` upgrades to uniform convergence off an arbitrarily small set.
The finiteness hypothesis `μ s ≠ ∞` is not a technical convenience -- it is genuinely
necessary. This file makes that precise with the canonical counterexample on the
σ-finite-but-infinite space `(ℝ, Lebesgue)`.

The **marching indicators** are the unit-width bumps that walk off to infinity:

  `marching n = 𝟙_{[n, n+1)}`,   i.e.   `marching n x = 1` if `n ≤ x < n+1`, else `0`.

We prove three facts that together show Egorov's conclusion *fails* once the ambient
measure is infinite:

* `marching_stronglyMeasurable` -- each `marching n` is (strongly) measurable, so the
  family satisfies every hypothesis of Egorov's theorem *except* finiteness.

* `marching_tendsto_zero` -- the sequence converges to `0` at **every** point of `ℝ`
  (not merely almost everywhere): for fixed `x`, once `n > x` the point `x` has been
  passed, so `marching n x = 0` for all large `n`.

* `marching_not_tendstoUniformlyOn` -- for **every** set `t` of finite Lebesgue
  measure, the sequence does *not* converge uniformly to `0` on the complement `tᶜ`.
  In particular no exceptional set of finite (let alone arbitrarily small) measure can
  be removed to obtain uniform convergence.

The capstone `egorov_finiteness_essential` bundles the three. The contrast with the
finite-measure case (`EgorovTheorem.pow_egorov_on_Icc`, where Egorov *does* apply) is
exactly the point: on `[0,1]` removing a small set works; on `ℝ` it cannot.

### Why `marching_not_tendstoUniformlyOn` holds

If `t` has finite measure then `t` cannot contain the whole ray `[N, ∞)` (which has
infinite measure), so for every `N` there is an integer `n ≥ N` and a point
`x ∈ [n, n+1) \ t`. At that point `marching n x = 1`, keeping `supₓ∈tᶜ |marching n x|`
equal to `1` infinitely often -- the negation of uniform convergence.

## Why It Is Not in Mathlib

Mathlib has the abstract Egorov theorem (`MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`)
and the sibling gallery file `EgorovTheorem.lean` exhibits its non-vacuity on `[0,1]`.
Neither states the *necessity of the finiteness hypothesis*; the marching-indicator
counterexample, its everywhere-convergence, and the no-finite-exceptional-set witness
are the new content. This answers the open question `egorov-theorem-oq-01-oq-01`.

## Axiom Status

Fully verified, 0 sorries, 0 `axiom` declarations, no `native_decide`. Relies only on
Mathlib's measure theory and the foundational axioms `propext`, `Classical.choice`,
`Quot.sound`.
-/

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace EgorovMarching

/-! ## The marching indicators -/

/-- The marching indicators `marching n = 𝟙_{[n, n+1)}`: a unit-height bump on the
half-open interval `[n, n+1)` that walks off to `+∞` as `n → ∞`. -/
noncomputable def marching (n : ℕ) : ℝ → ℝ :=
  (Set.Ico (n : ℝ) (n + 1)).indicator (fun _ => 1)

/-- On its own block the bump has value `1`. -/
theorem marching_apply_mem {n : ℕ} {x : ℝ} (hx : x ∈ Set.Ico (n : ℝ) (n + 1)) :
    marching n x = 1 := by
  rw [marching, Set.indicator_of_mem hx]

/-- Each marching indicator is strongly measurable, so the family meets every
hypothesis of Egorov's theorem *except* the finiteness of the ambient measure. -/
theorem marching_stronglyMeasurable (n : ℕ) : StronglyMeasurable (marching n) :=
  (stronglyMeasurable_const).indicator measurableSet_Ico

/-! ## Everywhere (hence a.e.) convergence to zero -/

/-- The marching indicators converge to `0` at **every** real point: for fixed `x`,
all blocks past `⌊x⌋₊` lie strictly to the right of `x`, so `marching n x = 0` for
every `n > ⌊x⌋₊`. -/
theorem marching_tendsto_zero (x : ℝ) :
    Tendsto (fun n => marching n x) atTop (𝓝 (0 : ℝ)) := by
  have hev : ∀ᶠ n in atTop, marching n x = 0 := by
    filter_upwards [eventually_gt_atTop ⌊x⌋₊] with n hn
    have hnotmem : x ∉ Set.Ico (n : ℝ) (n + 1) := by
      rw [Set.mem_Ico]
      rintro ⟨h1, _⟩
      have hcast : (⌊x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast Nat.add_one_le_iff.mpr hn
      have hlt := Nat.lt_floor_add_one x
      linarith
    rw [marching, Set.indicator_of_notMem hnotmem]
  exact tendsto_const_nhds.congr' (hev.mono fun n hn => hn.symm)

/-! ## No finite-measure exceptional set: failure of Egorov's conclusion -/

/-- Key geometric obstruction. If `t` has *finite* Lebesgue measure then it cannot
contain the entire ray `[N, ∞)`, so beyond any threshold `N` some block `[n, n+1)`
(with `n ≥ N`) still pokes out of `t`: there is `x ∈ [n, n+1)` with `x ∉ t`. -/
theorem exists_uncovered {t : Set ℝ} (ht : volume t ≠ ∞) (N : ℕ) :
    ∃ n ≥ N, ∃ x, x ∈ Set.Ico (n : ℝ) (n + 1) ∧ x ∉ t := by
  by_contra h
  push_neg at h
  -- Then every block past `N` lies inside `t`, forcing `[N, ∞) ⊆ t`.
  have hsub : Set.Ici (N : ℝ) ⊆ t := by
    intro x hx
    rw [Set.mem_Ici] at hx
    have hxnn : (0 : ℝ) ≤ x := le_trans (Nat.cast_nonneg N) hx
    have hnN : N ≤ ⌊x⌋₊ := Nat.le_floor hx
    have hxlo : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxnn
    have hxhi : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    exact h ⌊x⌋₊ hnN x ⟨hxlo, hxhi⟩
  -- But `[N, ∞)` has infinite measure, contradicting `volume t ≠ ∞`.
  have hbig : volume (Set.Ici (N : ℝ)) ≤ volume t := measure_mono hsub
  rw [Real.volume_Ici] at hbig
  exact ht (top_le_iff.mp hbig)

/-- **The finiteness hypothesis of Egorov's theorem is essential.** For every set `t`
of finite Lebesgue measure, the marching indicators do *not* converge uniformly to `0`
on `tᶜ` -- even though they converge to `0` everywhere on `ℝ`. Hence no finite-measure
(in particular no arbitrarily small) exceptional set can be removed to recover uniform
convergence on the σ-finite-but-infinite space `(ℝ, Lebesgue)`. -/
theorem marching_not_tendstoUniformlyOn {t : Set ℝ} (ht : volume t ≠ ∞) :
    ¬ TendstoUniformlyOn marching (fun _ => (0 : ℝ)) atTop tᶜ := by
  intro h
  rw [Metric.tendstoUniformlyOn_iff] at h
  have key := h (1 / 2) (by norm_num)
  rw [eventually_atTop] at key
  obtain ⟨N, hN⟩ := key
  obtain ⟨n, hnN, x, hxmem, hxnt⟩ := exists_uncovered ht N
  have hxc : x ∈ tᶜ := hxnt
  have hfx : marching n x = 1 := marching_apply_mem hxmem
  have hlt := hN n hnN x hxc
  simp only [hfx, Real.dist_eq] at hlt
  norm_num at hlt

/-! ## Capstone -/

/-- **Egorov's theorem is sharp.** The marching indicators on `(ℝ, Lebesgue)` are
strongly measurable and converge to `0` at every point, yet no finite-measure set can
be removed to make the convergence uniform. The single failing hypothesis relative to
Egorov's theorem is finiteness of the ambient measure, so that hypothesis cannot be
dropped. -/
theorem egorov_finiteness_essential :
    (∀ n, StronglyMeasurable (marching n)) ∧
      (∀ x, Tendsto (fun n => marching n x) atTop (𝓝 (0 : ℝ))) ∧
      (∀ t : Set ℝ, volume t ≠ ∞ →
        ¬ TendstoUniformlyOn marching (fun _ => (0 : ℝ)) atTop tᶜ) :=
  ⟨marching_stronglyMeasurable, marching_tendsto_zero,
    fun _ ht => marching_not_tendstoUniformlyOn ht⟩

end EgorovMarching
