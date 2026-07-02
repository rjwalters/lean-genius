/-
Blichfeldt's Generalization of Minkowski's Fundamental Theorem
(minkowski-fundamental-theorem-oq-03)

This file formalizes the *general-multiplicity* form of Blichfeldt's principle,
the honest generalization of Minkowski's fundamental theorem to a lattice of
arbitrary "packing multiplicity".

## Statement

Let `L` be a countable subgroup acting on a measure space `E` with an additive
fundamental domain `F` of covolume `μ F`, and let `s` be any null-measurable set.
If

  `k · μ F < μ s`

then there exist more than `k` lattice elements `l` and a common point `z` with
`z ∈ l +ᵥ s` for every such `l`.  Equivalently (in a group), there are `k + 1`
points of `s` that are pairwise congruent modulo `L`.

At `k = 1` this is exactly Mathlib's
`MeasureTheory.exists_pair_mem_lattice_not_disjoint_vadd` (Blichfeldt's principle,
two points), and it is the multiplicity input from which the general-`k`
(van der Corput) refinement of Minkowski's convex-body theorem is derived.

Unlike the parent entry's `blichfeldt_statement` (which is really *van der Corput*:
convexity, symmetry, and a `2ⁿ` factor produce `k + 1` *lattice points* of a
convex body), the statement here is the true Blichfeldt theorem: an arbitrary
bounded measurable set and no `2ⁿ` factor, producing points of `s` congruent mod
`L`.

## Proof

A measure-theoretic pigeonhole ("multiplicity averaging"):

* The covering-count `g z = ∑' l, 𝟙_{l +ᵥ s}(z)` integrates over the fundamental
  domain to `μ s` (Tonelli + translation of the fundamental domain).
* If `g z ≤ k` everywhere, then `μ s = ∫_F g ≤ k · μ F`, contradicting the
  hypothesis.  Hence some `z` is covered more than `k` times.
* Extracting a finite over-covered subfamily gives `T` with `k < #T` and
  `z ∈ l +ᵥ s` for all `l ∈ T`.

The `k = 1` case recovers `exists_pair_mem_lattice_not_disjoint_vadd`.
-/
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

open MeasureTheory ENNReal Set Filter
open scoped Pointwise ENNReal

namespace Blichfeldt

/-!
### Finite extraction from an over-large `tsum`

If a `[0,1]`-valued family sums (as a `tsum` in `ℝ≥0∞`) to something exceeding a
natural number `k`, then more than `k` of its terms are nonzero.  This is the
combinatorial core of the pigeonhole.
-/

/-- If each `f i ≤ 1` and `k < ∑' i, f i` in `ℝ≥0∞`, there is a finite set `T`
with more than `k` elements on each of which `f` is nonzero. -/
theorem exists_finset_card_lt_of_lt_tsum {ι : Type*} [Countable ι] {f : ι → ℝ≥0∞}
    (hf : ∀ i, f i ≤ 1) {k : ℕ} (h : (k : ℝ≥0∞) < ∑' i, f i) :
    ∃ T : Finset ι, k < T.card ∧ ∀ i ∈ T, f i ≠ 0 := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum] at h
  obtain ⟨u, hu⟩ := lt_iSup_iff.mp h
  refine ⟨u.filter (fun i => f i ≠ 0), ?_, ?_⟩
  · -- `k < #(filtered set)`
    have hsum : ∑ i ∈ u.filter (fun i => f i ≠ 0), f i = ∑ i ∈ u, f i :=
      Finset.sum_filter_of_ne (fun x _ hx => hx)
    have hcard : ∑ i ∈ u.filter (fun i => f i ≠ 0), f i
        ≤ (u.filter (fun i => f i ≠ 0)).card := by
      calc ∑ i ∈ u.filter (fun i => f i ≠ 0), f i
          ≤ ∑ _i ∈ u.filter (fun i => f i ≠ 0), (1 : ℝ≥0∞) :=
            Finset.sum_le_sum (fun i _ => hf i)
        _ = (u.filter (fun i => f i ≠ 0)).card := by simp
    have : (k : ℝ≥0∞) < ((u.filter (fun i => f i ≠ 0)).card : ℝ≥0∞) :=
      lt_of_lt_of_le (hsum ▸ hu) hcard
    exact_mod_cast this
  · intro i hi
    exact (Finset.mem_filter.mp hi).2

end Blichfeldt

namespace MeasureTheory

variable {E L : Type*} [MeasurableSpace E] {μ : Measure E} {F s : Set E}

/-- **Blichfeldt's Theorem (general multiplicity).**  If the volume of `s`
exceeds `k` times the covolume `μ F` of the countable subgroup `L`, then there is
a point `z` covered by more than `k` translates of `s` by `L`: a finite set
`T ⊆ L` with `k < #T` and `z ∈ l +ᵥ s` for every `l ∈ T`.

Equivalently, the `#T` points `{z} - T ⊆ s` are pairwise congruent modulo `L`.

At `k = 1` this specializes to
`exists_pair_mem_lattice_not_disjoint_vadd`. -/
theorem exists_finset_lattice_common_vadd [AddGroup L] [Countable L] [AddAction L E]
    [MeasurableSpace L] [MeasurableVAdd L E] [VAddInvariantMeasure L E μ]
    (fund : IsAddFundamentalDomain L F μ) (hs : NullMeasurableSet s μ) {k : ℕ}
    (h : k • μ F < μ s) :
    ∃ T : Finset L, k < T.card ∧ ∃ z, ∀ l ∈ T, z ∈ (l +ᵥ s) := by
  classical
  -- Each translate of `s` is null-measurable (invariance of `μ`).
  have hnull : ∀ l : L, NullMeasurableSet (l +ᵥ s) μ := fun l => hs.vadd l
  have hnullr : ∀ l : L, NullMeasurableSet (l +ᵥ s) (μ.restrict F) := fun l =>
    (hnull l).mono_ac Measure.restrict_le_self.absolutelyContinuous
  -- Key averaging identity: the covering count integrates over `F` to `μ s`.
  have key : ∫⁻ z in F, (∑' l : L, (l +ᵥ s).indicator (1 : E → ℝ≥0∞) z) ∂μ = μ s := by
    rw [lintegral_tsum (f := fun (l : L) (z : E) => (l +ᵥ s).indicator (1 : E → ℝ≥0∞) z)
      (fun l => (aemeasurable_indicator_iff₀ (hnullr l)).mpr aemeasurable_const),
      fund.measure_eq_tsum s]
    refine tsum_congr (fun l => ?_)
    rw [lintegral_indicator_one₀ (hnullr l), Measure.restrict_apply₀' fund.nullMeasurableSet]
  -- Pigeonhole: some point is covered more than `k` times.
  have hz : ∃ z, (k : ℝ≥0∞) < ∑' l : L, (l +ᵥ s).indicator (1 : E → ℝ≥0∞) z := by
    by_contra hall
    push_neg at hall
    have hle : ∫⁻ z in F, (∑' l : L, (l +ᵥ s).indicator (1 : E → ℝ≥0∞) z) ∂μ
        ≤ ∫⁻ _ in F, (k : ℝ≥0∞) ∂μ := lintegral_mono hall
    rw [key, setLIntegral_const] at hle
    rw [nsmul_eq_mul] at h
    exact absurd (lt_of_lt_of_le h hle) (lt_irrefl _)
  obtain ⟨z, hz⟩ := hz
  -- Extract a finite over-covered subfamily.
  have hbound : ∀ l : L, (l +ᵥ s).indicator (1 : E → ℝ≥0∞) z ≤ 1 := by
    intro l; rw [Set.indicator_apply]; split <;> simp
  obtain ⟨T, hcard, hne⟩ :=
    Blichfeldt.exists_finset_card_lt_of_lt_tsum hbound hz
  refine ⟨T, hcard, z, fun l hl => ?_⟩
  exact (Set.indicator_apply_ne_zero.mp (hne l hl)).1

end MeasureTheory
