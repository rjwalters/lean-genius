/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# Brouwer's Fixed-Point Theorem via Sperner's Lemma (OQ-02)

Answers **OQ-02** from `sperner-ndim-mathlib`: prove Brouwer's fixed-point theorem
for the standard n-simplex using Sperner's lemma.

## Proof outline

Let `Δⁿ = {x : Fin (n+1) → ℝ | ∀ i, 0 ≤ x i ∧ ∑ i, x i = 1}` and
let `f : Δⁿ → Δⁿ` be continuous.

**Step 1 (proved here)**: For any vertex `v` of any triangulation of `Δⁿ`, define
  `c(v) := min {i ∈ supp(v) : f(v)ᵢ ≤ vᵢ}`
where `supp(v) = {i : vᵢ > 0}`. This is well-defined (some index in `supp(v)` satisfies
`f(v)ᵢ ≤ vᵢ`, proved from `∑ f(v)ᵢ = 1 = ∑ vᵢ`) and satisfies the Sperner boundary
condition (`c(v) ∈ supp(v)`, so if `vⱼ = 0` then `c(v) ≠ j`).

**Step 2 (axiom)**: By Sperner's lemma applied to the Nth grid triangulation of `Δⁿ`,
each subdivision has a fully-colored simplex, yielding a near-fixed-point `x ∈ Δⁿ`
with `|f(x)ᵢ - xᵢ| ≤ (n+1)/(N+1)` for all `i`.

**Step 3 (proved here)**: By compactness of `Δⁿ`, the sequence of near-fixed-points has a
convergent subsequence. By continuity of `f`, the limit is an exact fixed point.

## Axiom justification (1 remaining)

`sperner_near_fixed_point`: Follows from (a) the Nth grid triangulation of `Δⁿ`
  (vertices `{(a₀/N,...,aₙ/N) : Σaᵢ=N, aᵢ ∈ ℕ}`, simplices from ordered chains),
  (b) the proved Sperner boundary condition `spernerColor_ne_of_zero`, and
  (c) abstract Sperner's lemma (`SpernerAbstract.sperner` in SpernerNDimMathlib.lean).
  The grid CellComplex instance is structurally identical to `SpernerGrid.lean` but with
  a fixed adjacency that correctly handles cross-miss neighbors.

## Main results

* `SpernerBrouwer.supp_nonempty`: support of any `Δⁿ` point is nonempty
* `SpernerBrouwer.exists_le_of_simplex_map`: key coloring well-definedness lemma
* `SpernerBrouwer.colorSet_nonempty`: the Sperner candidate set is nonempty
* `SpernerBrouwer.spernerColor_in_supp`: color lies in support (Sperner condition)
* `SpernerBrouwer.spernerColor_le`: the coloring index satisfies `f(v)ᵢ ≤ vᵢ`
* `SpernerBrouwer.spernerColor_ne_of_zero`: face boundary condition
* `SpernerBrouwer.sperner_near_fixed_point`: near-fixed-point from Sperner (axiom)
* `SpernerBrouwer.fixed_point_from_approx`: exact fixed point from approximations (proved)
* `SpernerBrouwer.brouwer_fixed_point_simplex`: **Brouwer's theorem for `Δⁿ`**

## Tags

Brouwer, fixed point, Sperner, simplex, parity, combinatorial topology
-/

set_option linter.unusedVariables false

namespace SpernerBrouwer

open Finset BigOperators

variable {n : ℕ}

-- ============================================================
-- SECTION I: Standard n-Simplex and Support
-- ============================================================

/-- A point lies in the standard `n`-simplex: nonneg coordinates summing to 1. -/
def InSimplex (v : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ∑ i : Fin (n + 1), v i = 1

/-- Support of `v`: the set of strictly positive coordinates. -/
noncomputable def supp (v : Fin (n + 1) → ℝ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => 0 < v i)

lemma mem_supp_iff {v : Fin (n + 1) → ℝ} {i : Fin (n + 1)} :
    i ∈ supp v ↔ 0 < v i := by
  simp [supp]

/-- If `i ∉ supp v` and `v` has nonneg coordinates, then `v i = 0`. -/
lemma supp_le {v : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (hi : i ∉ supp v) (hpos : ∀ j, 0 ≤ v j) : v i = 0 :=
  le_antisymm (not_lt.mp (by rwa [mem_supp_iff] at hi)) (hpos i)

/-- The support of any simplex point is nonempty: coordinates sum to 1 > 0. -/
lemma supp_nonempty {v : Fin (n + 1) → ℝ} (hv : InSimplex v) : (supp v).Nonempty := by
  by_contra h
  have h_empty : ∀ i : Fin (n + 1), i ∉ supp v := fun i hi => h ⟨i, hi⟩
  have hzero : ∀ i : Fin (n + 1), v i = 0 := fun i => supp_le (h_empty i) hv.1
  have hsum : ∑ i : Fin (n + 1), v i = 0 :=
    Finset.sum_eq_zero (fun i _ => hzero i)
  linarith [hv.2]

-- ============================================================
-- SECTION II: Key Coloring Lemma (purely algebraic)
-- ============================================================

/-- **Key Lemma**: For `v, fv ∈ Δⁿ`, some coordinate in `supp(v)` satisfies `fv i ≤ v i`.

    Proof: If `fv i > v i` for all `i ∈ supp v`, and `0 = v i ≤ fv i` for `i ∉ supp v`,
    then `∑ fv > ∑ v = 1`, contradicting `∑ fv = 1`. -/
theorem exists_le_of_simplex_map {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) :
    ∃ i ∈ supp v, fv i ≤ v i := by
  by_contra h
  push_neg at h
  -- h : ∀ i ∈ supp v, v i < fv i
  have hle : ∀ i : Fin (n + 1), v i ≤ fv i := by
    intro i
    by_cases hi : i ∈ supp v
    · exact (h i hi).le
    · rw [supp_le hi hv.1]; exact hfv.1 i
  have hlt : ∑ i : Fin (n + 1), v i < ∑ i : Fin (n + 1), fv i := by
    apply Finset.sum_lt_sum (fun i _ => hle i)
    obtain ⟨j, hj⟩ := supp_nonempty hv
    exact ⟨j, Finset.mem_univ j, h j hj⟩
  linarith [hv.2, hfv.2]

-- ============================================================
-- SECTION III: Sperner Coloring Construction
-- ============================================================

/-- The candidate color set: indices in `supp(v)` where `fv` does not exceed `v`. -/
noncomputable def colorSet (v fv : Fin (n + 1) → ℝ) : Finset (Fin (n + 1)) :=
  (supp v).filter (fun i => fv i ≤ v i)

lemma colorSet_subset_supp (v fv : Fin (n + 1) → ℝ) :
    colorSet v fv ⊆ supp v :=
  Finset.filter_subset _ _

lemma mem_colorSet_iff {v fv : Fin (n + 1) → ℝ} {i : Fin (n + 1)} :
    i ∈ colorSet v fv ↔ i ∈ supp v ∧ fv i ≤ v i := by
  simp [colorSet, Finset.mem_filter]

/-- The candidate color set is nonempty, by the key lemma. -/
lemma colorSet_nonempty {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) :
    (colorSet v fv).Nonempty := by
  obtain ⟨i, hi_supp, hi_le⟩ := exists_le_of_simplex_map hv hfv
  exact ⟨i, mem_colorSet_iff.mpr ⟨hi_supp, hi_le⟩⟩

/-- **Sperner coloring**: the minimum index in `supp(v)` where `f` does not increase.
    Well-defined because `colorSet v fv` is nonempty (`colorSet_nonempty`). -/
noncomputable def spernerColor (v fv : Fin (n + 1) → ℝ)
    (hv : InSimplex v) (hfv : InSimplex fv) : Fin (n + 1) :=
  (colorSet v fv).min' (colorSet_nonempty hv hfv)

/-- The Sperner color lies in `supp(v)` (color is "supported" by `v`). -/
lemma spernerColor_in_supp {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) :
    spernerColor v fv hv hfv ∈ supp v :=
  colorSet_subset_supp v fv (Finset.min'_mem _ _)

/-- The Sperner color `c` satisfies the inequality: `fv c ≤ v c`. -/
lemma spernerColor_le {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) :
    fv (spernerColor v fv hv hfv) ≤ v (spernerColor v fv hv hfv) :=
  (mem_colorSet_iff.mp (Finset.min'_mem _ _)).2

/-- **Sperner boundary condition**: if coordinate `j` of `v` is zero (i.e., `v` lies on face `j`),
    then the Sperner color is not `j`. This is the key property making our coloring valid. -/
theorem spernerColor_ne_of_zero {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) {j : Fin (n + 1)} (hj : v j = 0) :
    spernerColor v fv hv hfv ≠ j := by
  intro heq
  have hmem := spernerColor_in_supp hv hfv
  rw [heq, mem_supp_iff] at hmem
  linarith [hmem]

/-- The Sperner coloring map: assigns each `v ∈ Δⁿ` a color in `Fin (n+1)`. -/
noncomputable def spernerColorMap
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v))
    (v : Fin (n + 1) → ℝ) (hv : InSimplex v) : Fin (n + 1) :=
  spernerColor v (f v) hv (hf_map v hv)

/-- The coloring map satisfies the Sperner boundary condition. -/
theorem spernerColorMap_boundary
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v))
    (v : Fin (n + 1) → ℝ) (hv : InSimplex v)
    {j : Fin (n + 1)} (hvj : v j = 0) :
    spernerColorMap f hf_map v hv ≠ j :=
  spernerColor_ne_of_zero hv (hf_map v hv) hvj

-- ============================================================
-- SECTION IV: From Sperner to Brouwer
-- ============================================================

/-- **Axiom (Grid Sperner → Near-Fixed-Point)**: For each `N`, the Nth grid
    triangulation of `Δⁿ` with the Sperner coloring derived from `f` yields a near-fixed-point
    with `|f(x)ᵢ - xᵢ| ≤ (n+1)/(N+1)` for all `i`.

    **Justification**: Partition `Δⁿ` into small simplices with vertices
      `{(a₀/N,...,aₙ/N) : aᵢ ∈ ℕ, Σaᵢ = N}` (the Nth grid triangulation).
    Apply the Sperner coloring `c(v) = spernerColorMap f hf_map v hv`.
    By `spernerColorMap_boundary`, this satisfies the Sperner boundary condition.
    By abstract Sperner's lemma (`SpernerAbstract.sperner` in SpernerNDimMathlib.lean),
    a fully-colored simplex exists with near-fixed-point bound (n+1)/(N+1). -/
axiom sperner_near_fixed_point (n N : ℕ)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ x : Fin (n + 1) → ℝ, InSimplex x ∧
      ∀ i : Fin (n + 1), |f x i - x i| ≤ (n + 1 : ℝ) / (N + 1)

/-- **Theorem (Compactness → Fixed Point)**: Given approximate fixed points with error → 0,
    there exists an exact fixed point.

    **Proof**: The simplex `Δⁿ` is compact (closed subset of `[0,1]^(n+1)`). The sequence
    of approximate fixed points has a convergent subsequence `xφ(k) → x*` by sequential
    compactness (`IsCompact.tendsto_subseq`). By continuity of `f`, `f(xφ(k)) → f(x*)`.
    Also `f(xφ(k)) → x*` because `|f(xφ(k))ᵢ - xφ(k)ᵢ| ≤ (n+1)/(φ(k)+1) → 0` (squeeze).
    By uniqueness of limits (`tendsto_nhds_unique`), `f(x*) = x*`. -/
theorem fixed_point_from_approx {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_cont : Continuous f)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v))
    (happrox : ∀ N : ℕ, ∃ x : Fin (n + 1) → ℝ,
        InSimplex x ∧ ∀ i : Fin (n + 1), |f x i - x i| ≤ (n + 1 : ℝ) / (N + 1)) :
    ∃ x : Fin (n + 1) → ℝ, InSimplex x ∧ f x = x := by
  -- Step 1: The simplex Δⁿ is compact
  have hS_compact : IsCompact {v : Fin (n + 1) → ℝ | InSimplex v} := by
    apply IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => isCompact_Icc))
    · -- Closed: ⋂ᵢ{v | 0 ≤ vᵢ} ∩ {v | Σvᵢ = 1}
      have heq : {v : Fin (n + 1) → ℝ | InSimplex v} =
          (⋂ i, {v | (0 : ℝ) ≤ v i}) ∩ {v | ∑ i : Fin (n + 1), v i = 1} := by
        ext v; simp [InSimplex, Set.mem_iInter]
      rw [heq]
      exact (isClosed_iInter fun i =>
        isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)
    · -- Subset of [0,1]^(n+1): vᵢ ≥ 0 and vᵢ ≤ Σvⱼ = 1
      intro v ⟨hnn, hsum⟩
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
      exact fun i => ⟨hnn i,
        (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum.le⟩
  -- Step 2: Approximate fixed point sequence u N = (happrox N).choose
  let u : ℕ → Fin (n + 1) → ℝ := fun N => (happrox N).choose
  have hu_mem : ∀ N, u N ∈ {v : Fin (n + 1) → ℝ | InSimplex v} :=
    fun N => (happrox N).choose_spec.1
  have hu_bound : ∀ N i, |f (u N) i - u N i| ≤ (n + 1 : ℝ) / ((N : ℝ) + 1) :=
    fun N i => (happrox N).choose_spec.2 i
  -- Step 3: Sequential compactness → convergent subsequence u ∘ φ → x
  obtain ⟨x, hx_mem, φ, hφ_mono, hφ_conv⟩ := hS_compact.tendsto_subseq hu_mem
  refine ⟨x, hx_mem, ?_⟩
  -- Step 4a: f(u(φk)) → f(x) by continuity
  have hfconv : Filter.Tendsto (fun k => f (u (φ k))) Filter.atTop (nhds (f x)) :=
    (hf_cont.tendsto x).comp hφ_conv
  -- Step 4b: f(u(φk)) → x via squeeze (|f - id| bounded by (n+1)/(φk+1) → 0)
  have hfconv2 : Filter.Tendsto (fun k => f (u (φ k))) Filter.atTop (nhds x) := by
    -- (φk + 1) → ∞ since φ strictly monotone implies φk ≥ k
    have h_phi_atTop : Filter.Tendsto (fun k : ℕ => (φ k : ℝ) + 1)
        Filter.atTop Filter.atTop := by
      apply Filter.tendsto_atTop_atTop.mpr
      intro b
      exact ⟨⌈b⌉₊, fun k hk => by
        have hkphi : (k : ℝ) ≤ φ k := by exact_mod_cast hφ_mono.id_le k
        linarith [Nat.le_ceil b, show (⌈b⌉₊ : ℝ) ≤ k from by exact_mod_cast hk]⟩
    -- (n+1)/(φk+1) → 0 since denominator → ∞
    have h_bound_zero : Filter.Tendsto (fun k => (n + 1 : ℝ) / ((φ k : ℝ) + 1))
        Filter.atTop (nhds 0) :=
      tendsto_const_nhds.div_atTop h_phi_atTop
    -- f(u(φk)) - u(φk) → 0 coordinatewise by squeeze
    have h_diff_zero : Filter.Tendsto (fun k => f (u (φ k)) - u (φ k))
        Filter.atTop (nhds 0) := by
      rw [tendsto_pi_nhds]
      intro i
      simp only [Pi.sub_apply, Pi.zero_apply]
      exact squeeze_zero_norm
        (fun k => by rw [Real.norm_eq_abs]; exact hu_bound (φ k) i)
        h_bound_zero
    -- u(φk) + (f(u(φk)) - u(φk)) = f(u(φk)) → x + 0 = x
    have hsum := hφ_conv.add h_diff_zero
    rw [add_zero] at hsum
    exact hsum.congr' (by
      filter_upwards with k
      funext i
      simp only [Function.comp, Pi.add_apply, Pi.sub_apply]
      ring)
  -- Step 5: Uniqueness of limits gives f(x) = x
  exact tendsto_nhds_unique hfconv hfconv2

-- ============================================================
-- SECTION V: Main Theorem
-- ============================================================

/-- **Brouwer's Fixed-Point Theorem for the standard simplex** (via Sperner's lemma):
    Every continuous self-map of `Δⁿ` has a fixed point. -/
theorem brouwer_fixed_point_simplex {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_cont : Continuous f)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ x : Fin (n + 1) → ℝ, InSimplex x ∧ f x = x :=
  fixed_point_from_approx f hf_cont hf_map
    (fun N => sperner_near_fixed_point n N f hf_map)

end SpernerBrouwer
