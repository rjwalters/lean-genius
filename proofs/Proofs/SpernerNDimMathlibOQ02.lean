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
each subdivision yields a *panchromatic* simplex — `n+1` vertices `v₀, ..., vₙ`,
one per color, each satisfying `f(vᵢ)ᵢ ≤ (vᵢ)ᵢ`, with all vertices within
diameter `(n+1)/(N+1)` of each other.

**Step 3 (proved here)**: By compactness of `Δⁿ`, the first vertices of the
sequence of panchromatic tuples have a convergent subsequence with limit `x*`.
The diameter bound forces every vertex of the same tuple to converge to the
same limit. The per-color inequalities pass to the limit by continuity:
`f(x*)ᵢ ≤ x*ᵢ` for all `i`. Summing and using `Σ f(x*)ᵢ = 1 = Σ x*ᵢ`, all
inequalities must be equalities, giving `f(x*) = x*`.

## Why panchromatic, not single near-fixed-point

A "near-fixed-point" formulation `∃ x, ∀ i, |f(x)ᵢ - xᵢ| ≤ ε` would require
**Lipschitz continuity** of `f` to derive: extracting a per-coordinate bound
at a single `x` from a fully-colored simplex requires comparing `f(x)` to
`f(vᵢ)` for each color-`i` vertex `vᵢ`, which costs a Lipschitz factor. The
panchromatic formulation gives the *raw* Sperner output: one inequality per
distinct vertex, with a diameter bound. Continuity alone (no Lipschitz)
suffices to derive the fixed point.

## Axiom justification (1 remaining)

`sperner_panchromatic`: Follows from (a) the Nth grid triangulation of `Δⁿ`
  (vertices `{(a₀/N,...,aₙ/N) : Σaᵢ=N, aᵢ ∈ ℕ}`, simplices from ordered chains),
  (b) the proved Sperner boundary condition `spernerColor_ne_of_zero` /
  `spernerColorMap_boundary`, and (c) abstract Sperner's lemma
  (`SpernerAbstract.sperner` in SpernerNDimMathlib.lean).
  The output is `n+1` distinct grid vertices of the panchromatic top-simplex,
  one per color, with the color-`i` inequality at vertex `i` and diameter
  bounded by the grid mesh `(n+1)/(N+1)`.

## Main results

* `SpernerBrouwer.supp_nonempty`: support of any `Δⁿ` point is nonempty
* `SpernerBrouwer.exists_le_of_simplex_map`: key coloring well-definedness lemma
* `SpernerBrouwer.colorSet_nonempty`: the Sperner candidate set is nonempty
* `SpernerBrouwer.spernerColor_in_supp`: color lies in support (Sperner condition)
* `SpernerBrouwer.spernerColor_le`: the coloring index satisfies `f(v)ᵢ ≤ vᵢ`
* `SpernerBrouwer.spernerColor_ne_of_zero`: face boundary condition
* `SpernerBrouwer.sperner_panchromatic`: panchromatic tuple from grid Sperner (axiom)
* `SpernerBrouwer.brouwer_from_panchromatic`: fixed point from panchromatic tuples (proved)
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
-- SECTION IV: From Sperner to Brouwer (via panchromatic tuples)
-- ============================================================

/-- **Axiom (Grid Sperner → Panchromatic Tuple)**: For each `N`, the Nth grid
    triangulation of `Δⁿ` with the Sperner coloring derived from `f` yields a
    *panchromatic simplex*: `n+1` vertices in `Δⁿ`, one per color, each
    satisfying its color-`i` inequality `f(vᵢ)ᵢ ≤ (vᵢ)ᵢ`, and all within
    pairwise coordinate gap `(n+1)/(N+1)`.

    **Justification**: Partition `Δⁿ` into small simplices with vertices
      `{(a₀/N,...,aₙ/N) : aᵢ ∈ ℕ, Σaᵢ = N}` (the Nth grid triangulation).
    Apply the Sperner coloring `c(v) = spernerColorMap f hf_map v hv`.
    By `spernerColorMap_boundary`, this satisfies the Sperner boundary condition.
    By abstract Sperner's lemma (`SpernerAbstract.sperner` in SpernerNDimMathlib.lean),
    a fully-colored (panchromatic) simplex exists. Two grid vertices share a
    grid simplex of edge length `1/N`, so each pairwise coordinate gap is
    bounded by `1/N ≤ (n+1)/(N+1)` (loose bound used here for convenience).

    **Why panchromatic, not single-point**: extracting per-coordinate bounds
    `|f(x)ᵢ - xᵢ| ≤ ε` at a single `x` from a fully-colored simplex requires
    Lipschitz continuity (to relate `f` at different vertices to `f` at one
    point). The panchromatic formulation provides the *raw* Sperner output:
    one one-sided inequality per vertex. The diameter bound + continuity is
    enough to derive a fixed point without Lipschitz. -/
axiom sperner_panchromatic (n N : ℕ)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i, InSimplex (v i)) ∧
      (∀ i : Fin (n + 1), f (v i) i ≤ v i i) ∧
      (∀ (i j : Fin (n + 1)) (l : Fin (n + 1)),
          |v i l - v j l| ≤ (n + 1 : ℝ) / ((N : ℝ) + 1))

/-- **Theorem (Panchromatic → Fixed Point)**: Given a sequence of panchromatic
    tuples whose pairwise diameter shrinks to 0, there exists a fixed point of `f`.

    **Proof**: The simplex `Δⁿ` is compact. Take the first vertex of each
    panchromatic tuple to form a sequence in `Δⁿ`; extract a convergent
    subsequence `v_{φ(k)}⁰ → x*` (sequential compactness). By the diameter
    bound, every other vertex `v_{φ(k)}ⁱ` of the same tuple converges to the
    same limit `x*`. By continuity, `f(v_{φ(k)}ⁱ) → f(x*)`. The Sperner
    inequality `f(v_{φ(k)}ⁱ)ᵢ ≤ (v_{φ(k)}ⁱ)ᵢ` passes to the limit:
    `f(x*)ᵢ ≤ x*ᵢ` for all `i`. Summing over `i`: `Σ f(x*)ᵢ ≤ Σ x*ᵢ`. But
    both sums equal `1` (since `f(x*), x* ∈ Δⁿ`), so all inequalities are
    equalities, i.e., `f(x*) = x*`. -/
theorem brouwer_from_panchromatic {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_cont : Continuous f)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v))
    (happrox : ∀ N : ℕ, ∃ v : Fin (n + 1) → Fin (n + 1) → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin (n + 1), f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin (n + 1)) (l : Fin (n + 1)),
            |v i l - v j l| ≤ (n + 1 : ℝ) / ((N : ℝ) + 1))) :
    ∃ x : Fin (n + 1) → ℝ, InSimplex x ∧ f x = x := by
  -- Step 1: The simplex Δⁿ is compact (closed subset of [0,1]^(n+1))
  have hS_compact : IsCompact {v : Fin (n + 1) → ℝ | InSimplex v} := by
    apply IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => isCompact_Icc))
    · have heq : {v : Fin (n + 1) → ℝ | InSimplex v} =
          (⋂ i, {v | (0 : ℝ) ≤ v i}) ∩ {v | ∑ i : Fin (n + 1), v i = 1} := by
        ext v; simp [InSimplex, Set.mem_iInter]
      rw [heq]
      exact (isClosed_iInter fun i =>
        isClosed_le continuous_const (continuous_apply i)).inter
        (isClosed_eq (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const)
    · intro v ⟨hnn, hsum⟩
      simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
      exact fun i => ⟨hnn i,
        (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)).trans hsum.le⟩
  -- Step 2: Choose a panchromatic tuple for each N
  let u : ℕ → Fin (n + 1) → Fin (n + 1) → ℝ := fun N => (happrox N).choose
  have hu_mem : ∀ N i, InSimplex (u N i) := fun N i => (happrox N).choose_spec.1 i
  have hu_color : ∀ N i, f (u N i) i ≤ u N i i :=
    fun N i => (happrox N).choose_spec.2.1 i
  have hu_diam : ∀ N i j l,
      |u N i l - u N j l| ≤ (n + 1 : ℝ) / ((N : ℝ) + 1) :=
    fun N i j l => (happrox N).choose_spec.2.2 i j l
  -- Step 3: First vertices live in compact Δⁿ — extract convergent subsequence
  let v0 : ℕ → Fin (n + 1) → ℝ := fun N => u N 0
  have hv0_mem : ∀ N, v0 N ∈ {v : Fin (n + 1) → ℝ | InSimplex v} :=
    fun N => hu_mem N 0
  obtain ⟨x, hx_mem, φ, hφ_mono, hφ_conv⟩ := hS_compact.tendsto_subseq hv0_mem
  refine ⟨x, hx_mem, ?_⟩
  -- Step 4: (n+1)/(φk+1) → 0 since φ is strictly monotone (so φk ≥ k → ∞)
  have h_phi_atTop : Filter.Tendsto (fun k : ℕ => (φ k : ℝ) + 1)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    exact ⟨⌈b⌉₊, fun k hk => by
      have hkphi : (k : ℝ) ≤ φ k := by exact_mod_cast hφ_mono.id_le k
      linarith [Nat.le_ceil b, show (⌈b⌉₊ : ℝ) ≤ k from by exact_mod_cast hk]⟩
  have h_bound_zero : Filter.Tendsto (fun k => (n + 1 : ℝ) / ((φ k : ℝ) + 1))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h_phi_atTop
  -- Step 5: For each i, u(φk) i → x via diameter bound applied to v0(φk) → x
  have hu_conv : ∀ i,
      Filter.Tendsto (fun k => u (φ k) i) Filter.atTop (nhds x) := by
    intro i
    have h_diff : Filter.Tendsto (fun k => u (φ k) i - u (φ k) 0)
        Filter.atTop (nhds 0) := by
      rw [tendsto_pi_nhds]
      intro l
      simp only [Pi.sub_apply, Pi.zero_apply]
      exact squeeze_zero_norm
        (fun k => by rw [Real.norm_eq_abs]; exact hu_diam (φ k) i 0 l)
        h_bound_zero
    have hsum := hφ_conv.add h_diff
    rw [add_zero] at hsum
    exact hsum.congr (fun k => by
      funext l
      simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply, v0]
      ring)
  -- Step 6: For each i, f(u(φk) i) i ≤ u(φk) i i, pass to limit ⇒ f(x) i ≤ x i
  have hf_le : ∀ i, f x i ≤ x i := by
    intro i
    have h_apply_i : Continuous (fun y : Fin (n + 1) → ℝ => y i) := continuous_apply i
    have hf_apply : Continuous (fun y : Fin (n + 1) → ℝ => f y i) :=
      h_apply_i.comp hf_cont
    have hfconv : Filter.Tendsto (fun k => f (u (φ k) i) i)
        Filter.atTop (nhds (f x i)) :=
      (hf_apply.tendsto x).comp (hu_conv i)
    have hxconv : Filter.Tendsto (fun k => u (φ k) i i)
        Filter.atTop (nhds (x i)) :=
      (h_apply_i.tendsto x).comp (hu_conv i)
    exact le_of_tendsto_of_tendsto' hfconv hxconv (fun k => hu_color (φ k) i)
  -- Step 7: Σ f(x) i ≤ Σ x i, both sums equal 1, so all inequalities are equalities
  have hfx_mem : InSimplex (f x) := hf_map x hx_mem
  have hsum_eq : ∑ i, f x i = ∑ i, x i := by rw [hfx_mem.2, hx_mem.2]
  funext i
  by_contra hne
  have hlt : f x i < x i := lt_of_le_of_ne (hf_le i) hne
  have : ∑ j, f x j < ∑ j, x j :=
    Finset.sum_lt_sum (fun j _ => hf_le j) ⟨i, Finset.mem_univ i, hlt⟩
  rw [hsum_eq] at this
  exact lt_irrefl _ this

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
  brouwer_from_panchromatic f hf_cont hf_map
    (fun N => sperner_panchromatic n N f hf_map)

end SpernerBrouwer
