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
each subdivision has a panchromatic simplex: vertices v₀,...,vₙ ∈ Δⁿ with
f(vᵢ)ᵢ ≤ (vᵢ)ᵢ for each i (color-i property) and all vertices within n/N of each other.

**Step 3 (proved here)**: Let u_N = v₀,N (first vertex from each panchromatic tuple).
By compactness of Δⁿ, some subsequence u_{φk} → x*. Since diameter n/φk → 0,
all vertices v_{i,φk} → x*. By continuity, f(v_{i,φk})ᵢ → f(x*)ᵢ and v_{i,φk}ᵢ → x*ᵢ.
From f(v_{i,φk})ᵢ ≤ v_{i,φk}ᵢ we get f(x*)ᵢ ≤ x*ᵢ for all i.
Since Σᵢ f(x*)ᵢ = 1 = Σᵢ x*ᵢ, all inequalities are equalities: f(x*) = x*.

## Axiom justification (1 remaining)

`sperner_panchromatic`: For each N > 0, the Nth grid triangulation of `Δⁿ` with the
  Sperner coloring derived from `f` has a panchromatic (n+1)-tuple: vertices v₀,...,vₙ ∈ Δⁿ
  satisfying f(vᵢ)ᵢ ≤ (vᵢ)ᵢ (the defining property of Sperner color i) and diameter ≤ n/N.
  Proof structure: (a) Fixed-miss Freudenthal triangulation gives a valid CellComplex
  (adj_symm, adj_vertex, adj_ne: ~80 lines), (b) boundary door count is odd via induction
  on n (boundary_doors_odd: ~200 lines), (c) CellComplex.sperner gives the panchromatic
  simplex, (d) map grid vertices to real coordinates to extract the bound.

## Main results

* `SpernerBrouwer.supp_nonempty`: support of any `Δⁿ` point is nonempty
* `SpernerBrouwer.exists_le_of_simplex_map`: key coloring well-definedness lemma
* `SpernerBrouwer.colorSet_nonempty`: the Sperner candidate set is nonempty
* `SpernerBrouwer.spernerColor_in_supp`: color lies in support (Sperner condition)
* `SpernerBrouwer.spernerColor_le`: the coloring index satisfies `f(v)ᵢ ≤ vᵢ`
* `SpernerBrouwer.spernerColor_ne_of_zero`: face boundary condition
* `SpernerBrouwer.sperner_panchromatic`: panchromatic tuple from Sperner (axiom)
* `SpernerBrouwer.brouwer_from_panchromatic`: exact fixed point from panchromatic tuples
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
-- SECTION IV: From Sperner to Brouwer (via Panchromatic Tuples)
-- ============================================================

/-- **Axiom (Grid Sperner → Panchromatic Tuple)**: For each N > 0, the Nth Freudenthal
    grid triangulation of `Δⁿ` with the Sperner coloring yields a panchromatic (n+1)-tuple:
    vertices v₀,...,vₙ ∈ Δⁿ such that f(vᵢ)ᵢ ≤ (vᵢ)ᵢ and all vertices are within n/N.

    **Justification**: The Freudenthal triangulation (vertices `{(a₀/N,...,aₙ/N) : Σaᵢ=N}`
    with constant-miss step ordering) gives a CellComplex satisfying adj_symm, adj_vertex,
    adj_ne. The Sperner coloring `spernerColorMap` satisfies the boundary condition. By
    the parity of boundary doors (odd, proved by induction on n), CellComplex.sperner gives
    a panchromatic simplex. The n/N diameter bound follows from the grid mesh size.

    **Note**: `boundary_face` (the SpernerTriangulation axiom) is NOT needed here because
    we use CellComplex.sperner directly, which only requires the CellComplex axioms.
    The boundary door count oddness is proved separately as `boundary_doors_odd` by induction,
    using the bijection between boundary doors at face d and FC simplices of the (d-1) grid. -/
axiom sperner_panchromatic {n : ℕ} (N : ℕ) (hN : 0 < N)
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin (n + 1) → Fin (n + 1) → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin (n + 1), f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin (n + 1)) (l : Fin (n + 1)), |v i l - v j l| ≤ (n : ℝ) / N)

/-- **Theorem (Panchromatic Tuples → Fixed Point)**: Given panchromatic tuples with
    diameter → 0, there exists an exact fixed point.

    **Proof**: Let u_N = v_{N,0} (first component of N-th panchromatic tuple). By
    compactness of Δⁿ, some subsequence u_{φk} → x*. Since diameter n/(φk) → 0, all
    components v_{φk,i} → x* too. For each i: f(v_{φk,i})ᵢ ≤ v_{φk,i}ᵢ → f(x*)ᵢ ≤ x*ᵢ
    (by continuity). Since Σᵢ f(x*)ᵢ = 1 = Σᵢ x*ᵢ, all inequalities are equalities. -/
theorem brouwer_from_panchromatic {n : ℕ}
    (f : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ)
    (hf_cont : Continuous f)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v))
    (hpanch : ∀ N : ℕ, 0 < N → ∃ v : Fin (n + 1) → Fin (n + 1) → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin (n + 1), f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin (n + 1)) (l : Fin (n + 1)), |v i l - v j l| ≤ (n : ℝ) / N)) :
    ∃ x : Fin (n + 1) → ℝ, InSimplex x ∧ f x = x := by
  -- Step 1: The simplex Δⁿ is compact
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
  -- Step 2: For each N, extract panchromatic tuple data
  have hpanch' : ∀ N : ℕ, ∃ v : Fin (n + 1) → Fin (n + 1) → ℝ,
      (∀ i, InSimplex (v i)) ∧
      (∀ i : Fin (n + 1), f (v i) i ≤ v i i) ∧
      (∀ (i j : Fin (n + 1)) (l : Fin (n + 1)), |v i l - v j l| ≤ (n : ℝ) / (N + 1)) :=
    fun N => hpanch (N + 1) (Nat.succ_pos N)
  let vdata : ℕ → Fin (n + 1) → Fin (n + 1) → ℝ := fun N => (hpanch' N).choose
  have hvdata_mem : ∀ N i, InSimplex (vdata N i) := fun N => (hpanch' N).choose_spec.1
  have hvdata_le : ∀ N i, f (vdata N i) i ≤ vdata N i i :=
    fun N => (hpanch' N).choose_spec.2.1
  have hvdata_diam : ∀ N i j l, |vdata N i l - vdata N j l| ≤ (n : ℝ) / (N + 1) :=
    fun N => (hpanch' N).choose_spec.2.2
  -- Step 3: Use first component as main sequence; compactness → convergent subsequence
  let u : ℕ → Fin (n + 1) → ℝ := fun N => vdata N 0
  have hu_mem : ∀ N, u N ∈ {v : Fin (n + 1) → ℝ | InSimplex v} :=
    fun N => hvdata_mem N 0
  obtain ⟨x, hx_mem, φ, hφ_mono, hφ_conv⟩ := hS_compact.tendsto_subseq hu_mem
  refine ⟨x, hx_mem, ?_⟩
  -- Step 4: φk → ∞ (strictly monotone implies φk ≥ k → ∞)
  have h_phi_atTop : Filter.Tendsto (fun k : ℕ => (φ k : ℝ) + 1)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_atTop.mpr
    intro b
    exact ⟨⌈b⌉₊, fun k hk => by
      have hkphi : (k : ℝ) ≤ φ k := by exact_mod_cast hφ_mono.id_le k
      linarith [Nat.le_ceil b, show (⌈b⌉₊ : ℝ) ≤ k from by exact_mod_cast hk]⟩
  have h_diam_zero : Filter.Tendsto (fun k => (n : ℝ) / (φ k + 1))
      Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop h_phi_atTop
  -- Step 5: All components vdata(φk).i converge to x (by diameter → 0)
  have hconv_i : ∀ i : Fin (n + 1),
      Filter.Tendsto (fun k => vdata (φ k) i) Filter.atTop (nhds x) := by
    intro i
    rw [tendsto_pi_nhds]
    intro l
    -- |vdata(φk).i.l - x.l| ≤ n/(φk+1) + |vdata(φk).0.l - x.l| → 0
    have h_u_l_diff : Filter.Tendsto (fun k => vdata (φ k) 0 l - x l)
        Filter.atTop (nhds 0) := by
      have h := (tendsto_pi_nhds.mp hφ_conv l).sub tendsto_const_nhds
      simp only [sub_self] at h; exact h
    have h_u_l_abs : Filter.Tendsto (fun k => |vdata (φ k) 0 l - x l|)
        Filter.atTop (nhds 0) := by
      have := h_u_l_diff.norm
      simp only [norm_zero, Real.norm_eq_abs] at this
      exact this
    have h_diff : Filter.Tendsto (fun k => vdata (φ k) i l - x l)
        Filter.atTop (nhds 0) := by
      apply squeeze_zero_norm
      · intro k
        rw [Real.norm_eq_abs]
        calc |vdata (φ k) i l - x l|
            ≤ |vdata (φ k) i l - vdata (φ k) 0 l| + |vdata (φ k) 0 l - x l| :=
              abs_sub_triangle _ _
          _ ≤ n / (φ k + 1) + |vdata (φ k) 0 l - x l| := by
              gcongr; exact hvdata_diam (φ k) i 0 l
      · have := h_diam_zero.add h_u_l_abs
        rwa [add_zero] at this
    have := h_diff.add_const (x l)
    rw [zero_add] at this
    exact this.congr' (Filter.eventually_of_forall fun k => by ring)
  -- Step 6: f(x*)ᵢ ≤ x*ᵢ for each i (limit of inequalities f(vᵢ)ᵢ ≤ vᵢᵢ)
  have hfx_le : ∀ i : Fin (n + 1), f x i ≤ x i := by
    intro i
    have hfv_conv : Filter.Tendsto (fun k => f (vdata (φ k) i))
        Filter.atTop (nhds (f x)) :=
      (hf_cont.tendsto x).comp (hconv_i i)
    -- Limit of f(vᵢ)ᵢ ≤ vᵢᵢ: use ge_of_tendsto on x*ᵢ - f(x*)ᵢ ≥ 0
    have h_diff_conv : Filter.Tendsto (fun k => vdata (φ k) i i - f (vdata (φ k) i) i)
        Filter.atTop (nhds (x i - f x i)) :=
      (tendsto_pi_nhds.mp (hconv_i i) i).sub (tendsto_pi_nhds.mp hfv_conv i)
    have h_diff_nonneg : ∀ k, 0 ≤ vdata (φ k) i i - f (vdata (φ k) i) i :=
      fun k => sub_nonneg.mpr (hvdata_le (φ k) i)
    linarith [ge_of_tendsto h_diff_conv (Filter.eventually_of_forall h_diff_nonneg)]
  -- Step 7: Σᵢ f(x*)ᵢ = 1 = Σᵢ x*ᵢ with all f(x*)ᵢ ≤ x*ᵢ → f(x*) = x*
  funext i
  apply le_antisymm (hfx_le i)
  by_contra h
  push_neg at h
  have hS : InSimplex x := hx_mem
  have hfS : InSimplex (f x) := hf_map x hS
  have hlt : ∑ j : Fin (n + 1), f x j < ∑ j : Fin (n + 1), x j :=
    Finset.sum_lt_sum (fun j _ => hfx_le j) ⟨i, Finset.mem_univ _, h⟩
  linarith [hS.2, hfS.2]

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
    (fun N hN => sperner_panchromatic N hN f hf_map)

end SpernerBrouwer
