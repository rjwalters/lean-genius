/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib
import Proofs.SpernerNDimMathlibOQ02

/-!
# Concrete Cases of sperner_panchromatic

This file proves `sperner_panchromatic` for n=0 and n=1, and documents
why the constant-miss FreudCell approach fails for n≥2.

## Proved Results

- `sperner_panchromatic_zero`: n=0 (Δ⁰ is a single point, trivial)
- `sperner_panchromatic_one`: n=1 (Δ¹ is an interval, via discrete IVT)

## Why FreudCell Is Wrong (Sessions 1-8 Failure Analysis)

Sessions 1-8 built a "constant-miss FreudCell" triangulation: simplex (b, σ)
where σ(n) is a fixed "miss direction" that decreases uniformly at each step.

This is FUNDAMENTALLY WRONG. For n=2, N=2 the 6 FreudCell cells all have
the pattern {corner, midpoint, midpoint} — they triangulate an ANNULUS, not Δ².

Concretely (corners A=(2,0,0), B=(0,2,0), C=(0,0,2), midpoints D=(1,1,0),
E=(1,0,1), F=(0,1,1)):
- FreudCell gives 6 cells: ADF, AEF, BDE, BFE, CED, CFD
- The centroid (2/3,2/3,2/3) lies in BOTH triangle ADF AND triangle BDE
  (verified: (1/3)A + 0·D + (2/3)F = centroid ✓, and (1/3)B + 0·D + (2/3)E = centroid ✓)
- Center triangle DEF is entirely MISSING
- Euler characteristic: V(6) - E(12) + F(6) = 0 ≠ 1 (annulus, not disk)

The standard N=2 Sperner triangulation has N²=4 triangles:
  ADE, BDF, CEF, DEF — with the inverted center triangle DEF.
None of these appear in FreudCell for n=2, N=2.

## Correct Approach for n≥2

Use `AbstractSimplicialData` from `SpernerSimplicialInstance.lean` (all
proved, 0 sorries) with the CORRECT standard Sperner triangulation.
Missing piece: define correct `topSimplices` and prove `pseudomanifold`.
Estimated: 300-400 additional lines.

## Tags

Brouwer, Sperner, simplex, parity, discrete IVT, fixed point
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace SpernerBrouwer

open Finset BigOperators

-- ============================================================
-- SECTION I: n=0 case (trivial)
-- ============================================================

/-- `sperner_panchromatic` for n=0: Δ⁰ is a single point.
    The unique point (1,) serves as all witnesses; diameter bound is 0/N = 0. -/
theorem sperner_panchromatic_zero (N : ℕ) (hN : 0 < N)
    (f : (Fin 1 → ℝ) → Fin 1 → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin 1 → Fin 1 → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin 1, f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin 1) (l : Fin 1), |v i l - v j l| ≤ (0 : ℝ) / N) := by
  have hfpt : InSimplex (f (fun _ => 1)) :=
    hf_map _ ⟨fun _ => le_refl _, by simp [Fin.sum_univ_one]⟩
  refine ⟨fun _ _ => 1,
          fun _ => ⟨fun _ => le_refl _, by simp [Fin.sum_univ_one]⟩,
          fun i => ?_, fun i j l => ?_⟩
  · -- f(pt) 0 ≤ pt 0 = 1: InSimplex forces f(pt) 0 = 1
    fin_cases i
    have hfsum : f (fun _ => (1 : ℝ)) 0 = 1 := by
      have := hfpt.2; simp [Fin.sum_univ_one] at this; exact this
    simp [hfsum]
  · -- Diameter 0/N = 0 ≤ |1-1| = 0
    fin_cases i <;> fin_cases j <;> fin_cases l <;> simp

-- ============================================================
-- SECTION II: n=1 case (discrete IVT)
-- ============================================================

/-- `sperner_panchromatic` for n=1: proved via discrete IVT on the grid of Δ¹.

**Proof sketch**: The N-th grid triangulation of Δ¹ has vertices
  g(k) = (k/N, (N-k)/N) for k = 0,...,N.
The Sperner coloring assigns color 0 (resp. 1) to g(k) when f(g(k))₀ ≤ k/N
(resp. f(g(k))₁ ≤ (N-k)/N) is the "first" satisfied inequality.
Since supp(g(0)) = {1}, we get c(0) = 1. Since supp(g(N)) = {0}, we get c(N) = 0.
Let K = last index with c(K) = 1. Then c(K+1) = 0. The pair (g(K+1), g(K))
is panchromatic with diameter 1/N = n/N. -/
theorem sperner_panchromatic_one (N : ℕ) (hN : 0 < N)
    (f : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin 2 → Fin 2 → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin 2, f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin 2) (l : Fin 2), |v i l - v j l| ≤ (1 : ℝ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  have hNrpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  -- Grid points on Δ¹: g k = (k/N, (N-k)/N)
  let g : Fin (N + 1) → Fin 2 → ℝ := fun k i =>
    if i.val = 0 then (k.val : ℝ) / N else ((N - k.val : ℕ) : ℝ) / N
  -- g k is in the 1-simplex Δ¹
  have hg : ∀ k : Fin (N + 1), InSimplex (g k) := fun k => by
    have hkle : k.val ≤ N := Nat.lt_succ_iff.mp k.isLt
    constructor
    · intro i; simp only [g]; split_ifs <;>
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · simp only [g, Fin.sum_univ_two,
                 show (0 : Fin 2).val = 0 from rfl, if_true,
                 show (1 : Fin 2).val = 1 from rfl,
                 show ¬(1 : Nat) = 0 from by omega, if_false]
      rw [div_add_div_same, div_self hNr]; push_cast; omega
  have hfg : ∀ k : Fin (N + 1), InSimplex (f (g k)) := fun k => hf_map _ (hg k)
  -- Sperner coloring on the grid
  let c : Fin (N + 1) → Fin 2 := fun k =>
    spernerColor (g k) (f (g k)) (hg k) (hfg k)
  -- c(0) = 1: g(0)₀ = 0/N = 0, so spernerColor ≠ 0, so = 1
  have hc0 : c ⟨0, Nat.succ_pos N⟩ = 1 := by
    have hg0 : g ⟨0, Nat.succ_pos N⟩ (0 : Fin 2) = 0 := by
      simp [g, show (0 : Fin 2).val = 0 from rfl]
    have hne : c ⟨0, Nat.succ_pos N⟩ ≠ 0 :=
      spernerColor_ne_of_zero (hg _) (hfg _) hg0
    exact Fin.ext (by
      have : (c ⟨0, Nat.succ_pos N⟩).val ≠ 0 := fun h => hne (Fin.ext h)
      have := (c ⟨0, Nat.succ_pos N⟩).isLt; omega)
  -- c(N) = 0: g(N)₁ = 0/N = 0, so spernerColor ≠ 1, so = 0
  have hcN : c ⟨N, Nat.lt_succ_self N⟩ = 0 := by
    have hgN : g ⟨N, Nat.lt_succ_self N⟩ (1 : Fin 2) = 0 := by
      simp [g, show (1 : Fin 2).val = 1 from rfl,
            show ¬(1 : Nat) = 0 from by omega, Nat.sub_self]
    have hne : c ⟨N, Nat.lt_succ_self N⟩ ≠ 1 :=
      spernerColor_ne_of_zero (hg _) (hfg _) hgN
    exact Fin.ext (by
      have : (c ⟨N, Nat.lt_succ_self N⟩).val ≠ 1 := fun h => hne (Fin.ext h)
      have := (c ⟨N, Nat.lt_succ_self N⟩).isLt; omega)
  -- Find K = last grid point with color 1 (discrete IVT: c goes 1...1,0...0)
  let S : Finset (Fin (N + 1)) := univ.filter (fun k => c k = 1)
  have hS_ne : S.Nonempty :=
    ⟨⟨0, Nat.succ_pos N⟩, mem_filter.mpr ⟨mem_univ _, hc0⟩⟩
  let K : Fin (N + 1) := S.max' hS_ne
  have hcK : c K = 1 := (mem_filter.mp (S.max'_mem hS_ne)).2
  -- K < N: if K = N then c(K) = c(N) = 0 contradicts c(K) = 1
  have hK_lt_N : K.val < N := by
    by_contra h; push_neg at h
    have hKN : K = ⟨N, Nat.lt_succ_self N⟩ :=
      Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp K.isLt) h)
    rw [hKN] at hcK
    exact absurd hcK (hcN ▸ by decide)
  -- K+1 is a valid grid index, and c(K+1) = 0
  let K1 : Fin (N + 1) := ⟨K.val + 1, by omega⟩
  have hcK1 : c K1 = 0 := by
    -- K+1 ∉ S since K is the max
    have hK1_not_S : K1 ∉ S := fun hmem =>
      absurd (Finset.le_max' S K1 hmem) (by simp [K1, Fin.le_iff_val_le_val]; omega)
    exact Fin.ext (by
      have : (c K1).val ≠ 1 :=
        fun h => hK1_not_S (mem_filter.mpr ⟨mem_univ _, Fin.ext h⟩)
      have := (c K1).isLt; omega)
  -- Extract color inequalities: c K = 1 → f(gK)₁ ≤ gK₁; c K1 = 0 → f(gK1)₀ ≤ gK1₀
  have hle_K : f (g K) (1 : Fin 2) ≤ g K (1 : Fin 2) := by
    have h := spernerColor_le (hg K) (hfg K)
    -- spernerColor (g K) ... = c K (definitional) and c K = 1
    rw [show spernerColor (g K) (f (g K)) (hg K) (hfg K) = c K from rfl, hcK] at h
    exact h
  have hle_K1 : f (g K1) (0 : Fin 2) ≤ g K1 (0 : Fin 2) := by
    have h := spernerColor_le (hg K1) (hfg K1)
    rw [show spernerColor (g K1) (f (g K1)) (hg K1) (hfg K1) = c K1 from rfl, hcK1] at h
    exact h
  -- Key grid difference: consecutive vertices differ by 1/N in each coordinate
  have hg0_diff : g K1 (0 : Fin 2) - g K (0 : Fin 2) = 1 / N := by
    simp only [g, K1, show (0 : Fin 2).val = 0 from rfl, if_true]
    push_cast; field_simp; ring
  have hg1_diff : g K (1 : Fin 2) - g K1 (1 : Fin 2) = 1 / N := by
    simp only [g, K1, show (1 : Fin 2).val = 1 from rfl,
               show ¬(1 : Nat) = 0 from by omega, if_false]
    have h1 : ((N - K.val : ℕ) : ℝ) = (N : ℝ) - K.val := by push_cast; omega
    have h2 : ((N - (K.val + 1) : ℕ) : ℝ) = (N : ℝ) - K.val - 1 := by push_cast; omega
    rw [h1, h2]; field_simp; ring
  -- Diameter bounds for all cases
  have habs_pos : (0 : ℝ) < 1 / N := by positivity
  have hdiam : ∀ (l : Fin 2), |g K1 l - g K l| ≤ 1 / N := by
    intro l; fin_cases l
    · rw [hg0_diff, abs_of_pos habs_pos]
    · have : g K1 (1 : Fin 2) - g K (1 : Fin 2) = -(1 / N) := by linarith [hg1_diff]
      rw [this, abs_neg, abs_of_pos habs_pos]
  -- Construct witnesses: v 0 = g K1 (color 0), v 1 = g K (color 1)
  refine ⟨fun i => if i.val = 0 then g K1 else g K, ?_, ?_, ?_⟩
  · -- InSimplex for each witness
    intro i; fin_cases i <;> simp [hg]
  · -- Color conditions
    intro i; fin_cases i
    · simpa using hle_K1
    · simpa using hle_K
  · -- Diameter: |v i l - v j l| ≤ 1/N
    intro i j l
    fin_cases i <;> fin_cases j <;>
      simp only [show (0 : Fin 2).val = 0 from rfl, if_true,
                 show (1 : Fin 2).val = 1 from rfl,
                 show ¬(1 : Nat) = 0 from by omega, if_false]
    -- i = j = 0: same vector, difference is 0
    · simp [div_nonneg (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hNrpos)]
    -- i = 0, j = 1: |g K1 l - g K l| ≤ 1/N
    · exact hdiam l
    -- i = 1, j = 0: |g K l - g K1 l| = |g K1 l - g K l| ≤ 1/N
    · rw [abs_sub_comm]; exact hdiam l
    -- i = j = 1: same vector, difference is 0
    · simp [div_nonneg (by norm_num : (0:ℝ) ≤ 1) (le_of_lt hNrpos)]

-- ============================================================
-- SECTION III: Path forward for n≥2
-- ============================================================

/-!
### What Remains for General n

For n≥2, `sperner_panchromatic` requires a correct n-dimensional
triangulation of N·Δⁿ. The correct standard Sperner triangulation
has N^n simplices (e.g., N² for n=2, including the inverted center triangle).

Implementation path via `AbstractSimplicialData` (SpernerSimplicialInstance.lean):
1. Define `topSimplices` as the correct set of n-simplices
2. Prove `card_eq` (n+1 vertices per simplex)
3. Prove `pseudomanifold` (≤2 containers per codim-1 face)
4. `AbstractSimplicialData.toTriangulation` gives full CellComplex automatically
5. Prove `boundary_doors_odd` by induction (using the bijection with (n-1)-dim case)
6. Apply `Triangulation.sperner` + real coordinate extraction
-/

end SpernerBrouwer
