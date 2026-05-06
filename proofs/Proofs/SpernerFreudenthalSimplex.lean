/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

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
- Center triangle DEF is entirely MISSING
- Euler characteristic: V(6) - E(12) + F(6) = 0 ≠ 1 (annulus, not disk)

## Correct Approach for n≥2

Use `AbstractSimplicialData` from `SpernerSimplicialInstance.lean` (0 sorries)
with the CORRECT standard Sperner triangulation (N^n simplices).
Missing piece: define correct `topSimplices` and prove `pseudomanifold`.

## Tags

Brouwer, Sperner, simplex, parity, discrete IVT, fixed point
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace SpernerFreudSimp

open Finset BigOperators

-- ============================================================
-- Simplex definitions (self-contained, no import from OQ02)
-- ============================================================

variable {n : ℕ}

def InSimplex (v : Fin (n + 1) → ℝ) : Prop :=
  (∀ i, 0 ≤ v i) ∧ ∑ i : Fin (n + 1), v i = 1

noncomputable def supp (v : Fin (n + 1) → ℝ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => 0 < v i)

lemma mem_supp_iff {v : Fin (n + 1) → ℝ} {i : Fin (n + 1)} :
    i ∈ supp v ↔ 0 < v i := by simp [supp]

lemma supp_le {v : Fin (n + 1) → ℝ} {i : Fin (n + 1)}
    (hi : i ∉ supp v) (hpos : ∀ j, 0 ≤ v j) : v i = 0 :=
  le_antisymm (not_lt.mp (by rwa [mem_supp_iff] at hi)) (hpos i)

lemma supp_nonempty {v : Fin (n + 1) → ℝ} (hv : InSimplex v) : (supp v).Nonempty := by
  by_contra h
  have hzero : ∀ i : Fin (n + 1), v i = 0 :=
    fun i => supp_le (fun hi => h ⟨i, hi⟩) hv.1
  linarith [hv.2, Finset.sum_eq_zero (fun i _ => hzero i)]

noncomputable def colorSet (v fv : Fin (n + 1) → ℝ) : Finset (Fin (n + 1)) :=
  (supp v).filter (fun i => fv i ≤ v i)

lemma mem_colorSet_iff {v fv : Fin (n + 1) → ℝ} {i : Fin (n + 1)} :
    i ∈ colorSet v fv ↔ i ∈ supp v ∧ fv i ≤ v i := by
  simp [colorSet, Finset.mem_filter]

private lemma exists_le_of_simplex_map {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) : ∃ i ∈ supp v, fv i ≤ v i := by
  by_contra h
  push_neg at h
  have hle : ∀ i : Fin (n + 1), v i ≤ fv i := by
    intro i
    by_cases hi : i ∈ supp v
    · exact (h i hi).le
    · rw [supp_le hi hv.1]; exact hfv.1 i
  have hlt : ∑ i : Fin (n + 1), v i < ∑ i : Fin (n + 1), fv i :=
    Finset.sum_lt_sum (fun i _ => hle i)
      ⟨(supp_nonempty hv).choose, Finset.mem_univ _, h _ (supp_nonempty hv).choose_spec⟩
  linarith [hv.2, hfv.2]

lemma colorSet_nonempty {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) : (colorSet v fv).Nonempty := by
  obtain ⟨i, hi_supp, hi_le⟩ := exists_le_of_simplex_map hv hfv
  exact ⟨i, mem_colorSet_iff.mpr ⟨hi_supp, hi_le⟩⟩

noncomputable def spernerColor (v fv : Fin (n + 1) → ℝ)
    (hv : InSimplex v) (hfv : InSimplex fv) : Fin (n + 1) :=
  (colorSet v fv).min' (colorSet_nonempty hv hfv)

lemma spernerColor_le {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) :
    fv (spernerColor v fv hv hfv) ≤ v (spernerColor v fv hv hfv) :=
  (mem_colorSet_iff.mp (Finset.min'_mem _ _)).2

lemma spernerColor_ne_of_zero {v fv : Fin (n + 1) → ℝ}
    (hv : InSimplex v) (hfv : InSimplex fv) {j : Fin (n + 1)} (hj : v j = 0) :
    spernerColor v fv hv hfv ≠ j := by
  intro heq
  have hmem := (mem_colorSet_iff.mp (Finset.min'_mem _ _)).1
  rw [heq, mem_supp_iff] at hmem
  linarith [hmem, hj.le]

-- ============================================================
-- SECTION I: n=0 case (trivial)
-- ============================================================

/-- `sperner_panchromatic` for n=0: Δ⁰ is a single point. -/
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
  · fin_cases i
    have hfsum : f (fun _ => (1 : ℝ)) 0 = 1 := by
      have := hfpt.2; simp [Fin.sum_univ_one] at this; exact this
    simp [hfsum]
  · fin_cases i <;> fin_cases j <;> fin_cases l <;> simp

-- ============================================================
-- SECTION II: n=1 case (discrete IVT)
-- ============================================================

/-- `sperner_panchromatic` for n=1: proved via discrete IVT.
Grid g(k) = (k/N, (N-k)/N). K = last k with color 1. Witnesses: (g(K+1), g(K)). -/
theorem sperner_panchromatic_one (N : ℕ) (hN : 0 < N)
    (f : (Fin 2 → ℝ) → Fin 2 → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin 2 → Fin 2 → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin 2, f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin 2) (l : Fin 2), |v i l - v j l| ≤ (1 : ℝ) / N) := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  have hNrpos : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  let g : Fin (N + 1) → Fin 2 → ℝ := fun k i =>
    if i.val = 0 then (k.val : ℝ) / N else ((N - k.val : ℕ) : ℝ) / N
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
  let c : Fin (N + 1) → Fin 2 := fun k =>
    spernerColor (g k) (f (g k)) (hg k) (hfg k)
  have hc0 : c ⟨0, Nat.succ_pos N⟩ = 1 := by
    have hg0 : g ⟨0, Nat.succ_pos N⟩ (0 : Fin 2) = 0 := by
      simp [g, show (0 : Fin 2).val = 0 from rfl]
    have hne : c ⟨0, Nat.succ_pos N⟩ ≠ 0 :=
      spernerColor_ne_of_zero (hg _) (hfg _) hg0
    exact Fin.ext (by
      have : (c ⟨0, Nat.succ_pos N⟩).val ≠ 0 := fun h => hne (Fin.ext h)
      have := (c ⟨0, Nat.succ_pos N⟩).isLt; omega)
  have hcN : c ⟨N, Nat.lt_succ_self N⟩ = 0 := by
    have hgN : g ⟨N, Nat.lt_succ_self N⟩ (1 : Fin 2) = 0 := by
      simp [g, show (1 : Fin 2).val = 1 from rfl,
            show ¬(1 : Nat) = 0 from by omega, Nat.sub_self]
    have hne : c ⟨N, Nat.lt_succ_self N⟩ ≠ 1 :=
      spernerColor_ne_of_zero (hg _) (hfg _) hgN
    exact Fin.ext (by
      have : (c ⟨N, Nat.lt_succ_self N⟩).val ≠ 1 := fun h => hne (Fin.ext h)
      have := (c ⟨N, Nat.lt_succ_self N⟩).isLt; omega)
  let S : Finset (Fin (N + 1)) := univ.filter (fun k => c k = 1)
  have hS_ne : S.Nonempty :=
    ⟨⟨0, Nat.succ_pos N⟩, mem_filter.mpr ⟨mem_univ _, hc0⟩⟩
  let K : Fin (N + 1) := S.max' hS_ne
  have hcK : c K = 1 := (mem_filter.mp (S.max'_mem hS_ne)).2
  have hK_lt_N : K.val < N := by
    by_contra h; push_neg at h
    have hKN : K = ⟨N, Nat.lt_succ_self N⟩ :=
      Fin.ext (Nat.le_antisymm (Nat.lt_succ_iff.mp K.isLt) h)
    have hcK' : c ⟨N, Nat.lt_succ_self N⟩ = 1 := hKN ▸ hcK
    rw [hcK'] at hcN
    exact absurd hcN (by decide)
  let K1 : Fin (N + 1) := ⟨K.val + 1, by omega⟩
  have hcK1 : c K1 = 0 := by
    have hK1_not_S : K1 ∉ S := fun hmem =>
      absurd (Finset.le_max' S K1 hmem) (by simp [K1, Fin.le_iff_val_le_val]; omega)
    exact Fin.ext (by
      have : (c K1).val ≠ 1 :=
        fun h => hK1_not_S (mem_filter.mpr ⟨mem_univ _, Fin.ext h⟩)
      have := (c K1).isLt; omega)
  have hle_K : f (g K) (1 : Fin 2) ≤ g K (1 : Fin 2) := by
    have h := spernerColor_le (hg K) (hfg K)
    rw [show spernerColor (g K) (f (g K)) (hg K) (hfg K) = c K from rfl, hcK] at h
    exact h
  have hle_K1 : f (g K1) (0 : Fin 2) ≤ g K1 (0 : Fin 2) := by
    have h := spernerColor_le (hg K1) (hfg K1)
    rw [show spernerColor (g K1) (f (g K1)) (hg K1) (hfg K1) = c K1 from rfl, hcK1] at h
    exact h
  have hg0_diff : g K1 (0 : Fin 2) - g K (0 : Fin 2) = 1 / N := by
    simp only [g, K1, show (0 : Fin 2).val = 0 from rfl, if_true]
    push_cast; field_simp; ring
  have hg1_diff : g K (1 : Fin 2) - g K1 (1 : Fin 2) = 1 / N := by
    simp only [g, K1, show (1 : Fin 2).val = 1 from rfl,
               show ¬(1 : Nat) = 0 from by omega, if_false]
    have h1 : ((N - K.val : ℕ) : ℝ) = (N : ℝ) - K.val := by push_cast; omega
    have h2 : ((N - (K.val + 1) : ℕ) : ℝ) = (N : ℝ) - K.val - 1 := by push_cast; omega
    rw [h1, h2]; field_simp; ring
  have habs_pos : (0 : ℝ) < 1 / N := by positivity
  have hdiam : ∀ (l : Fin 2), |g K1 l - g K l| ≤ 1 / N := by
    intro l; fin_cases l
    · rw [hg0_diff, abs_of_pos habs_pos]
    · have : g K1 (1 : Fin 2) - g K (1 : Fin 2) = -(1 / N) := by linarith [hg1_diff]
      rw [this, abs_neg, abs_of_pos habs_pos]
  refine ⟨fun i => if i.val = 0 then g K1 else g K, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [hg]
  · intro i; fin_cases i
    · simpa using hle_K1
    · simpa using hle_K
  · intro i j l
    fin_cases i <;> fin_cases j <;>
      simp only [show (0 : Fin 2).val = 0 from rfl, if_true,
                 show (1 : Fin 2).val = 1 from rfl,
                 show ¬(1 : Nat) = 0 from by omega, if_false]
    · simp [le_of_lt habs_pos]
    · exact hdiam l
    · rw [abs_sub_comm]; exact hdiam l
    · simp [le_of_lt habs_pos]

end SpernerFreudSimp
