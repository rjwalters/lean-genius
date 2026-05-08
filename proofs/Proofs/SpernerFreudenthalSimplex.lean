/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib
import Proofs.SpernerSimplicialInstance

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

-- ============================================================
-- SECTION III: n=2 case via Type-1/Type-2 triangulation of Δ²
-- ============================================================

/-!
## Type-1/Type-2 Triangulation of Δ²

The Nth regular subdivision of Δ² = {(x₀,x₁,x₂) | Σxᵢ=1, xᵢ≥0} uses:
- **Type-1** simplex: {a+e₀, a+e₁, a+e₂} for each a with Σa=N-1
- **Type-2** simplex: {a+e₀+e₁, a+e₀+e₂, a+e₁+e₂} for each a with Σa=N-2

We represent vertices as pairs (a₀, a₁) ∈ ℕ×ℕ, with a₂ = N-a₀-a₁ implicit.
- Type-1 with base b = (b₀,b₁): {(b₀+1,b₁), (b₀,b₁+1), (b₀,b₁)}  (need b₀+b₁<N)
- Type-2 with base b = (b₀,b₁): {(b₀+1,b₁+1), (b₀+1,b₁), (b₀,b₁+1)} (need b₀+b₁+1<N)

**Pseudomanifold**: each edge is in at most 1 Type-1 and at most 1 Type-2 simplex,
so each edge is in at most 2 simplices total.

**Boundary doors oddness** (sorry in this file): by induction using the n=1 result,
boundary doors on face 2 = panchromatic edges of the 1D grid, which is odd.
-/

section N2Triang

-- ============================================================
-- Vertex type: ℕ × ℕ with lexicographic LinearOrder
-- ============================================================

private noncomputable instance natPairLinearOrder : LinearOrder (ℕ × ℕ) :=
  LinearOrder.lift' (toLex (α := ℕ × ℕ)) (fun _ _ h => h)

-- ============================================================
-- Simplex constructors
-- ============================================================

private def t1 (b : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ({(b.1 + 1, b.2), (b.1, b.2 + 1), b} : Finset (ℕ × ℕ))

private def t2 (b : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  ({(b.1 + 1, b.2 + 1), (b.1 + 1, b.2), (b.1, b.2 + 1)} : Finset (ℕ × ℕ))

private def t1Bases (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun b => b.1 + b.2 < N)

private def t2Bases (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun b => b.1 + b.2 + 1 < N)

private def topSimps2 (N : ℕ) : Finset (Finset (ℕ × ℕ)) :=
  (t1Bases N).image t1 ∪ (t2Bases N).image t2

-- ============================================================
-- card_eq: every simplex has 3 vertices
-- ============================================================

private lemma t1_card (b : ℕ × ℕ) : (t1 b).card = 3 := by
  unfold t1
  have h1 : (b.1 + 1, b.2) ∉ ({(b.1, b.2 + 1), b} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or, not_and]
    omega
  have h2 : (b.1, b.2 + 1) ∉ ({b} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]; omega
  rw [Finset.card_insert_of_not_mem h1, Finset.card_insert_of_not_mem h2,
      Finset.card_singleton]

private lemma t2_card (b : ℕ × ℕ) : (t2 b).card = 3 := by
  unfold t2
  have h1 : (b.1 + 1, b.2 + 1) ∉ ({(b.1 + 1, b.2), (b.1, b.2 + 1)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or, not_and]
    omega
  have h2 : (b.1 + 1, b.2) ∉ ({(b.1, b.2 + 1)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]; omega
  rw [Finset.card_insert_of_not_mem h1, Finset.card_insert_of_not_mem h2,
      Finset.card_singleton]

private lemma topSimps2_card_eq (N : ℕ) :
    ∀ s ∈ topSimps2 N, s.card = 3 := by
  intro s hs
  simp only [topSimps2, Finset.mem_union, Finset.mem_image] at hs
  rcases hs with ⟨b, _, rfl⟩ | ⟨b, _, rfl⟩
  · exact t1_card b
  · exact t2_card b

-- ============================================================
-- pseudomanifold: each edge {u,v} is in at most 1 Type-1 and
-- at most 1 Type-2 simplex, so at most 2 simplices total.
-- ============================================================

-- The Type-1 simplex containing {u,v} has a uniquely determined base.
private lemma t1_unique_base {b c : ℕ × ℕ} {u v : ℕ × ℕ} (huv : u ≠ v)
    (hb : {u, v} ⊆ t1 b) (hc : {u, v} ⊆ t1 c) : b = c := by
  simp only [t1, Finset.insert_subset_iff, Finset.singleton_subset_iff,
             Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hb hc
  obtain ⟨hub, hvb⟩ := hb
  obtain ⟨huc, hvc⟩ := hc
  -- Case bash: each of u,v is one of the 3 vertices in t1 b and t1 c.
  -- In each case either u=v (contradiction with huv) or b=c follows from omega.
  rcases hub with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hvb with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases huc with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    rcases hvc with ⟨h7, h8⟩ | ⟨h7, h8⟩ | ⟨h7, h8⟩ <;>
    first
    | exact absurd (Prod.ext_iff.mpr ⟨by omega, by omega⟩) huv
    | exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma t2_unique_base {b c : ℕ × ℕ} {u v : ℕ × ℕ} (huv : u ≠ v)
    (hb : {u, v} ⊆ t2 b) (hc : {u, v} ⊆ t2 c) : b = c := by
  simp only [t2, Finset.insert_subset_iff, Finset.singleton_subset_iff,
             Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hb hc
  obtain ⟨hub, hvb⟩ := hb
  obtain ⟨huc, hvc⟩ := hc
  rcases hub with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hvb with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases huc with ⟨h5, h6⟩ | ⟨h5, h6⟩ | ⟨h5, h6⟩ <;>
    rcases hvc with ⟨h7, h8⟩ | ⟨h7, h8⟩ | ⟨h7, h8⟩ <;>
    first
    | exact absurd (Prod.ext_iff.mpr ⟨by omega, by omega⟩) huv
    | exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma t1_filter_le_one (N : ℕ) (u v : ℕ × ℕ) (huv : u ≠ v) :
    (((t1Bases N).image t1).filter (fun s => ({u, v} : Finset _) ⊆ s)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  simp only [Finset.mem_filter, Finset.mem_image] at hs ht
  obtain ⟨⟨b, _, rfl⟩, hs_sub⟩ := hs
  obtain ⟨⟨c, _, rfl⟩, ht_sub⟩ := ht
  exact congrArg t1 (t1_unique_base huv hs_sub ht_sub)

private lemma t2_filter_le_one (N : ℕ) (u v : ℕ × ℕ) (huv : u ≠ v) :
    (((t2Bases N).image t2).filter (fun s => ({u, v} : Finset _) ⊆ s)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro s hs t ht
  simp only [Finset.mem_filter, Finset.mem_image] at hs ht
  obtain ⟨⟨b, _, rfl⟩, hs_sub⟩ := hs
  obtain ⟨⟨c, _, rfl⟩, ht_sub⟩ := ht
  exact congrArg t2 (t2_unique_base huv hs_sub ht_sub)

private lemma topSimps2_pseudomanifold (N : ℕ) :
    ∀ (face : Finset (ℕ × ℕ)), face.card = 2 →
      ((topSimps2 N).filter (fun s => face ⊆ s)).card ≤ 2 := by
  intro face hface
  rw [Finset.card_eq_two] at hface
  obtain ⟨u, v, huv, rfl⟩ := hface
  have hle : ((topSimps2 N).filter (fun s => ({u, v} : Finset _) ⊆ s)).card ≤
      (((t1Bases N).image t1).filter (fun s => ({u, v} : Finset _) ⊆ s)).card +
      (((t2Bases N).image t2).filter (fun s => ({u, v} : Finset _) ⊆ s)).card := by
    simp only [topSimps2, Finset.filter_union]
    exact Finset.card_union_le _ _
  linarith [t1_filter_le_one N u v huv, t2_filter_le_one N u v huv]

-- ============================================================
-- AbstractSimplicialData instance (all adj axioms proved)
-- ============================================================

private noncomputable def simData2 (N : ℕ) : AbstractSimplicialData (ℕ × ℕ) 2 where
  topSimplices := topSimps2 N
  card_eq := topSimps2_card_eq N
  pseudomanifold := topSimps2_pseudomanifold N

-- ============================================================
-- n=2 Sperner panchromatic (boundary_doors_odd sorry'd)
-- ============================================================

/-- **n=2 sperner_panchromatic** (boundary_doors_odd sorry; all structural proofs done).
    The triangulation and pseudomanifold are fully proved. The remaining step is to show
    the boundary door count is odd, which follows from the n=1 result by induction. -/
theorem sperner_panchromatic_two (N : ℕ) (hN : 0 < N)
    (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin 3 → Fin 3 → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin 3, f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin 3) (l : Fin 3), |v i l - v j l| ≤ (2 : ℝ) / N) := by
  -- The Type-1/Type-2 triangulation of Δ² is fully constructed:
  -- simData2 N : AbstractSimplicialData (ℕ×ℕ) 2 (pseudomanifold proved above)
  -- (simData2 N).toTriangulation : Triangulation (ℕ×ℕ) 2 (all adj axioms proved)
  -- The Sperner coloring + boundary_doors_odd → panchromatic triangle exists.
  -- Remaining sorry: boundary_doors_odd (reduces to sperner_panchromatic_one by induction)
  sorry

end N2Triang

-- ============================================================
-- SECTION IV: XOR parity (pure combinatorics)
-- ============================================================

section N2XOR

/-- **XOR parity**: the number of adjacent differing pairs in a binary sequence
`g : ℕ → Fin 2` over `{0,...,n-1}` has the same parity as `g 0 ≠ g n`. -/
private lemma changes_parity_mod2 (n : ℕ) (g : ℕ → Fin 2) :
    ((Finset.range n).filter (fun k => g k ≠ g (k + 1))).card % 2 =
    if g 0 = g n then 0 else 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.range_succ, Finset.filter_union, Finset.filter_singleton]
    have hdisj : Disjoint ((Finset.range m).filter (fun k => g k ≠ g (k + 1)))
        (if g m ≠ g (m + 1) then {m} else ∅) := by
      apply Finset.disjoint_left.mpr; intro x hx
      simp only [Finset.mem_filter, Finset.mem_range] at hx
      split_ifs with h
      · simp only [Finset.mem_singleton]; omega
      · exact Finset.not_mem_empty x
    rw [Finset.card_union_of_disjoint hdisj]
    by_cases hne : g m ≠ g (m + 1)
    · rw [if_pos hne, Finset.card_singleton, ih]
      split_ifs with h0
      · have h1 : g 0 ≠ g (m + 1) := by
          fin_cases (g 0) <;> fin_cases (g m) <;> fin_cases (g (m + 1)) <;> simp_all
        rw [if_neg h1]; omega
      · have h1 : g 0 = g (m + 1) := by
          fin_cases (g 0) <;> fin_cases (g m) <;> fin_cases (g (m + 1)) <;> simp_all
        rw [if_pos h1]; omega
    · have heq : g m = g (m + 1) := not_ne_iff.mp hne
      rw [if_neg hne, Finset.card_empty, Nat.add_zero, ih]
      simp only [heq]

/-- A binary sequence with g(0)=1 and g(n)=0 has an odd number of adjacent transitions. -/
private lemma odd_changes (n : ℕ) (g : ℕ → Fin 2)
    (hg0 : g 0 = 1) (hgn : g n = 0) :
    Odd ((Finset.range n).filter (fun k => g k ≠ g (k + 1))).card := by
  have hne : g 0 ≠ g n := by rw [hg0, hgn]; decide
  rw [Nat.odd_iff, changes_parity_mod2, if_neg hne]

end N2XOR

-- ============================================================
-- SECTION V: Grid infrastructure for n=2 Sperner coloring
-- ============================================================

section N2Grid

variable (N : ℕ) (hN : 0 < N)
variable (f : (Fin 3 → ℝ) → Fin 3 → ℝ) (hf_map : ∀ v, InSimplex v → InSimplex (f v))

/-- Grid embedding: (b₀, b₁) ↦ (b₀/N, b₁/N, (N-b₀-b₁)/N) in Δ². -/
private noncomputable def gridPt (b : ℕ × ℕ) : Fin 3 → ℝ := fun i =>
  if i.val = 0 then (b.1 : ℝ) / N
  else if i.val = 1 then (b.2 : ℝ) / N
  else ((N : ℝ) - b.1 - b.2) / N

/-- `gridPt N b` is in Δ² when b₀ + b₁ ≤ N. -/
private lemma gridPt_inSimplex (b : ℕ × ℕ) (hb : b.1 + b.2 ≤ N) :
    InSimplex (gridPt N b) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hb12 : (b.1 : ℝ) + b.2 ≤ N := by exact_mod_cast hb
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;>
      simp only [gridPt, show (0:Fin 3).val=0 from rfl, ↓reduceIte,
                 show (1:Fin 3).val=1 from rfl, show ¬(1:ℕ)=0 from by omega,
                 show (2:Fin 3).val=2 from rfl, show ¬(2:ℕ)=0 from by omega,
                 show ¬(2:ℕ)=1 from by omega] <;>
      first
        | exact div_nonneg (Nat.cast_nonneg _) hNr.le
        | exact div_nonneg (by linarith) hNr.le
  · rw [Fin.sum_univ_three]
    simp only [gridPt, show (0:Fin 3).val=0 from rfl, ↓reduceIte,
               show (1:Fin 3).val=1 from rfl, show ¬(1:ℕ)=0 from by omega,
               show (2:Fin 3).val=2 from rfl, show ¬(2:ℕ)=0 from by omega,
               show ¬(2:ℕ)=1 from by omega]
    field_simp [hNr.ne']
    ring

/-- Sperner coloring for grid vertex b with b₀+b₁ ≤ N. -/
private noncomputable def cN2 (b : ℕ × ℕ) (hb : b.1 + b.2 ≤ N) : Fin 3 :=
  spernerColor (gridPt N b) (f (gridPt N b))
    (gridPt_inSimplex N hN b hb) (hf_map _ (gridPt_inSimplex N hN b hb))

/-- Sperner condition: coordinate j = 0 implies color ≠ j. -/
private lemma cN2_ne_of_zero (b : ℕ × ℕ) (hb : b.1 + b.2 ≤ N)
    (j : Fin 3) (hj : gridPt N b j = 0) :
    cN2 N hN f hf_map b hb ≠ j :=
  spernerColor_ne_of_zero (gridPt_inSimplex N hN b hb)
    (hf_map _ (gridPt_inSimplex N hN b hb)) hj

private lemma gridPt_0N_coord0 : gridPt N (0, N) 0 = 0 := by
  simp [gridPt, show (0:Fin 3).val=0 from rfl]

private lemma gridPt_0N_coord2 : gridPt N (0, N) 2 = 0 := by
  simp only [gridPt, show (2:Fin 3).val=2 from rfl,
             show ¬(2:ℕ)=0 from by omega, show ¬(2:ℕ)=1 from by omega, ↓reduceIte]
  push_cast; ring

private lemma gridPt_N0_coord1 : gridPt N (N, 0) 1 = 0 := by
  simp [gridPt, show (1:Fin 3).val=1 from rfl, show ¬(1:ℕ)=0 from by omega]

private lemma gridPt_N0_coord2 : gridPt N (N, 0) 2 = 0 := by
  simp only [gridPt, show (2:Fin 3).val=2 from rfl,
             show ¬(2:ℕ)=0 from by omega, show ¬(2:ℕ)=1 from by omega, ↓reduceIte]
  push_cast; ring

private lemma gridPt_00_coord0 : gridPt N (0, 0) 0 = 0 := by
  simp [gridPt, show (0:Fin 3).val=0 from rfl]

private lemma gridPt_00_coord1 : gridPt N (0, 0) 1 = 0 := by
  simp [gridPt, show (1:Fin 3).val=1 from rfl, show ¬(1:ℕ)=0 from by omega]

/-- Corner (0, N) has forced color 1: on face 0 (coord 0 = 0) and face 2 (coord 2 = 0). -/
private lemma cN2_left_corner :
    cN2 N hN f hf_map (0, N) (by omega) = 1 := by
  have h0 := cN2_ne_of_zero N hN f hf_map (0, N) (by omega) 0 (gridPt_0N_coord0 N)
  have h2 := cN2_ne_of_zero N hN f hf_map (0, N) (by omega) 2 (gridPt_0N_coord2 N)
  fin_cases (cN2 N hN f hf_map (0, N) (by omega)) <;> simp_all

/-- Corner (N, 0) has forced color 0: on face 1 (coord 1 = 0) and face 2 (coord 2 = 0). -/
private lemma cN2_right_corner :
    cN2 N hN f hf_map (N, 0) (by omega) = 0 := by
  have h1 := cN2_ne_of_zero N hN f hf_map (N, 0) (by omega) 1 (gridPt_N0_coord1 N)
  have h2 := cN2_ne_of_zero N hN f hf_map (N, 0) (by omega) 2 (gridPt_N0_coord2 N)
  fin_cases (cN2 N hN f hf_map (N, 0) (by omega)) <;> simp_all

/-- Corner (0, 0) has forced color 2: on face 0 (coord 0 = 0) and face 1 (coord 1 = 0). -/
private lemma cN2_origin_corner :
    cN2 N hN f hf_map (0, 0) (by omega) = 2 := by
  have h0 := cN2_ne_of_zero N hN f hf_map (0, 0) (by omega) 0 (gridPt_00_coord0 N)
  have h1 := cN2_ne_of_zero N hN f hf_map (0, 0) (by omega) 1 (gridPt_00_coord1 N)
  fin_cases (cN2 N hN f hf_map (0, 0) (by omega)) <;> simp_all

/-- Geometric face predicate for grid vertices.
A vertex `b = (b.1, b.2)` (representing `(b.1/N, b.2/N, (N-b.1-b.2)/N)` in Δ²)
is on face j iff its j-th coordinate is zero. -/
private def onFaceΔ2 (N : ℕ) (b : ℕ × ℕ) (j : Fin 3) : Prop :=
  if j.val = 0 then b.1 = 0
  else if j.val = 1 then b.2 = 0
  else b.1 + b.2 = N

private instance onFaceΔ2_decidable (N : ℕ) (b : ℕ × ℕ) (j : Fin 3) :
    Decidable (onFaceΔ2 N b j) := by
  unfold onFaceΔ2; split_ifs <;> infer_instance

private lemma onFaceΔ2_zero_iff (b : ℕ × ℕ) :
    onFaceΔ2 N b 0 ↔ b.1 = 0 := by
  simp [onFaceΔ2, show (0:Fin 3).val = 0 from rfl]

private lemma onFaceΔ2_one_iff (b : ℕ × ℕ) :
    onFaceΔ2 N b 1 ↔ b.2 = 0 := by
  simp [onFaceΔ2, show (1:Fin 3).val = 1 from rfl]

private lemma onFaceΔ2_two_iff (b : ℕ × ℕ) :
    onFaceΔ2 N b 2 ↔ b.1 + b.2 = N := by
  simp [onFaceΔ2, show (2:Fin 3).val = 2 from rfl, show ¬(2:ℕ)=0 from by omega,
        show ¬(2:ℕ)=1 from by omega]

private lemma onFaceΔ2_zero_iff_gridPt_zero (b : ℕ × ℕ) :
    onFaceΔ2 N b 0 ↔ gridPt N b 0 = 0 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  rw [onFaceΔ2_zero_iff]
  simp only [gridPt, show (0:Fin 3).val = 0 from rfl, ↓reduceIte]
  rw [div_eq_zero_iff]
  constructor
  · intro h; left; exact_mod_cast h
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h hNne

private lemma onFaceΔ2_one_iff_gridPt_zero (b : ℕ × ℕ) :
    onFaceΔ2 N b 1 ↔ gridPt N b 1 = 0 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  rw [onFaceΔ2_one_iff]
  simp only [gridPt, show (1:Fin 3).val = 1 from rfl,
             show ¬(1:ℕ)=0 from by omega, ↓reduceIte]
  rw [div_eq_zero_iff]
  constructor
  · intro h; left; exact_mod_cast h
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h hNne

private lemma onFaceΔ2_two_iff_gridPt_zero (b : ℕ × ℕ) (hb : b.1 + b.2 ≤ N) :
    onFaceΔ2 N b 2 ↔ gridPt N b 2 = 0 := by
  have hNne : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  rw [onFaceΔ2_two_iff]
  simp only [gridPt, show (2:Fin 3).val = 2 from rfl,
             show ¬(2:ℕ)=0 from by omega, show ¬(2:ℕ)=1 from by omega, ↓reduceIte]
  rw [div_eq_zero_iff]
  constructor
  · intro h
    left
    have hb12 : (b.1 : ℝ) + b.2 = N := by exact_mod_cast h
    linarith
  · rintro (h | h)
    · have : (b.1 : ℝ) + b.2 = N := by linarith
      exact_mod_cast this
    · exact absurd h hNne

/-- Sperner condition (face form): if vertex b is on face j of Δ², its color is not j. -/
private lemma cN2_ne_of_onFace (b : ℕ × ℕ) (hb : b.1 + b.2 ≤ N) (j : Fin 3)
    (hface : onFaceΔ2 N b j) : cN2 N hN f hf_map b hb ≠ j := by
  have hzero : gridPt N b j = 0 := by
    fin_cases j
    · exact (onFaceΔ2_zero_iff_gridPt_zero N hN b).mp hface
    · exact (onFaceΔ2_one_iff_gridPt_zero N hN b).mp hface
    · exact (onFaceΔ2_two_iff_gridPt_zero N hN b hb).mp hface
  exact cN2_ne_of_zero N hN f hf_map b hb j hzero

/-- Face 2 diagonal: the coloring g(k) = (cN2(k, N-k) mod 2) has g(0)=1, g(N)=0,
    so by XOR parity there are an odd number of color-changing edges on face 2.

    **Key remaining connection to `sperner_panchromatic_two`** (not yet proved):
    These color-changing edges correspond exactly to the boundary doors of the
    n=2 Type-1/Type-2 triangulation. This requires:
    1. Characterizing adjFn = none for t1/t2 simplices (containersOf analysis)
    2. Showing IsDoor ↔ color-change for face-2 boundary edges
    3. Showing faces 0,1 contribute no doors (Sperner condition)
    4. Applying Triangulation.sperner to get the panchromatic triangle -/
private lemma face2_path_odd :
    let g : ℕ → Fin 2 := fun k =>
      if hk : k ≤ N then
        if (cN2 N hN f hf_map (k, N - k) (by omega)).val = 0 then 0 else 1
      else 1
    Odd ((Finset.range N).filter (fun k => g k ≠ g (k + 1))).card := by
  apply odd_changes
  · -- g 0 = 1: vertex (0, N) has forced color 1
    rw [dif_pos (Nat.zero_le N), Nat.sub_zero]
    have hcol := cN2_left_corner N hN f hf_map
    simp [hcol]
  · -- g N = 0: vertex (N, 0) has forced color 0
    rw [dif_pos (le_refl N), Nat.sub_self]
    have hcol := cN2_right_corner N hN f hf_map
    simp [hcol]

end N2Grid

end SpernerFreudSimp

-- ============================================================
-- Generic `_hLowerDim` discharge helper for Sperner-on-Triangulation
-- (Session 15 — reusable across all concrete Sperner instantiations)
-- ============================================================

/-! ## Generic `_hLowerDim` Discharge

`Triangulation.boundary_doors_odd` (in `SpernerSimplicialInstance.lean`)
requires four hypotheses, one of which (`_hLowerDim`) states that, for
each face index with `faceIdx.val < n`, the boundary doors landing on
geometric face `faceIdx` form an Even-cardinality finset.

Inspecting the proof of `boundary_doors_odd` shows that `_hLowerDim`
is *not actually used* in the proof body — the proof shows directly
that every boundary door must lie on the last face — yet the
hypothesis must still be discharged at every call site.

The lemmas in this section discharge `_hLowerDim` generically: for
*any* Sperner coloring on *any* triangulation, the filter set is
empty (cardinality `0`, hence Even). The argument is the same Sperner
contradiction used inside `boundary_doors_odd` to show `S = S_n`: an
`IsDoor` at color `faceIdx` requires some non-`k` vertex with color
`faceIdx`, but the third filter clause says that non-`k` vertex is on
geometric face `faceIdx`, contradicting the Sperner condition.

These helpers are `f`-independent (they depend only on the abstract
`IsSpernerColoring` predicate) and apply to every concrete Sperner
instantiation. They are intended to be passed directly as the
`_hLowerDim` argument of `Triangulation.boundary_doors_odd`,
eliminating ~30 lines of boilerplate per call site. -/

namespace SpernerLowerDimHelper

open Finset

variable {V : Type*} [DecidableEq V] {n : ℕ}

/-- The `_hLowerDim` filter of `Triangulation.boundary_doors_odd` is
empty whenever `c` is a Sperner coloring with respect to `onFace`
and `faceIdx.val < n`. Any candidate door would witness a vertex
with color `faceIdx` on geometric face `faceIdx`, which the Sperner
condition forbids. -/
lemma sperner_lowerDim_filter_empty
    (T : Triangulation V n)
    (c : V → Fin (n + 1)) (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (hSperner : Triangulation.IsSpernerColoring c onFace)
    (faceIdx : Fin (n + 1)) (hlt : faceIdx.val < n) :
    (Finset.univ.filter (fun p : T.Cell × Fin (n + 1) =>
      CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
      T.adj p.1 p.2 = none ∧
      (∀ j : Fin (n + 1), j ≠ p.2 →
        onFace (T.vertex p.1 j) faceIdx))) = ∅ := by
  rw [Finset.eq_empty_iff_forall_not_mem]
  rintro ⟨s, k⟩ hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  obtain ⟨hDoor, _hAdj, hOnFace⟩ := hmem
  -- `IsDoor c (T.toCellComplex) s k` says: for every `j : Fin n`, some
  -- non-`k` vertex of `s` has color `Fin.castSucc j`.
  have hDoor' := hDoor ⟨faceIdx.val, hlt⟩
  obtain ⟨i, hi_ne, hi_color⟩ := hDoor'
  -- Vertex `i` is on face `faceIdx` (since `i ≠ k` and `hOnFace` covers
  -- all non-`k` vertices).
  have hOnFace_i := hOnFace i hi_ne
  -- Sperner condition: vertex on face `faceIdx` has color ≠ `faceIdx`.
  have hSperner_i := hSperner (T.vertex s i) faceIdx hOnFace_i
  -- `T.toCellComplex.vertex = T.vertex` is definitional.
  change c (T.vertex s i) = _ at hi_color
  -- `Fin.castSucc ⟨faceIdx.val, hlt⟩ = faceIdx`.
  have hcast : (⟨faceIdx.val, hlt⟩ : Fin n).castSucc = faceIdx :=
    Fin.ext rfl
  rw [hcast] at hi_color
  exact hSperner_i hi_color

/-- Corollary of `sperner_lowerDim_filter_empty`: the cardinality is
`0`, hence Even. This is the exact form required by `_hLowerDim`
of `Triangulation.boundary_doors_odd`, ready to be passed at any
concrete call site. -/
lemma sperner_lowerDim_card_even
    (T : Triangulation V n)
    (c : V → Fin (n + 1)) (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (hSperner : Triangulation.IsSpernerColoring c onFace)
    (faceIdx : Fin (n + 1)) (hlt : faceIdx.val < n) :
    Even (Finset.univ.filter (fun p : T.Cell × Fin (n + 1) =>
      CellComplex.IsDoor c (T.toCellComplex) p.1 p.2 ∧
      T.adj p.1 p.2 = none ∧
      (∀ j : Fin (n + 1), j ≠ p.2 →
        onFace (T.vertex p.1 j) faceIdx))).card := by
  rw [sperner_lowerDim_filter_empty T c onFace hSperner faceIdx hlt,
      Finset.card_empty]
  exact ⟨0, rfl⟩

end SpernerLowerDimHelper
