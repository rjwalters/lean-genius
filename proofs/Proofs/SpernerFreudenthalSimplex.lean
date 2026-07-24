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
- `sperner_panchromatic_two`: n=2 (Type-1/Type-2 triangulation of Δ², via
  `Triangulation.boundary_doors_odd` — boundary doors on face 2 biject with
  the odd color-changing edges of the diagonal path; end of file)

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
  have hsum0 : ∑ i : Fin (n + 1), v i = 0 := Finset.sum_eq_zero (fun i _ => hzero i)
  linarith [hv.2, hsum0]

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
  have hmem : spernerColor v fv hv hfv ∈ supp v :=
    (mem_colorSet_iff.mp (Finset.min'_mem (colorSet v fv) (colorSet_nonempty hv hfv))).1
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
    hf_map _ ⟨fun _ => zero_le_one, by simp [Fin.sum_univ_one]⟩
  refine ⟨fun _ _ => 1,
          fun _ => ⟨fun _ => zero_le_one, by simp [Fin.sum_univ_one]⟩,
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
    · show ∑ i : Fin 2, g k i = 1
      simp only [g, Fin.sum_univ_two,
                 show (0 : Fin 2).val = 0 from rfl, if_true,
                 show (1 : Fin 2).val = 1 from rfl,
                 show ¬(1 : Nat) = 0 from by omega, if_false]
      have hcast : ((k : ℕ) : ℝ) + ((N - (k : ℕ) : ℕ) : ℝ) = (N : ℝ) := by
        rw [Nat.cast_sub hkle]; ring
      rw [← add_div, hcast, div_self hNr]
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
    have hK1_not_S : K1 ∉ S := by
      intro hmem
      have hle : K1 ≤ K := Finset.le_max' S K1 hmem
      have hnle : ¬ (K1 ≤ K) := by simp [K1, Fin.le_iff_val_le_val]
      exact hnle hle
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
    have h1 : ((N - K.val : ℕ) : ℝ) = (N : ℝ) - K.val := by
      rw [Nat.cast_sub hK_lt_N.le]
    have h2 : ((N - (K.val + 1) : ℕ) : ℝ) = (N : ℝ) - K.val - 1 := by
      rw [Nat.cast_sub (by omega : K.val + 1 ≤ N)]; push_cast; ring
    rw [h1, h2]; field_simp; ring
  have habs_pos : (0 : ℝ) < 1 / N := by positivity
  have hdiam : ∀ (l : Fin 2), |g K1 l - g K l| ≤ 1 / N := by
    intro l; fin_cases l
    · show |g K1 (0 : Fin 2) - g K (0 : Fin 2)| ≤ 1 / N
      rw [hg0_diff, abs_of_pos habs_pos]
    · show |g K1 (1 : Fin 2) - g K (1 : Fin 2)| ≤ 1 / N
      have : g K1 (1 : Fin 2) - g K (1 : Fin 2) = -(1 / N) := by linarith [hg1_diff]
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

**Boundary doors oddness** (proved in section N2LastFaceAssembly): boundary doors
on face 2 biject with the color-changing edges of the 1D diagonal grid path
(`face2_path_odd_gDiag`), which are odd by discrete IVT parity.
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
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff,
               not_or, not_and]
    omega
  have h2 : (b.1, b.2 + 1) ∉ ({b} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff, not_and]; omega
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]

private lemma t2_card (b : ℕ × ℕ) : (t2 b).card = 3 := by
  unfold t2
  have h1 : (b.1 + 1, b.2 + 1) ∉ ({(b.1 + 1, b.2), (b.1, b.2 + 1)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, not_or, not_and]
    omega
  have h2 : (b.1 + 1, b.2) ∉ ({(b.1, b.2 + 1)} : Finset (ℕ × ℕ)) := by
    simp only [Finset.mem_singleton, Prod.mk.injEq, not_and]; omega
  rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
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
             Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff] at hb hc
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
             Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff] at hb hc
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

private noncomputable def simData2 (N : ℕ) : Triangulation.AbstractSimplicialData (ℕ × ℕ) 2 where
  topSimplices := topSimps2 N
  card_eq := topSimps2_card_eq N
  pseudomanifold := topSimps2_pseudomanifold N

-- ============================================================
-- n=2 Sperner panchromatic: the theorem `sperner_panchromatic_two`
-- is stated and fully proved at the END of this file (section
-- N2Panchromatic), after the boundary-door infrastructure it
-- consumes (S16-S33). The triangulation and pseudomanifold above
-- are its geometric core.
-- ============================================================

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
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hne : g m ≠ g (m + 1)
    · rw [if_pos hne, Finset.card_insert_of_notMem (by simp)]
      by_cases h0 : g 0 = g m
      · have ihv := ih
        rw [if_pos h0] at ihv
        have h1 : g 0 ≠ g (m + 1) := by rw [h0]; exact hne
        rw [if_neg h1]; omega
      · have ihv := ih
        rw [if_neg h0] at ihv
        have h1 : g 0 = g (m + 1) := by
          set a := g 0 with ha
          set b := g m with hb
          set c := g (m + 1) with hc
          clear_value a b c
          fin_cases a <;> fin_cases b <;> fin_cases c <;> simp_all
        rw [if_pos h1]; omega
    · have heq : g m = g (m + 1) := not_ne_iff.mp hne
      rw [if_neg hne, ih]
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

include hN

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

include f hf_map

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

omit hN f hf_map in
private lemma gridPt_0N_coord0 : gridPt N (0, N) 0 = 0 := by
  simp [gridPt, show (0:Fin 3).val=0 from rfl]

omit hN f hf_map in
private lemma gridPt_0N_coord2 : gridPt N (0, N) 2 = 0 := by
  simp only [gridPt, show (2:Fin 3).val=2 from rfl,
             show ¬(2:ℕ)=0 from by omega, show ¬(2:ℕ)=1 from by omega, ↓reduceIte]
  push_cast; ring

omit hN f hf_map in
private lemma gridPt_N0_coord1 : gridPt N (N, 0) 1 = 0 := by
  simp [gridPt, show (1:Fin 3).val=1 from rfl, show ¬(1:ℕ)=0 from by omega]

omit hN f hf_map in
private lemma gridPt_N0_coord2 : gridPt N (N, 0) 2 = 0 := by
  simp only [gridPt, show (2:Fin 3).val=2 from rfl,
             show ¬(2:ℕ)=0 from by omega, show ¬(2:ℕ)=1 from by omega, ↓reduceIte]
  push_cast; ring

omit hN f hf_map in
private lemma gridPt_00_coord0 : gridPt N (0, 0) 0 = 0 := by
  simp [gridPt, show (0:Fin 3).val=0 from rfl]

omit hN f hf_map in
private lemma gridPt_00_coord1 : gridPt N (0, 0) 1 = 0 := by
  simp [gridPt, show (1:Fin 3).val=1 from rfl, show ¬(1:ℕ)=0 from by omega]

/-- Corner (0, N) has forced color 1: on face 0 (coord 0 = 0) and face 2 (coord 2 = 0). -/
private lemma cN2_left_corner :
    cN2 N hN f hf_map (0, N) (by omega) = 1 := by
  have h0 := cN2_ne_of_zero N hN f hf_map (0, N) (by omega) 0 (gridPt_0N_coord0 N)
  have h2 := cN2_ne_of_zero N hN f hf_map (0, N) (by omega) 2 (gridPt_0N_coord2 N)
  set c := cN2 N hN f hf_map (0, N) (by omega) with hc
  clear_value c
  fin_cases c <;> simp_all

/-- Corner (N, 0) has forced color 0: on face 1 (coord 1 = 0) and face 2 (coord 2 = 0). -/
private lemma cN2_right_corner :
    cN2 N hN f hf_map (N, 0) (by omega) = 0 := by
  have h1 := cN2_ne_of_zero N hN f hf_map (N, 0) (by omega) 1 (gridPt_N0_coord1 N)
  have h2 := cN2_ne_of_zero N hN f hf_map (N, 0) (by omega) 2 (gridPt_N0_coord2 N)
  set c := cN2 N hN f hf_map (N, 0) (by omega) with hc
  clear_value c
  fin_cases c <;> simp_all

/-- Corner (0, 0) has forced color 2: on face 0 (coord 0 = 0) and face 1 (coord 1 = 0). -/
private lemma cN2_origin_corner :
    cN2 N hN f hf_map (0, 0) (by omega) = 2 := by
  have h0 := cN2_ne_of_zero N hN f hf_map (0, 0) (by omega) 0 (gridPt_00_coord0 N)
  have h1 := cN2_ne_of_zero N hN f hf_map (0, 0) (by omega) 1 (gridPt_00_coord1 N)
  set c := cN2 N hN f hf_map (0, 0) (by omega) with hc
  clear_value c
  fin_cases c <;> simp_all

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

omit hN f hf_map in
private lemma onFaceΔ2_zero_iff (b : ℕ × ℕ) :
    onFaceΔ2 N b 0 ↔ b.1 = 0 := by
  simp [onFaceΔ2, show (0:Fin 3).val = 0 from rfl]

omit hN f hf_map in
private lemma onFaceΔ2_one_iff (b : ℕ × ℕ) :
    onFaceΔ2 N b 1 ↔ b.2 = 0 := by
  simp [onFaceΔ2, show (1:Fin 3).val = 1 from rfl]

omit hN f hf_map in
private lemma onFaceΔ2_two_iff (b : ℕ × ℕ) :
    onFaceΔ2 N b 2 ↔ b.1 + b.2 = N := by
  simp [onFaceΔ2, show (2:Fin 3).val = 2 from rfl, show ¬(2:ℕ)=0 from by omega,
        show ¬(2:ℕ)=1 from by omega]

omit f hf_map in
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

omit f hf_map in
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

omit f hf_map in
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
    show (if hk : (0:ℕ) ≤ N then
            if (cN2 N hN f hf_map (0, N - 0) (by omega)).val = 0 then 0 else 1
          else 1) = 1
    rw [dif_pos (Nat.zero_le N)]
    have heq : cN2 N hN f hf_map (0, N - 0) (by omega) = cN2 N hN f hf_map (0, N) (by omega) := by
      congr 1
    rw [heq, cN2_left_corner N hN f hf_map]
    decide
  · -- g N = 0: vertex (N, 0) has forced color 0
    show (if hk : N ≤ N then
            if (cN2 N hN f hf_map (N, N - N) (by omega)).val = 0 then 0 else 1
          else 1) = 0
    rw [dif_pos (le_refl N)]
    have heq : cN2 N hN f hf_map (N, N - N) (by omega) = cN2 N hN f hf_map (N, 0) (by omega) := by
      congr 1
      simp
    rw [heq, cN2_right_corner N hN f hf_map]
    decide

-- ============================================================
-- SECTION VI: Total wrapper of cN2 + IsSpernerColoring lift
-- (Session 14 — bridges concrete coloring to Triangulation API)
-- ============================================================

include N in
/-- Total wrapper of `cN2` to a function on all of `ℕ × ℕ`.
    Default to color `0` outside the `b₀+b₁≤N` region; this wrapping is
    irrelevant since only in-range vertices appear in `topSimps2 N`. -/
private noncomputable def cN2_total : (ℕ × ℕ) → Fin 3 :=
  fun b => if h : b.1 + b.2 ≤ N then cN2 N hN f hf_map b h else 0

/-- On the in-range region, the wrapper agrees with `cN2`. -/
private lemma cN2_total_eq (b : ℕ × ℕ) (hb : b.1 + b.2 ≤ N) :
    cN2_total N hN f hf_map b = cN2 N hN f hf_map b hb := by
  unfold cN2_total
  exact dif_pos hb

/-- Strict face predicate: combines the geometric `onFaceΔ2` predicate with the
    in-range constraint `b.1+b.2 ≤ N`. The conjunction makes the Sperner
    condition liftable to a total function on `ℕ × ℕ` — exactly the form
    required by `Triangulation.IsSpernerColoring`. -/
private def onFaceΔ2_strict (N : ℕ) (b : ℕ × ℕ) (j : Fin 3) : Prop :=
  b.1 + b.2 ≤ N ∧ onFaceΔ2 N b j

private instance onFaceΔ2_strict_decidable (N : ℕ) (b : ℕ × ℕ) (j : Fin 3) :
    Decidable (onFaceΔ2_strict N b j) := by
  unfold onFaceΔ2_strict; infer_instance

/-- **Lifted Sperner condition**: `cN2_total` satisfies `IsSpernerColoring`
    with respect to the strict face predicate. This is precisely the
    `_hSperner` hypothesis of `Triangulation.boundary_doors_odd`. -/
private lemma cN2_total_isSpernerColoring :
    Triangulation.IsSpernerColoring (cN2_total N hN f hf_map) (onFaceΔ2_strict N) := by
  intro b j hstrict
  obtain ⟨hb, hface⟩ := hstrict
  rw [cN2_total_eq N hN f hf_map b hb]
  exact cN2_ne_of_onFace N hN f hf_map b hb j hface

end N2Grid

-- ============================================================
-- SECTION VII: Vertex range bound for topSimps2
-- (f-independent; useful for downstream wrapper lifts)
-- ============================================================

section N2VertexRange

/-- All three vertices of `t1 b` are bounded by the base `b`'s sum + 1. -/
private lemma t1_vertex_sum_le (b : ℕ × ℕ) (v : ℕ × ℕ) (hv : v ∈ t1 b) :
    v.1 + v.2 ≤ b.1 + b.2 + 1 := by
  simp only [t1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

/-- All three vertices of `t2 b` are bounded by the base `b`'s sum + 2. -/
private lemma t2_vertex_sum_le (b : ℕ × ℕ) (v : ℕ × ℕ) (hv : v ∈ t2 b) :
    v.1 + v.2 ≤ b.1 + b.2 + 2 := by
  simp only [t2, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

/-- Every vertex of every top simplex in `topSimps2 N` satisfies
    `v.1 + v.2 ≤ N`. This is the in-range condition used by `cN2_total_eq`
    to switch from the wrapper to the underlying `cN2`. -/
private lemma topSimps2_vertex_in_range (N : ℕ) {s : Finset (ℕ × ℕ)}
    (hs : s ∈ topSimps2 N) {v : ℕ × ℕ} (hv : v ∈ s) :
    v.1 + v.2 ≤ N := by
  simp only [topSimps2, Finset.mem_union, Finset.mem_image] at hs
  rcases hs with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩
  · -- Type-1: base in t1Bases means b.1+b.2 < N, vertices ≤ b.1+b.2+1 ≤ N
    simp only [t1Bases, Finset.mem_filter] at hb
    have h1 := t1_vertex_sum_le b v hv
    omega
  · -- Type-2: base in t2Bases means b.1+b.2+1 < N, vertices ≤ b.1+b.2+2 ≤ N
    simp only [t2Bases, Finset.mem_filter] at hb
    have h1 := t2_vertex_sum_le b v hv
    omega

end N2VertexRange

-- ============================================================
-- SECTION VIII: gridPt per-coordinate diameter bounds
-- (S26-prep, f-independent: pairwise per-coordinate distances between
-- vertices of a single top simplex in `topSimps2 N`. Feeds the
-- real-coordinate diameter conclusion `|v i l - v j l| ≤ 2/N` of
-- `sperner_panchromatic_two`. Independent of in-flight S23 PR #17571
-- (color-side wiring) and S25-prep PR #17621 (explicit gridPt
-- coordinate values) — added in a new section between
-- `N2VertexRange` and `end SpernerFreudSimp`, no overlap with either.)
-- ============================================================

section N2GridDiameter

variable (N : ℕ) (hN : 0 < N)

/-- Closed form for the coordinate-0 difference of two `gridPt` values:
the ℕ difference of the first coordinates divided by `N`. -/
private lemma gridPt_coord0_diff (b₁ b₂ : ℕ × ℕ) :
    gridPt N b₁ 0 - gridPt N b₂ 0 = ((b₁.1 : ℝ) - b₂.1) / N := by
  simp only [gridPt, show (0:Fin 3).val = 0 from rfl, ↓reduceIte]
  ring

/-- Closed form for the coordinate-1 difference of two `gridPt` values:
the ℕ difference of the second coordinates divided by `N`. -/
private lemma gridPt_coord1_diff (b₁ b₂ : ℕ × ℕ) :
    gridPt N b₁ 1 - gridPt N b₂ 1 = ((b₁.2 : ℝ) - b₂.2) / N := by
  simp only [gridPt, show (1:Fin 3).val = 1 from rfl,
             show ¬(1:ℕ) = 0 from by omega, ↓reduceIte]
  ring

/-- Closed form for the coordinate-2 difference of two `gridPt` values:
the reverse-sign ℕ difference of the coordinate sums divided by `N`.
(Coordinate 2 of `gridPt N b` is `(N - b.1 - b.2)/N`, so increasing the
sum decreases the value.) -/
private lemma gridPt_coord2_diff (b₁ b₂ : ℕ × ℕ) :
    gridPt N b₁ 2 - gridPt N b₂ 2 =
      (((b₂.1 : ℝ) + b₂.2) - ((b₁.1 : ℝ) + b₁.2)) / N := by
  simp only [gridPt, show (2:Fin 3).val = 2 from rfl,
             show ¬(2:ℕ) = 0 from by omega, show ¬(2:ℕ) = 1 from by omega,
             ↓reduceIte]
  ring

/-- First-coordinate range bound for `t1 b` vertices: `b.1 ≤ v.1 ≤ b.1 + 1`. -/
private lemma t1_vertex_first_coord_range (b v : ℕ × ℕ) (hv : v ∈ t1 b) :
    b.1 ≤ v.1 ∧ v.1 ≤ b.1 + 1 := by
  simp only [t1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

/-- Second-coordinate range bound for `t1 b` vertices: `b.2 ≤ v.2 ≤ b.2 + 1`. -/
private lemma t1_vertex_second_coord_range (b v : ℕ × ℕ) (hv : v ∈ t1 b) :
    b.2 ≤ v.2 ∧ v.2 ≤ b.2 + 1 := by
  simp only [t1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

/-- Coordinate-sum range bound for `t1 b` vertices:
`b.1 + b.2 ≤ v.1 + v.2 ≤ b.1 + b.2 + 1`. The upper half coincides with the
existing `t1_vertex_sum_le`; the lower half is new (the diagonal vertex
realises the lower bound). -/
private lemma t1_vertex_sum_coord_range (b v : ℕ × ℕ) (hv : v ∈ t1 b) :
    b.1 + b.2 ≤ v.1 + v.2 ∧ v.1 + v.2 ≤ b.1 + b.2 + 1 := by
  simp only [t1, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

/-- First-coordinate range bound for `t2 b` vertices: `b.1 ≤ v.1 ≤ b.1 + 1`. -/
private lemma t2_vertex_first_coord_range (b v : ℕ × ℕ) (hv : v ∈ t2 b) :
    b.1 ≤ v.1 ∧ v.1 ≤ b.1 + 1 := by
  simp only [t2, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

/-- Second-coordinate range bound for `t2 b` vertices: `b.2 ≤ v.2 ≤ b.2 + 1`. -/
private lemma t2_vertex_second_coord_range (b v : ℕ × ℕ) (hv : v ∈ t2 b) :
    b.2 ≤ v.2 ∧ v.2 ≤ b.2 + 1 := by
  simp only [t2, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

/-- Coordinate-sum range bound for `t2 b` vertices:
`b.1 + b.2 + 1 ≤ v.1 + v.2 ≤ b.1 + b.2 + 2`. The upper-corner vertex
`(b.1+1, b.2+1)` realises the upper bound; the two edge vertices realise
the lower bound. -/
private lemma t2_vertex_sum_coord_range (b v : ℕ × ℕ) (hv : v ∈ t2 b) :
    b.1 + b.2 + 1 ≤ v.1 + v.2 ∧ v.1 + v.2 ≤ b.1 + b.2 + 2 := by
  simp only [t2, Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl <;> omega

include hN

/-- Per-coordinate gridPt diameter within `t1 b` is bounded by `1/N`. Any
two vertices of a single `t1` cell differ in each coordinate by at most
`1/N`, because each ℕ coordinate (and the coordinate sum) varies over a
unit interval among the three vertices `{(b.1+1, b.2), (b.1, b.2+1), b}`. -/
private lemma gridPt_t1_coord_diameter (b b₁ b₂ : ℕ × ℕ)
    (hb₁ : b₁ ∈ t1 b) (hb₂ : b₂ ∈ t1 b) (l : Fin 3) :
    |gridPt N b₁ l - gridPt N b₂ l| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  fin_cases l
  · -- l = 0: first-coordinate difference
    show |gridPt N b₁ (0 : Fin 3) - gridPt N b₂ (0 : Fin 3)| ≤ 1 / N
    rw [gridPt_coord0_diff, abs_div, abs_of_pos hNr]
    have h₁ := t1_vertex_first_coord_range b b₁ hb₁
    have h₂ := t1_vertex_first_coord_range b b₂ hb₂
    have hnum : |(b₁.1 : ℝ) - b₂.1| ≤ 1 := by
      have h₁lo : (b.1 : ℝ) ≤ b₁.1 := by exact_mod_cast h₁.1
      have h₁hi : (b₁.1 : ℝ) ≤ (b.1 : ℝ) + 1 := by exact_mod_cast h₁.2
      have h₂lo : (b.1 : ℝ) ≤ b₂.1 := by exact_mod_cast h₂.1
      have h₂hi : (b₂.1 : ℝ) ≤ (b.1 : ℝ) + 1 := by exact_mod_cast h₂.2
      rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    exact div_le_div_of_nonneg_right hnum hNr.le
  · -- l = 1: second-coordinate difference
    show |gridPt N b₁ (1 : Fin 3) - gridPt N b₂ (1 : Fin 3)| ≤ 1 / N
    rw [gridPt_coord1_diff, abs_div, abs_of_pos hNr]
    have h₁ := t1_vertex_second_coord_range b b₁ hb₁
    have h₂ := t1_vertex_second_coord_range b b₂ hb₂
    have hnum : |(b₁.2 : ℝ) - b₂.2| ≤ 1 := by
      have h₁lo : (b.2 : ℝ) ≤ b₁.2 := by exact_mod_cast h₁.1
      have h₁hi : (b₁.2 : ℝ) ≤ (b.2 : ℝ) + 1 := by exact_mod_cast h₁.2
      have h₂lo : (b.2 : ℝ) ≤ b₂.2 := by exact_mod_cast h₂.1
      have h₂hi : (b₂.2 : ℝ) ≤ (b.2 : ℝ) + 1 := by exact_mod_cast h₂.2
      rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    exact div_le_div_of_nonneg_right hnum hNr.le
  · -- l = 2: third-coordinate difference (via coordinate-sum range)
    show |gridPt N b₁ (2 : Fin 3) - gridPt N b₂ (2 : Fin 3)| ≤ 1 / N
    rw [gridPt_coord2_diff, abs_div, abs_of_pos hNr]
    have h₁ := t1_vertex_sum_coord_range b b₁ hb₁
    have h₂ := t1_vertex_sum_coord_range b b₂ hb₂
    have hnum :
        |((b₂.1 : ℝ) + b₂.2) - ((b₁.1 : ℝ) + b₁.2)| ≤ 1 := by
      have h₁lo : (b.1 : ℝ) + b.2 ≤ (b₁.1 : ℝ) + b₁.2 := by exact_mod_cast h₁.1
      have h₁hi : (b₁.1 : ℝ) + b₁.2 ≤ (b.1 : ℝ) + b.2 + 1 := by exact_mod_cast h₁.2
      have h₂lo : (b.1 : ℝ) + b.2 ≤ (b₂.1 : ℝ) + b₂.2 := by exact_mod_cast h₂.1
      have h₂hi : (b₂.1 : ℝ) + b₂.2 ≤ (b.1 : ℝ) + b.2 + 1 := by exact_mod_cast h₂.2
      rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    exact div_le_div_of_nonneg_right hnum hNr.le

/-- Per-coordinate gridPt diameter within `t2 b` is bounded by `1/N`. Same
shape as `gridPt_t1_coord_diameter` but with the `t2`-vertex bounds (the
coordinate-sum interval is now `[b.1+b.2+1, b.1+b.2+2]`). -/
private lemma gridPt_t2_coord_diameter (b b₁ b₂ : ℕ × ℕ)
    (hb₁ : b₁ ∈ t2 b) (hb₂ : b₂ ∈ t2 b) (l : Fin 3) :
    |gridPt N b₁ l - gridPt N b₂ l| ≤ 1 / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  fin_cases l
  · show |gridPt N b₁ (0 : Fin 3) - gridPt N b₂ (0 : Fin 3)| ≤ 1 / N
    rw [gridPt_coord0_diff, abs_div, abs_of_pos hNr]
    have h₁ := t2_vertex_first_coord_range b b₁ hb₁
    have h₂ := t2_vertex_first_coord_range b b₂ hb₂
    have hnum : |(b₁.1 : ℝ) - b₂.1| ≤ 1 := by
      have h₁lo : (b.1 : ℝ) ≤ b₁.1 := by exact_mod_cast h₁.1
      have h₁hi : (b₁.1 : ℝ) ≤ (b.1 : ℝ) + 1 := by exact_mod_cast h₁.2
      have h₂lo : (b.1 : ℝ) ≤ b₂.1 := by exact_mod_cast h₂.1
      have h₂hi : (b₂.1 : ℝ) ≤ (b.1 : ℝ) + 1 := by exact_mod_cast h₂.2
      rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    exact div_le_div_of_nonneg_right hnum hNr.le
  · show |gridPt N b₁ (1 : Fin 3) - gridPt N b₂ (1 : Fin 3)| ≤ 1 / N
    rw [gridPt_coord1_diff, abs_div, abs_of_pos hNr]
    have h₁ := t2_vertex_second_coord_range b b₁ hb₁
    have h₂ := t2_vertex_second_coord_range b b₂ hb₂
    have hnum : |(b₁.2 : ℝ) - b₂.2| ≤ 1 := by
      have h₁lo : (b.2 : ℝ) ≤ b₁.2 := by exact_mod_cast h₁.1
      have h₁hi : (b₁.2 : ℝ) ≤ (b.2 : ℝ) + 1 := by exact_mod_cast h₁.2
      have h₂lo : (b.2 : ℝ) ≤ b₂.2 := by exact_mod_cast h₂.1
      have h₂hi : (b₂.2 : ℝ) ≤ (b.2 : ℝ) + 1 := by exact_mod_cast h₂.2
      rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    exact div_le_div_of_nonneg_right hnum hNr.le
  · show |gridPt N b₁ (2 : Fin 3) - gridPt N b₂ (2 : Fin 3)| ≤ 1 / N
    rw [gridPt_coord2_diff, abs_div, abs_of_pos hNr]
    have h₁ := t2_vertex_sum_coord_range b b₁ hb₁
    have h₂ := t2_vertex_sum_coord_range b b₂ hb₂
    have hnum :
        |((b₂.1 : ℝ) + b₂.2) - ((b₁.1 : ℝ) + b₁.2)| ≤ 1 := by
      have h₁lo : (b.1 : ℝ) + b.2 + 1 ≤ (b₁.1 : ℝ) + b₁.2 := by exact_mod_cast h₁.1
      have h₁hi : (b₁.1 : ℝ) + b₁.2 ≤ (b.1 : ℝ) + b.2 + 2 := by exact_mod_cast h₁.2
      have h₂lo : (b.1 : ℝ) + b.2 + 1 ≤ (b₂.1 : ℝ) + b₂.2 := by exact_mod_cast h₂.1
      have h₂hi : (b₂.1 : ℝ) + b₂.2 ≤ (b.1 : ℝ) + b.2 + 2 := by exact_mod_cast h₂.2
      rw [abs_le]; refine ⟨?_, ?_⟩ <;> linarith
    exact div_le_div_of_nonneg_right hnum hNr.le

/-- Per-coordinate gridPt diameter within any `s ∈ topSimps2 N` is bounded
by `2/N`. This is the form matching `sperner_panchromatic_two`'s
real-coordinate conclusion `|v i l - v j l| ≤ 2/N`; the underlying tight
bound is `1/N` (via `gridPt_t1_coord_diameter` / `gridPt_t2_coord_diameter`).
The factor-of-2 slack is harmless and matches the abstract axiom shape
`diameter ≤ n/N` (here `n = 2`). -/
private lemma gridPt_topSimps2_coord_diameter
    (s : Finset (ℕ × ℕ)) (hs : s ∈ topSimps2 N)
    (b₁ b₂ : ℕ × ℕ) (hb₁ : b₁ ∈ s) (hb₂ : b₂ ∈ s) (l : Fin 3) :
    |gridPt N b₁ l - gridPt N b₂ l| ≤ 2 / N := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h12 : (1 : ℝ) / N ≤ 2 / N :=
    div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) hNr.le
  simp only [topSimps2, Finset.mem_union, Finset.mem_image] at hs
  rcases hs with ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩
  · exact (gridPt_t1_coord_diameter N hN c b₁ b₂ hb₁ hb₂ l).trans h12
  · exact (gridPt_t2_coord_diameter N hN c b₁ b₂ hb₁ hb₂ l).trans h12

end N2GridDiameter

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
  rw [Finset.eq_empty_iff_forall_notMem]
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

-- ============================================================
-- SECTION VIII: Boundary-edge characterization for the n=2
-- Type-1/Type-2 triangulation
-- (Session 16 — infrastructure for `_hBoundaryOnFace`)
-- ============================================================

/-! ## Boundary-Edge Characterization

For the `simData2` triangulation of Δ² (Type-1 + Type-2 simplices),
a codim-1 face (edge) lies on the boundary precisely when it is
contained in only one top simplex. Each Type-1 simplex `t1 b` has
three edges (the codim-1 faces, i.e., 2-element subsets):

* **Diagonal**: `{(b.1, b.2+1), (b.1+1, b.2)}` — opposite the
  smallest vertex `b`.
* **Horizontal**: `{b, (b.1+1, b.2)}` — opposite `(b.1, b.2+1)`.
* **Vertical**: `{b, (b.1, b.2+1)}` — opposite `(b.1+1, b.2)`.

The lemmas here characterize, for each edge type, the unique base
of the *other* simplex that could contain it (a Type-2 base in
each case). When the resulting base is invalid for `t2Bases`, the
edge lies on the boundary of Δ². -/

namespace SpernerFreudSimp
section N2BoundaryAnalysis

-- Each t1 base is distinct from any t2 cell (`t1 b` always contains
-- the smallest vertex `b`, which `t2 c` never contains).
private lemma t1_ne_t2 (b c : ℕ × ℕ) : t1 b ≠ t2 c := by
  intro h
  have h1 : b ∈ t2 c := by rw [← h]; simp [t1]
  have h2 : (b.1 + 1, b.2) ∈ t2 c := by rw [← h]; simp [t1]
  have h3 : (b.1, b.2 + 1) ∈ t2 c := by rw [← h]; simp [t1]
  simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff] at h1 h2 h3
  omega

-- For two distinct vertices u, v, if both are in t1(b) ∩ t2(c), the
-- bases b, c are forced. Combined with `t1_unique_base` and
-- `t2_unique_base`, this gives full container characterization.
private lemma diagonal_in_t1_iff (b c : ℕ × ℕ) :
    ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t1 c ↔ c = b := by
  refine ⟨fun h => ?_, ?_⟩
  · -- Forward: if both diagonal vertices are in t1(c), unique-base gives c = b.
    have hne : ((b.1, b.2+1) : ℕ × ℕ) ≠ (b.1+1, b.2) := by
      intro heq; simp [Prod.mk.injEq, Prod.ext_iff] at heq
    -- Both vertices of t1(b) and of t1(c)
    have hb_diag : ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t1 b := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;>
        · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
          first | omega | tauto
    -- t1_unique_base gives `c = b` directly.
    exact t1_unique_base hne h hb_diag
  · rintro rfl
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
        first | omega | tauto

-- The "diagonal" edge of t1(b) is contained in t2(c) iff c = b.
private lemma diagonal_in_t2_iff (b c : ℕ × ℕ) :
    ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t2 c ↔ c = b := by
  refine ⟨fun h => ?_, ?_⟩
  · have hu : (b.1, b.2+1) ∈ t2 c := h (by simp)
    have hv : (b.1+1, b.2) ∈ t2 c := h (by simp)
    -- t2 c = {(c.1+1, c.2+1), (c.1+1, c.2), (c.1, c.2+1)}; both vertices match
    -- forces c.1 = b.1 and c.2 = b.2.
    simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff] at hu hv
    -- u = (b.1, b.2+1) and v = (b.1+1, b.2). Each ∈ {3 vertices}.
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv <;>
      first
        | (exact Prod.ext_iff.mpr ⟨by omega, by omega⟩)
        | (exfalso; omega)
  · rintro rfl
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp [t2]

-- The "horizontal" edge `{b, (b.1+1, b.2)}` of t1(b) is contained
-- in t2(c) iff c = (b.1, b.2 - 1) and b.2 ≥ 1. (For b.2 = 0 the
-- edge lies on the y=0 boundary of Δ² and no t2 contains it.)
private lemma horizontal_in_t2_pos (b : ℕ × ℕ) (hb2 : 1 ≤ b.2) :
    ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t2 (b.1, b.2 - 1) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff,
                 true_and]
      omega

-- The "vertical" edge `{b, (b.1, b.2+1)}` of t1(b) is contained
-- in t2(c) iff c = (b.1 - 1, b.2) and b.1 ≥ 1.
private lemma vertical_in_t2_pos (b : ℕ × ℕ) (hb1 : 1 ≤ b.1) :
    ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t2 (b.1 - 1, b.2) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff,
                 true_and, and_true]
      omega

-- When b.2 = 0, no t2 cell contains the horizontal edge `{b, (b.1+1, b.2)}`.
private lemma horizontal_not_in_t2_at_y0 (b : ℕ × ℕ) (hb2 : b.2 = 0) (c : ℕ × ℕ) :
    ¬ (({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t2 c) := by
  intro h
  -- Both b and (b.1+1, b.2) are in t2 c = {(c.1+1, c.2+1), (c.1+1, c.2), (c.1, c.2+1)}.
  -- Each of these three vertices has its second coordinate ≥ 1 except (c.1+1, c.2)
  -- and (c.1, c.2+1)'s second coordinate equals c.2 or c.2+1.
  -- Actually: (c.1+1, c.2+1).2 = c.2 + 1 ≥ 1; (c.1+1, c.2).2 = c.2; (c.1, c.2+1).2 = c.2 + 1 ≥ 1.
  -- So the only vertex with second coord = 0 is (c.1+1, 0), forcing c.2 = 0. Then
  -- t2 c = {(c.1+1, 1), (c.1+1, 0), (c.1, 1)}. Exactly one vertex with second coord 0.
  -- But we need TWO vertices with second coord 0 (b and (b.1+1, 0)). Contradiction.
  have hb_mem : b ∈ t2 c := h (by simp)
  have hbp_mem : (b.1+1, b.2) ∈ t2 c := h (by simp)
  simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff] at hb_mem hbp_mem
  -- b.2 = 0 forces b coordinates; b.1+1 differs from b.1
  rcases hb_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hbp_mem with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    omega

-- When b.1 = 0, no t2 cell contains the vertical edge `{b, (b.1, b.2+1)}`.
private lemma vertical_not_in_t2_at_x0 (b : ℕ × ℕ) (hb1 : b.1 = 0) (c : ℕ × ℕ) :
    ¬ (({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t2 c) := by
  intro h
  have hb_mem : b ∈ t2 c := h (by simp)
  have hbp_mem : (b.1, b.2+1) ∈ t2 c := h (by simp)
  simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff] at hb_mem hbp_mem
  rcases hb_mem with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rcases hbp_mem with ⟨h3, h4⟩ | ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    omega

-- ============================================================
-- t2 face containment: every face of every t2 cell is shared
-- with a t1 cell, so t2 cells contribute no boundary doors.
-- ============================================================

-- The "right side" edge of t2(b): the vertices v_1, v_2.
-- Equivalently: {(b.1+1, b.2), (b.1+1, b.2+1)}. Shared with t1(b.1+1, b.2).
private lemma t2_face0_in_t1 (b : ℕ × ℕ) :
    ({(b.1+1, b.2), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t1 (b.1+1, b.2) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
      first | omega | tauto

-- The "top side" edge of t2(b): vertices v_0, v_2.
-- Equivalently: {(b.1, b.2+1), (b.1+1, b.2+1)}. Shared with t1(b.1, b.2+1).
private lemma t2_face1_in_t1 (b : ℕ × ℕ) :
    ({(b.1, b.2+1), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t1 (b.1, b.2+1) := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
      first | omega | tauto

-- The "diagonal" edge of t2(b): vertices v_0, v_1.
-- Equivalently: {(b.1, b.2+1), (b.1+1, b.2)} = the diagonal of t1(b) too.
-- Shared with t1(b).
private lemma t2_face2_in_t1 (b : ℕ × ℕ) :
    ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t1 b := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
      first | omega | tauto

-- ============================================================
-- (Session 17) Boundary classification — base ↔ topSimps2 bridge
--
-- These lemmas characterize when each face of a t1/t2 cell is a
-- boundary face of Δ², i.e. when no other top simplex of the
-- triangulation contains it. They build on the S16 edge-containment
-- lemmas and the t1Bases / t2Bases membership conditions.
-- ============================================================

-- ----------------------------------------------------------------
-- (S17.1) Base-membership iff. Bare-`Finset.mem_filter` unfolding
-- gives an unwieldy product blob; the iff form is a cleaner rewrite
-- target for downstream boundary classification.
-- ----------------------------------------------------------------

private lemma t1Bases_mem_iff (N : ℕ) (b : ℕ × ℕ) :
    b ∈ t1Bases N ↔ b.1 < N ∧ b.2 < N ∧ b.1 + b.2 < N := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩
  · simp only [t1Bases, Finset.mem_filter, Finset.mem_product,
               Finset.mem_range] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · simp only [t1Bases, Finset.mem_filter, Finset.mem_product,
               Finset.mem_range]
    exact ⟨⟨h1, h2⟩, h3⟩

private lemma t2Bases_mem_iff (N : ℕ) (b : ℕ × ℕ) :
    b ∈ t2Bases N ↔ b.1 < N ∧ b.2 < N ∧ b.1 + b.2 + 1 < N := by
  refine ⟨fun h => ?_, fun ⟨h1, h2, h3⟩ => ?_⟩
  · simp only [t2Bases, Finset.mem_filter, Finset.mem_product,
               Finset.mem_range] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  · simp only [t2Bases, Finset.mem_filter, Finset.mem_product,
               Finset.mem_range]
    exact ⟨⟨h1, h2⟩, h3⟩

-- ----------------------------------------------------------------
-- (S17.2) topSimps2 membership of t1/t2 cells from base membership.
-- ----------------------------------------------------------------

private lemma t1_in_topSimps2_of_base (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t1Bases N) : t1 b ∈ topSimps2 N := by
  unfold topSimps2
  exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨b, hb, rfl⟩))

private lemma t2_in_topSimps2_of_base (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t2Bases N) : t2 b ∈ topSimps2 N := by
  unfold topSimps2
  exact Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨b, hb, rfl⟩))

-- (S17.3) Reverse: every cell in topSimps2 is t1 or t2 of some base.
private lemma topSimps2_mem_iff (N : ℕ) (s : Finset (ℕ × ℕ)) :
    s ∈ topSimps2 N ↔
      (∃ b ∈ t1Bases N, t1 b = s) ∨ (∃ b ∈ t2Bases N, t2 b = s) := by
  unfold topSimps2
  simp only [Finset.mem_union, Finset.mem_image]

-- ----------------------------------------------------------------
-- (S17.4) Base translation across t2 ↔ t1 face-mates.
--
-- For every t2 cell with base in `t2Bases N`, the three t1 cells
-- sharing its three faces (per S16's `t2_face{0,1,2}_in_t1`) all
-- have their bases in `t1Bases N`. Hence every t2 face is shared
-- with another top simplex — t2 faces are *never* boundary.
-- ----------------------------------------------------------------

private lemma t2Bases_self_in_t1Bases (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t2Bases N) : b ∈ t1Bases N := by
  rw [t1Bases_mem_iff]
  rw [t2Bases_mem_iff] at hb
  exact ⟨hb.1, hb.2.1, by omega⟩

private lemma t2Bases_right_in_t1Bases (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t2Bases N) : (b.1 + 1, b.2) ∈ t1Bases N := by
  rw [t1Bases_mem_iff]
  rw [t2Bases_mem_iff] at hb
  refine ⟨?_, hb.2.1, ?_⟩ <;> omega

private lemma t2Bases_top_in_t1Bases (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t2Bases N) : (b.1, b.2 + 1) ∈ t1Bases N := by
  rw [t1Bases_mem_iff]
  rw [t2Bases_mem_iff] at hb
  refine ⟨hb.1, ?_, ?_⟩ <;> omega

-- ----------------------------------------------------------------
-- (S17.5) Base translation across t1 ↔ t2 face-mates.
--
-- For a t1 cell with base `b ∈ t1Bases`, its three faces are:
--   * diagonal {(b.1, b.2+1), (b.1+1, b.2)} — shared with t2(b)
--     iff b ∈ t2Bases (i.e. b.1 + b.2 + 1 < N)
--   * horizontal {b, (b.1+1, b.2)} — shared with t2(b.1, b.2-1)
--     iff b.2 ≥ 1
--   * vertical {b, (b.1, b.2+1)} — shared with t2(b.1-1, b.2)
--     iff b.1 ≥ 1
-- The lemmas below give the existential side of these
-- characterizations; the negative side comes from S16 via
-- `horizontal_not_in_t2_at_y0`, `vertical_not_in_t2_at_x0`, and
-- the new `diagonal_not_in_t2_at_diagonal` below.
-- ----------------------------------------------------------------

private lemma t1Bases_horizontal_neighbor_in_t2Bases
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb2 : 1 ≤ b.2) :
    (b.1, b.2 - 1) ∈ t2Bases N := by
  rw [t1Bases_mem_iff] at hb
  rw [t2Bases_mem_iff]
  refine ⟨hb.1, ?_, ?_⟩ <;> omega

private lemma t1Bases_vertical_neighbor_in_t2Bases
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb1 : 1 ≤ b.1) :
    (b.1 - 1, b.2) ∈ t2Bases N := by
  rw [t1Bases_mem_iff] at hb
  rw [t2Bases_mem_iff]
  refine ⟨?_, hb.2.1, ?_⟩ <;> omega

private lemma t1Bases_diagonal_neighbor_in_t2Bases
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hbd : b.1 + b.2 + 1 < N) :
    b ∈ t2Bases N := by
  rw [t1Bases_mem_iff] at hb
  rw [t2Bases_mem_iff]
  exact ⟨hb.1, hb.2.1, hbd⟩

-- ----------------------------------------------------------------
-- (S17.6) The missing boundary case — diagonal at the diag-boundary.
--
-- Counterpart to `horizontal_not_in_t2_at_y0` and
-- `vertical_not_in_t2_at_x0`: when `b ∈ t1Bases N` saturates the
-- diagonal-boundary `b.1 + b.2 + 1 ≥ N`, no t2 cell with base in
-- `t2Bases N` contains the diagonal of t1(b).
-- ----------------------------------------------------------------

private lemma diagonal_not_in_t2_at_diagonal (N : ℕ) (b : ℕ × ℕ)
    (hbd : N ≤ b.1 + b.2 + 1) (c : ℕ × ℕ) (hc : c ∈ t2Bases N) :
    ¬ (({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t2 c) := by
  intro h
  rw [diagonal_in_t2_iff] at h
  rw [t2Bases_mem_iff] at hc
  -- h : c = b ⇒ b.1 + b.2 + 1 < N, contradicting hbd
  subst h
  omega

-- ----------------------------------------------------------------
-- (S17.7) Diagonal-neighbor classification at topSimps2 level.
--
-- For `b ∈ t1Bases N`, the diagonal edge of `t1 b` is contained in
-- *some other* simplex of `topSimps2 N` iff `b ∈ t2Bases N`
-- (equivalently `b.1 + b.2 + 1 < N`), and that other simplex is
-- `t2 b`. This is the form needed by S18's `containersOf`-based
-- assembly of `_hBoundaryOnFace` for the diagonal face.
-- ----------------------------------------------------------------

private lemma diagonal_neighbor_topSimps2 (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t1Bases N) :
    (∃ s ∈ topSimps2 N, s ≠ t1 b ∧
      ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s) ↔
      b.1 + b.2 + 1 < N := by
  refine ⟨?_, ?_⟩
  · rintro ⟨s, hs_mem, hs_ne, hs_sub⟩
    rw [topSimps2_mem_iff] at hs_mem
    rcases hs_mem with ⟨c, _, rfl⟩ | ⟨c, hc, rfl⟩
    · -- s = t1 c. Diagonal forces c = b ⇒ s = t1 b, contradicting hs_ne.
      rw [diagonal_in_t1_iff] at hs_sub
      subst hs_sub
      exact (hs_ne rfl).elim
    · -- s = t2 c with c ∈ t2Bases. Diagonal forces c = b.
      rw [diagonal_in_t2_iff] at hs_sub
      subst hs_sub
      rw [t2Bases_mem_iff] at hc
      exact hc.2.2
  · intro hbd
    refine ⟨t2 b, ?_, ?_, ?_⟩
    · exact t2_in_topSimps2_of_base N
        (t1Bases_diagonal_neighbor_in_t2Bases N hb hbd)
    · exact (t1_ne_t2 b b).symm
    · rw [diagonal_in_t2_iff]

-- ----------------------------------------------------------------
-- (S18) Boundary-edge container singletons + onFaceΔ2 witnesses.
--
-- These lemmas connect S16/S17's edge-membership building blocks to
-- the `_hBoundaryOnFace` hypothesis of `Triangulation.boundary_doors_odd`.
--
-- For each of the three edge types of a Type-1 cell `t1 b`, we prove:
--   (a) The boundary case: when the geometric boundary condition holds,
--       no other top simplex of `topSimps2 N` contains the edge — the
--       container set is exactly `{t1 b}`.
--   (b) The geometric witness: the two endpoints of the boundary edge
--       both satisfy the matching `onFaceΔ2 N · j` predicate, supplying
--       the `faceIdx` required by the existential in `_hBoundaryOnFace`.
--
-- Together with the t1 interior cases (covered by S17 and the symmetric
-- horizontal/vertical analogues) and the t2 face-share lemmas (S16 +
-- S17 base translations, future S18.b), these reduce `_hBoundaryOnFace`
-- for the n=2 triangulation to a straightforward case-split.
-- ----------------------------------------------------------------

-- (S18.1) Boundary diagonal: only t1 b contains the diagonal of t1 b
-- when b saturates the diag-boundary `N ≤ b.1 + b.2 + 1`.
private lemma diagonal_only_container_of_t1_boundary
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N)
    (hbd : N ≤ b.1 + b.2 + 1) :
    (topSimps2 N).filter
        (fun s => ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s) =
      ({t1 b} : Finset (Finset (ℕ × ℕ))) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hs_mem, hs_sub⟩ => ?_, ?_⟩
  · rw [topSimps2_mem_iff] at hs_mem
    rcases hs_mem with ⟨c, _, rfl⟩ | ⟨c, hc, rfl⟩
    · -- s = t1 c : diagonal forces c = b
      rw [diagonal_in_t1_iff] at hs_sub
      exact congrArg t1 hs_sub
    · -- s = t2 c with c ∈ t2Bases : diagonal forces c = b, but
      -- c ∈ t2Bases means c.1 + c.2 + 1 < N, contradicting hbd.
      exfalso
      rw [diagonal_in_t2_iff] at hs_sub
      subst hs_sub
      rw [t2Bases_mem_iff] at hc
      omega
  · rintro rfl
    exact ⟨t1_in_topSimps2_of_base N hb,
           (diagonal_in_t1_iff b b).mpr rfl⟩

-- (S18.2) Boundary horizontal: only t1 b contains its horizontal edge
-- when `b.2 = 0`.
private lemma horizontal_only_container_of_t1_boundary
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb2 : b.2 = 0) :
    (topSimps2 N).filter
        (fun s => ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s) =
      ({t1 b} : Finset (Finset (ℕ × ℕ))) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hs_mem, hs_sub⟩ => ?_, ?_⟩
  · rw [topSimps2_mem_iff] at hs_mem
    rcases hs_mem with ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩
    · -- s = t1 c : horizontal {b, (b.1+1, b.2)} ⊆ t1 c forces c = b
      -- via t1_unique_base (the two vertices are distinct since they
      -- differ in the first coordinate).
      have hne : (b : ℕ × ℕ) ≠ (b.1+1, b.2) := fun heq =>
        absurd (congrArg Prod.fst heq) (by omega)
      have hb_in_t1b : ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t1 b := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;>
          · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
            first | omega | tauto
      exact congrArg t1 (t1_unique_base hne hb_in_t1b hs_sub).symm
    · -- s = t2 c : excluded by horizontal_not_in_t2_at_y0 (b.2 = 0).
      exfalso
      exact horizontal_not_in_t2_at_y0 b hb2 c hs_sub
  · rintro rfl
    refine ⟨t1_in_topSimps2_of_base N hb, ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
        first | omega | tauto

-- (S18.3) Boundary vertical: only t1 b contains its vertical edge
-- when `b.1 = 0`.
private lemma vertical_only_container_of_t1_boundary
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb1 : b.1 = 0) :
    (topSimps2 N).filter
        (fun s => ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s) =
      ({t1 b} : Finset (Finset (ℕ × ℕ))) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_singleton]
  refine ⟨fun ⟨hs_mem, hs_sub⟩ => ?_, ?_⟩
  · rw [topSimps2_mem_iff] at hs_mem
    rcases hs_mem with ⟨c, _, rfl⟩ | ⟨c, _, rfl⟩
    · have hne : (b : ℕ × ℕ) ≠ (b.1, b.2+1) := fun heq =>
        absurd (congrArg Prod.snd heq) (by omega)
      have hb_in_t1b : ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t1 b := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;>
          · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
            first | omega | tauto
      exact congrArg t1 (t1_unique_base hne hb_in_t1b hs_sub).symm
    · exfalso
      exact vertical_not_in_t2_at_x0 b hb1 c hs_sub
  · rintro rfl
    refine ⟨t1_in_topSimps2_of_base N hb, ?_⟩
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;>
      · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
        first | omega | tauto

-- (S18.4) Cardinality corollaries: the three boundary cases above all
-- have container-card = 1, ready to feed `_hBoundaryOnFace` analysis.

private lemma diagonal_card_eq_one_of_t1_boundary
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N)
    (hbd : N ≤ b.1 + b.2 + 1) :
    ((topSimps2 N).filter
        (fun s => ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s)).card = 1 := by
  rw [diagonal_only_container_of_t1_boundary N hb hbd, Finset.card_singleton]

private lemma horizontal_card_eq_one_of_t1_boundary
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb2 : b.2 = 0) :
    ((topSimps2 N).filter
        (fun s => ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s)).card = 1 := by
  rw [horizontal_only_container_of_t1_boundary N hb hb2, Finset.card_singleton]

private lemma vertical_card_eq_one_of_t1_boundary
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb1 : b.1 = 0) :
    ((topSimps2 N).filter
        (fun s => ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s)).card = 1 := by
  rw [vertical_only_container_of_t1_boundary N hb hb1, Finset.card_singleton]

-- ----------------------------------------------------------------
-- (S18.5) onFaceΔ2 witnesses for boundary t1 edges.
--
-- For each boundary case, the two endpoints of the edge both satisfy
-- the appropriate `onFaceΔ2` predicate. These will supply the
-- `faceIdx` and the `∀ j ≠ k, ...` clause in the existential of
-- `_hBoundaryOnFace`.
-- ----------------------------------------------------------------

private lemma diagonal_endpoints_on_face2
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N)
    (hbd : N ≤ b.1 + b.2 + 1) :
    onFaceΔ2 N (b.1, b.2+1) 2 ∧ onFaceΔ2 N (b.1+1, b.2) 2 := by
  rw [t1Bases_mem_iff] at hb
  refine ⟨?_, ?_⟩
  · rw [onFaceΔ2_two_iff]; omega
  · rw [onFaceΔ2_two_iff]; omega

private lemma horizontal_endpoints_on_face1
    (N : ℕ) (b : ℕ × ℕ) (hb2 : b.2 = 0) :
    onFaceΔ2 N b 1 ∧ onFaceΔ2 N (b.1+1, b.2) 1 := by
  refine ⟨?_, ?_⟩
  · rw [onFaceΔ2_one_iff]; exact hb2
  · rw [onFaceΔ2_one_iff]; exact hb2

private lemma vertical_endpoints_on_face0
    (N : ℕ) (b : ℕ × ℕ) (hb1 : b.1 = 0) :
    onFaceΔ2 N b 0 ∧ onFaceΔ2 N (b.1, b.2+1) 0 := by
  refine ⟨?_, ?_⟩
  · rw [onFaceΔ2_zero_iff]; exact hb1
  · rw [onFaceΔ2_zero_iff]; exact hb1

-- ----------------------------------------------------------------
-- (S18 part 2) t2-face shared with t1: container card ≥ 2.
--
-- For `b ∈ t2Bases N`, every face of `t2 b` is shared with a t1
-- cell (per S16 `t2_face{0,1,2}_in_t1` + S17 `t2Bases_*_in_t1Bases`).
-- Hence the container set in `topSimps2 N` for any face of `t2 b`
-- contains both `t2 b` and a sharing t1 cell, giving card ≥ 2.
-- This *rules out* t2 faces from being boundary doors in
-- `_hBoundaryOnFace`, completing the t1/t2 dichotomy:
--
--   * t1 boundary edges (S18 part 1): container card = 1.
--   * t2 faces (S18 part 2): container card ≥ 2 (interior shared).
--   * t1 interior edges (diagonal/horizontal/vertical, non-boundary
--     positions): container card ≥ 2 via S17's
--     `diagonal_neighbor_topSimps2` + S16's `*_in_t2_pos`.
-- ----------------------------------------------------------------

-- Each face of `t2 b` is contained in `t2 b` itself (used as the
-- second container alongside the sharing t1 cell). These three
-- inclusions are pure unfolding + omega.

private lemma t2_face0_in_t2 (b : ℕ × ℕ) :
    ({(b.1+1, b.2), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t2 b := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
      first | omega | tauto

private lemma t2_face1_in_t2 (b : ℕ × ℕ) :
    ({(b.1, b.2+1), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t2 b := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
      first | omega | tauto

private lemma t2_face2_in_t2 (b : ℕ × ℕ) :
    ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t2 b := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl <;>
    · simp only [t2, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
      first | omega | tauto

-- Card-≥-2 lemmas: each t2 face has at least two containers in
-- `topSimps2 N` — `t2 b` itself and the sharing t1 cell.

private lemma t2_face0_card_ge_two (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t2Bases N) :
    2 ≤ ((topSimps2 N).filter
        (fun s => ({(b.1+1, b.2), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s)).card := by
  have h_t1_in : t1 (b.1+1, b.2) ∈ (topSimps2 N).filter
      (fun s => ({(b.1+1, b.2), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact t1_in_topSimps2_of_base N (t2Bases_right_in_t1Bases N hb)
    · exact t2_face0_in_t1 b
  have h_t2_in : t2 b ∈ (topSimps2 N).filter
      (fun s => ({(b.1+1, b.2), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact t2_in_topSimps2_of_base N hb
    · exact t2_face0_in_t2 b
  have h_ne : t1 (b.1+1, b.2) ≠ t2 b := t1_ne_t2 _ _
  have h_pair_card : ({t1 (b.1+1, b.2), t2 b} : Finset (Finset (ℕ × ℕ))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact h_ne),
        Finset.card_singleton]
  have h_pair_sub :
      ({t1 (b.1+1, b.2), t2 b} : Finset (Finset (ℕ × ℕ))) ⊆
        (topSimps2 N).filter
          (fun s => ({(b.1+1, b.2), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_t1_in
    · exact h_t2_in
  calc 2 = ({t1 (b.1+1, b.2), t2 b} : Finset (Finset (ℕ × ℕ))).card := h_pair_card.symm
    _ ≤ _ := Finset.card_le_card h_pair_sub

private lemma t2_face1_card_ge_two (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t2Bases N) :
    2 ≤ ((topSimps2 N).filter
        (fun s => ({(b.1, b.2+1), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s)).card := by
  have h_t1_in : t1 (b.1, b.2+1) ∈ (topSimps2 N).filter
      (fun s => ({(b.1, b.2+1), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact t1_in_topSimps2_of_base N (t2Bases_top_in_t1Bases N hb)
    · exact t2_face1_in_t1 b
  have h_t2_in : t2 b ∈ (topSimps2 N).filter
      (fun s => ({(b.1, b.2+1), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact t2_in_topSimps2_of_base N hb
    · exact t2_face1_in_t2 b
  have h_ne : t1 (b.1, b.2+1) ≠ t2 b := t1_ne_t2 _ _
  have h_pair_card : ({t1 (b.1, b.2+1), t2 b} : Finset (Finset (ℕ × ℕ))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact h_ne),
        Finset.card_singleton]
  have h_pair_sub :
      ({t1 (b.1, b.2+1), t2 b} : Finset (Finset (ℕ × ℕ))) ⊆
        (topSimps2 N).filter
          (fun s => ({(b.1, b.2+1), (b.1+1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_t1_in
    · exact h_t2_in
  calc 2 = ({t1 (b.1, b.2+1), t2 b} : Finset (Finset (ℕ × ℕ))).card := h_pair_card.symm
    _ ≤ _ := Finset.card_le_card h_pair_sub

private lemma t2_face2_card_ge_two (N : ℕ) {b : ℕ × ℕ}
    (hb : b ∈ t2Bases N) :
    2 ≤ ((topSimps2 N).filter
        (fun s => ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s)).card := by
  have h_t1_in : t1 b ∈ (topSimps2 N).filter
      (fun s => ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact t1_in_topSimps2_of_base N (t2Bases_self_in_t1Bases N hb)
    · exact t2_face2_in_t1 b
  have h_t2_in : t2 b ∈ (topSimps2 N).filter
      (fun s => ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s) := by
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact t2_in_topSimps2_of_base N hb
    · exact t2_face2_in_t2 b
  have h_ne : t1 b ≠ t2 b := t1_ne_t2 _ _
  have h_pair_card : ({t1 b, t2 b} : Finset (Finset (ℕ × ℕ))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by rw [Finset.mem_singleton]; exact h_ne),
        Finset.card_singleton]
  have h_pair_sub :
      ({t1 b, t2 b} : Finset (Finset (ℕ × ℕ))) ⊆
        (topSimps2 N).filter
          (fun s => ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h_t1_in
    · exact h_t2_in
  calc 2 = ({t1 b, t2 b} : Finset (Finset (ℕ × ℕ))).card := h_pair_card.symm
    _ ≤ _ := Finset.card_le_card h_pair_sub

end N2BoundaryAnalysis

-- ============================================================
-- (Session 18 part 2) Interior-face neighbor existentials.
--
-- Companion to S18 part 1's t1-boundary container singletons:
-- whereas part 1 covers the case when an edge of t1(b) has NO
-- other top-simplex container (geometric boundary cases:
--    diagonal at b.1+b.2+1 ≥ N, horizontal at b.2 = 0,
--    vertical at b.1 = 0),
-- this section covers the *interior* cases — when an edge of
-- a t1 or t2 cell DOES have another top-simplex container, and
-- explicitly produces the witness (`t2(face-mate)` or
-- `t1(face-mate)`).
--
-- Together these cover all six face/edge × cell-type
-- combinations needed by `_hBoundaryOnFace` for the n=2
-- triangulation:
--   * t1 cell, diagonal: S17 `diagonal_neighbor_topSimps2`
--                        (interior) + S18.1 (boundary)
--   * t1 cell, horizontal: S18.2.1 below (interior)
--                          + S18.1 (boundary)
--   * t1 cell, vertical:   S18.2.2 below (interior)
--                          + S18.1 (boundary)
--   * t2 cell, face0/1/2:  S18.2.3-5 below (always interior;
--                          t2 contributes no boundary doors)
-- ============================================================

-- NOTE (S33): redundant nested `namespace SpernerFreudSimp` re-open
-- removed here (see the matching note before N2HBoundaryOnFace).
section N2BoundaryInteriorNeighbors

-- ----------------------------------------------------------------
-- (S18.2.1) Interior horizontal: for `b ∈ t1Bases N` with
-- `b.2 ≥ 1`, the horizontal edge `{b, (b.1+1, b.2)}` of `t1 b`
-- is also contained in `t2 (b.1, b.2 - 1)`, which is a distinct
-- simplex of `topSimps2 N`.
-- ----------------------------------------------------------------

private lemma horizontal_neighbor_topSimps2
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb2 : 1 ≤ b.2) :
    ∃ s ∈ topSimps2 N, s ≠ t1 b ∧
      ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ s :=
  ⟨t2 (b.1, b.2 - 1),
   t2_in_topSimps2_of_base N (t1Bases_horizontal_neighbor_in_t2Bases N hb hb2),
   (t1_ne_t2 b (b.1, b.2 - 1)).symm,
   horizontal_in_t2_pos b hb2⟩

-- ----------------------------------------------------------------
-- (S18.2.2) Interior vertical: for `b ∈ t1Bases N` with
-- `b.1 ≥ 1`, the vertical edge `{b, (b.1, b.2+1)}` of `t1 b`
-- is also contained in `t2 (b.1 - 1, b.2)`, distinct from t1 b.
-- ----------------------------------------------------------------

private lemma vertical_neighbor_topSimps2
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N) (hb1 : 1 ≤ b.1) :
    ∃ s ∈ topSimps2 N, s ≠ t1 b ∧
      ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ s :=
  ⟨t2 (b.1 - 1, b.2),
   t2_in_topSimps2_of_base N (t1Bases_vertical_neighbor_in_t2Bases N hb hb1),
   (t1_ne_t2 b (b.1 - 1, b.2)).symm,
   vertical_in_t2_pos b hb1⟩

-- ----------------------------------------------------------------
-- (S18.2.3) t2 face0 ("right side") is always shared with a t1
-- cell. For `c ∈ t2Bases N`, the edge `{(c.1+1, c.2),
-- (c.1+1, c.2+1)}` is contained in `t1 (c.1+1, c.2)`, which is a
-- distinct simplex of `topSimps2 N`. Hence t2 cells contribute
-- no boundary doors via face0.
-- ----------------------------------------------------------------

private lemma t2_face0_neighbor_topSimps2
    (N : ℕ) {c : ℕ × ℕ} (hc : c ∈ t2Bases N) :
    ∃ s ∈ topSimps2 N, s ≠ t2 c ∧
      ({(c.1+1, c.2), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) ⊆ s :=
  ⟨t1 (c.1+1, c.2),
   t1_in_topSimps2_of_base N (t2Bases_right_in_t1Bases N hc),
   t1_ne_t2 (c.1+1, c.2) c,
   t2_face0_in_t1 c⟩

-- ----------------------------------------------------------------
-- (S18.2.4) t2 face1 ("top side") is always shared with a t1
-- cell. For `c ∈ t2Bases N`, the edge `{(c.1, c.2+1),
-- (c.1+1, c.2+1)}` is contained in `t1 (c.1, c.2+1)`, distinct
-- from t2 c.
-- ----------------------------------------------------------------

private lemma t2_face1_neighbor_topSimps2
    (N : ℕ) {c : ℕ × ℕ} (hc : c ∈ t2Bases N) :
    ∃ s ∈ topSimps2 N, s ≠ t2 c ∧
      ({(c.1, c.2+1), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) ⊆ s :=
  ⟨t1 (c.1, c.2+1),
   t1_in_topSimps2_of_base N (t2Bases_top_in_t1Bases N hc),
   t1_ne_t2 (c.1, c.2+1) c,
   t2_face1_in_t1 c⟩

-- ----------------------------------------------------------------
-- (S18.2.5) t2 face2 ("diagonal") is always shared with a t1
-- cell — specifically `t1 c` itself. For `c ∈ t2Bases N`, the
-- edge `{(c.1, c.2+1), (c.1+1, c.2)}` is contained in `t1 c`,
-- which is distinct from t2 c (different vertex sets).
-- ----------------------------------------------------------------

private lemma t2_face2_neighbor_topSimps2
    (N : ℕ) {c : ℕ × ℕ} (hc : c ∈ t2Bases N) :
    ∃ s ∈ topSimps2 N, s ≠ t2 c ∧
      ({(c.1, c.2+1), (c.1+1, c.2)} : Finset (ℕ × ℕ)) ⊆ s :=
  ⟨t1 c,
   t1_in_topSimps2_of_base N (t2Bases_self_in_t1Bases N hc),
   t1_ne_t2 c c,
   t2_face2_in_t1 c⟩

end N2BoundaryInteriorNeighbors

-- ============================================================
-- (Session 19 part 2) Concrete face computations for `simData2 N`.
--
-- For the `_hBoundaryOnFace` discharge of `simData2 N`, we need to
-- compute `(simData2 N).faceOf s hs k` once we know which vertex
-- of `s` is the `vertexEnum`-th. The S19.1 generic translation
-- `adjFn = none ↔ container card ≤ 1` plus the
-- `forall_vertex_ne_iff_forall_face_mem` bridge reduce
-- `_hBoundaryOnFace` to a pure case-split on the codim-1 face.
--
-- Since `vertexEnum (t1 b) hs k ∈ t1 b`, the removed vertex is one
-- of {b, (b.1, b.2+1), (b.1+1, b.2)} — in each case we compute
-- the resulting face explicitly. The same for `t2 c` with the
-- three vertices {(c.1+1, c.2), (c.1, c.2+1), (c.1+1, c.2+1)}.
--
-- These are 6 erase computations: pure Finset.ext + omega.
-- ============================================================

section N2FaceErase

-- ----------------------------------------------------------------
-- (S19.2.1) t1 b erases: removing each of the three vertices of
-- `t1 b` gives one of the three edges (vertical, horizontal,
-- diagonal). All three Finset equalities are pure ext+omega.
-- ----------------------------------------------------------------

/-- Removing `(b.1+1, b.2)` from `t1 b` gives the vertical edge. -/
private lemma t1_erase_first (b : ℕ × ℕ) :
    (t1 b).erase (b.1+1, b.2) = ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) := by
  ext x
  simp only [Finset.mem_erase, t1, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, h | h | h⟩
    · exact absurd h hne
    · right; exact h
    · left; exact h
  · rintro (rfl | rfl)
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).1 (by omega)
      · right; right; rfl
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).2 (by omega)
      · right; left; rfl

/-- Removing `(b.1, b.2+1)` from `t1 b` gives the horizontal edge. -/
private lemma t1_erase_second (b : ℕ × ℕ) :
    (t1 b).erase (b.1, b.2+1) = ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) := by
  ext x
  simp only [Finset.mem_erase, t1, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, h | h | h⟩
    · right; exact h
    · exact absurd h hne
    · left; exact h
  · rintro (rfl | rfl)
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).2 (by omega)
      · right; right; rfl
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).1 (by omega)
      · left; rfl

/-- Removing `b` from `t1 b` gives the diagonal edge. -/
private lemma t1_erase_third (b : ℕ × ℕ) :
    (t1 b).erase b = ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) := by
  ext x
  simp only [Finset.mem_erase, t1, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, h | h | h⟩
    · right; exact h
    · left; exact h
    · exact absurd h hne
  · rintro (rfl | rfl)
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).2 (by omega)
      · right; left; rfl
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).1 (by omega)
      · left; rfl

-- ----------------------------------------------------------------
-- (S19.2.2) t2 c erases: removing each of the three vertices of
-- `t2 c` gives one of the three edges (face0/face1/face2 in
-- the `t2_face*_in_t2` sense).
-- ----------------------------------------------------------------

/-- Removing `(c.1+1, c.2+1)` from `t2 c` gives face2 (the diagonal
edge of the t2 cell, which is also the diagonal edge of t1 c). -/
private lemma t2_erase_first (c : ℕ × ℕ) :
    (t2 c).erase (c.1+1, c.2+1) =
      ({(c.1, c.2+1), (c.1+1, c.2)} : Finset (ℕ × ℕ)) := by
  ext x
  simp only [Finset.mem_erase, t2, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, h | h | h⟩
    · exact absurd h hne
    · right; exact h
    · left; exact h
  · rintro (rfl | rfl)
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).1 (by omega)
      · right; right; rfl
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).2 (by omega)
      · right; left; rfl

/-- Removing `(c.1+1, c.2)` from `t2 c` gives face1 (the "top"
edge of the t2 cell). -/
private lemma t2_erase_second (c : ℕ × ℕ) :
    (t2 c).erase (c.1+1, c.2) =
      ({(c.1, c.2+1), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) := by
  ext x
  simp only [Finset.mem_erase, t2, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, h | h | h⟩
    · right; exact h
    · exact absurd h hne
    · left; exact h
  · rintro (rfl | rfl)
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).2 (by omega)
      · right; right; rfl
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).2 (by omega)
      · left; rfl

/-- Removing `(c.1, c.2+1)` from `t2 c` gives face0 (the "right"
edge of the t2 cell). -/
private lemma t2_erase_third (c : ℕ × ℕ) :
    (t2 c).erase (c.1, c.2+1) =
      ({(c.1+1, c.2), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) := by
  ext x
  simp only [Finset.mem_erase, t2, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne, h | h | h⟩
    · right; exact h
    · left; exact h
    · exact absurd h hne
  · rintro (rfl | rfl)
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).1 (by omega)
      · right; left; rfl
    · refine ⟨fun h => ?_, ?_⟩
      · exact absurd (Prod.ext_iff.mp h).1 (by omega)
      · left; rfl

end N2FaceErase

-- NOTE (S33): the `end SpernerFreudSimp` that used to sit here was
-- removed together with the redundant re-opens; the namespace opened
-- before `SimplicialAdjFnHelper`'s enclosing block now runs to the
-- file-final `end SpernerFreudSimp`, keeping every declaration —
-- including `SimplicialAdjFnHelper.*` — at its established name.

-- ============================================================
-- (Session 19 part 1) Generic `adjFn = none ↔ card ≤ 1` translation.
--
-- `AbstractSimplicialData.adjFn` (in `SpernerSimplicialInstance.lean`)
-- returns `none` precisely when the codim-1 face lies on the boundary
-- of the triangulation. Its definition uses a nested
--    if cs.card ≤ 1 then none
--    else if (cs.erase s).Nonempty then some _ else none
-- pattern, which is operationally correct but inconvenient for
-- case-split reasoning in `_hBoundaryOnFace` discharges.
--
-- This section provides a single clean iff translation:
--    `adjFn p k = none ↔ (containersOf (faceOf p.1 p.2 k)).card ≤ 1`
--
-- The proof uses `self_mem_containersOf` (so `cs.card ≥ 1` always)
-- and `card_erase_of_mem` (so `cs.erase p.1` has card `cs.card - 1`)
-- to show that the second `none`-branch of the inner `if` is
-- unreachable: `cs.card > 1` forces `cs.erase p.1` nonempty, hence
-- `adjFn` returns `some`. Equivalently, `adjFn = none ↔ cs.card = 1`
-- (the corollary below).
--
-- This is the abstract-level bridge that the n=2 `_hBoundaryOnFace`
-- proof (S19 part 2, future) and any other concrete
-- `Sperner-on-Triangulation` instance will consume to translate
-- "no adjacent simplex" into "the codim-1 face has only one
-- container" — exactly the form produced by S16-S18's geometric
-- container-card analysis (`*_only_container_of_t1_boundary`,
-- `*_card_eq_one_of_t1_boundary`).
-- ============================================================

namespace SimplicialAdjFnHelper

variable {V : Type} [DecidableEq V] [LinearOrder V] {n : ℕ}

/-- The generic translation: `adjFn p k = none` iff the container
set of the codim-1 face has cardinality at most 1.

The right-to-left direction takes the outer `if`-branch of `adjFn`.
The left-to-right direction proceeds by `split_ifs`: the case where
`cs.card > 1` and `cs.erase p.1` is empty is impossible, since
`p.1 ∈ cs` (via `self_mem_containersOf`) gives
`(cs.erase p.1).card = cs.card - 1 ≥ 1`. -/
lemma adjFn_eq_none_iff_card_le_one
    (D : Triangulation.AbstractSimplicialData V n)
    (p : { s : Finset V // s ∈ D.topSimplices })
    (k : Fin (n + 1)) :
    D.adjFn p k = none ↔
      (D.containersOf (D.faceOf p.1 p.2 k)).card ≤ 1 := by
  have h_self : p.1 ∈ D.containersOf (D.faceOf p.1 p.2 k) :=
    D.self_mem_containersOf p.1 p.2 k
  unfold Triangulation.AbstractSimplicialData.adjFn
  simp only
  split_ifs with hc hne
  · -- Outer `if` taken: cs.card ≤ 1; both sides hold.
    exact ⟨fun _ => hc, fun _ => rfl⟩
  · -- Outer skipped, inner taken: returns `some _`. LHS False, RHS False.
    exact ⟨fun h => h.elim, fun h => absurd h hc⟩
  · -- Outer skipped, inner skipped: contradicts `p.1 ∈ cs` + `cs.card > 1`.
    exfalso
    apply hne
    show ((D.containersOf (D.faceOf p.1 p.2 k)).erase p.1).Nonempty
    refine Finset.card_pos.mp ?_
    rw [Finset.card_erase_of_mem h_self]
    omega

/-- Corollary: `adjFn p k = none` iff the container set has card
exactly 1. Combines `adjFn_eq_none_iff_card_le_one` with the
`cs.card ≥ 1` lower bound from `self_mem_containersOf`. -/
lemma adjFn_eq_none_iff_card_eq_one
    (D : Triangulation.AbstractSimplicialData V n)
    (p : { s : Finset V // s ∈ D.topSimplices })
    (k : Fin (n + 1)) :
    D.adjFn p k = none ↔
      (D.containersOf (D.faceOf p.1 p.2 k)).card = 1 := by
  rw [adjFn_eq_none_iff_card_le_one]
  have h_pos : 0 < (D.containersOf (D.faceOf p.1 p.2 k)).card :=
    Finset.card_pos.mpr ⟨p.1, D.self_mem_containersOf p.1 p.2 k⟩
  omega

/-- Generic vertex-vs-face bridge: a predicate `P` holds for every
`vertexEnum s hs j` with `j ≠ k` iff it holds for every element of
the codim-1 face `faceOf s hs k`. The codim-1 face is exactly the
image of `Finset.univ.erase k` under `vertexEnum`, so this is a
direct reformulation via `vertexEnum_image_erase`.

This is the universal-quantifier shape that `_hBoundaryOnFace`
hypothesis of `Triangulation.boundary_doors_odd` requires —
`∀ j ≠ k, onFace (vertexEnum s hs j) faceIdx` — restated in
"face-content" terms suitable for case-splitting on `faceOf`. -/
lemma forall_vertex_ne_iff_forall_face_mem
    (D : Triangulation.AbstractSimplicialData V n)
    (s : Finset V) (hs : s ∈ D.topSimplices) (k : Fin (n + 1))
    (P : V → Prop) :
    (∀ j : Fin (n + 1), j ≠ k → P (D.vertexEnum s hs j)) ↔
    (∀ v ∈ D.faceOf s hs k, P v) := by
  constructor
  · intro h v hv
    rw [← D.vertexEnum_image_erase s hs k] at hv
    obtain ⟨j, hj_mem, rfl⟩ := Finset.mem_image.mp hv
    rw [Finset.mem_erase] at hj_mem
    exact h j hj_mem.1
  · intro h j hj_ne
    apply h
    rw [← D.vertexEnum_image_erase s hs k]
    exact Finset.mem_image.mpr ⟨j,
      Finset.mem_erase.mpr ⟨hj_ne, Finset.mem_univ j⟩, rfl⟩

/-- Generic `d = 2` characterization of `CellComplex.IsDoor`:
for a 2-dim cell complex with coloring `c : V → Fin 3`, the door
condition at face `k` says exactly that colors `0` and `1` both
appear among the non-`k` vertices.

`CellComplex.IsDoor` is defined as
`∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ c (K.vertex s i) = Fin.castSucc j`.
For `d = 2`, the inner quantifier ranges over `j : Fin 2 = {0, 1}`,
and `Fin.castSucc` lifts each reflexively into `Fin 3`, giving the
explicit color-existence conjunction below.

This is the abstract-level bridge consumed by `_hLastFace` discharges
that need to translate the door condition into concrete color
predicates on the codim-1 face vertices. For an `n = 2` Sperner
instance whose two non-`k` vertices both lie on geometric face `2`
(forcing both colors into `{0, 1}` by the Sperner condition), this
iff specialises further to "the two non-`k` vertices have different
colors", matching the `g k ≠ g (k + 1)` predicate of
`face2_path_odd`. -/
lemma isDoor_dim_two_iff
    {V : Type*} [DecidableEq V] (K : CellComplex V 2)
    (c : V → Fin 3) (s : K.Cell) (k : Fin 3) :
    CellComplex.IsDoor c K s k ↔
      (∃ i : Fin 3, i ≠ k ∧ c (K.vertex s i) = (0 : Fin 3)) ∧
      (∃ i : Fin 3, i ≠ k ∧ c (K.vertex s i) = (1 : Fin 3)) := by
  unfold CellComplex.IsDoor
  -- `Fin.castSucc (0 : Fin 2) = (0 : Fin 3)` and
  -- `Fin.castSucc (1 : Fin 2) = (1 : Fin 3)`, both by `Fin.ext rfl`.
  have h0_cast : ((0 : Fin 2).castSucc : Fin 3) = 0 := Fin.ext rfl
  have h1_cast : ((1 : Fin 2).castSucc : Fin 3) = 1 := Fin.ext rfl
  refine ⟨fun h => ⟨?_, ?_⟩, fun ⟨h0, h1⟩ j => ?_⟩
  · -- Forward direction, `j = 0`.
    obtain ⟨i, hi_ne, hi_color⟩ := h 0
    rw [h0_cast] at hi_color
    exact ⟨i, hi_ne, hi_color⟩
  · -- Forward direction, `j = 1`.
    obtain ⟨i, hi_ne, hi_color⟩ := h 1
    rw [h1_cast] at hi_color
    exact ⟨i, hi_ne, hi_color⟩
  · -- Reverse direction: case-split on `j : Fin 2`.
    fin_cases j
    · -- `j = 0`
      obtain ⟨i, hi_ne, hi_color⟩ := h0
      rw [← h0_cast] at hi_color
      exact ⟨i, hi_ne, hi_color⟩
    · -- `j = 1`
      obtain ⟨i, hi_ne, hi_color⟩ := h1
      rw [← h1_cast] at hi_color
      exact ⟨i, hi_ne, hi_color⟩

/-- Helper: in `Fin 3`, given two distinct indices `i₁, i₂` both
differing from a third index `k`, every fourth index `j` differing
from `k` equals one of `i₁` or `i₂`. Used to convert "every non-`k`
vertex" into "the two specific non-`k` vertices `i₁` and `i₂`" in the
proof of `isDoor_dim_two_iff_color_change_of_no_color_two`.

Proved by full enumeration over `Fin 3` with `decide`; all 81 (k, i₁,
i₂, j)-combinations are eliminated by the four hypotheses. -/
private lemma fin_three_other_eq :
    ∀ k i₁ i₂ j : Fin 3, i₁ ≠ k → i₂ ≠ k → i₁ ≠ i₂ → j ≠ k →
      j = i₁ ∨ j = i₂ := by
  decide

/-- Sperner-restricted specialization of `isDoor_dim_two_iff`: when
neither non-`k` vertex of `s` carries color `2` (which the Sperner
condition automatically forces whenever both lie on geometric face
`2`), the door condition collapses to "the two non-`k` vertices have
different colors".

Concretely, for any two distinct non-`k` indices `i₁ ≠ i₂` (which
together exhaust the non-`k` vertices of a 2-cell), `IsDoor c K s k`
is equivalent to `c (K.vertex s i₁) ≠ c (K.vertex s i₂)`.

This is the abstract bridge consumed by `_hLastFace` discharges of
n = 2 Sperner-on-Triangulation instances. The hypothesis `h_no2`
typically arises by combining `IsSpernerColoring c onFace` with the
assumption that both non-`k` vertices satisfy `onFace v 2`. The
conclusion is in the canonical "color-change" shape that matches the
`g k ≠ g (k + 1)` predicate of the diagonal-path coloring used in
`face2_path_odd`. -/
lemma isDoor_dim_two_iff_color_change_of_no_color_two
    {V : Type*} [DecidableEq V] (K : CellComplex V 2)
    (c : V → Fin 3) (s : K.Cell) (k : Fin 3)
    (h_no2 : ∀ i : Fin 3, i ≠ k → c (K.vertex s i) ≠ (2 : Fin 3))
    {i₁ i₂ : Fin 3} (h_i₁_ne : i₁ ≠ k) (h_i₂_ne : i₂ ≠ k)
    (h_i_distinct : i₁ ≠ i₂) :
    CellComplex.IsDoor c K s k ↔
      c (K.vertex s i₁) ≠ c (K.vertex s i₂) := by
  rw [isDoor_dim_two_iff]
  have hc1_no2 : c (K.vertex s i₁) ≠ (2 : Fin 3) := h_no2 i₁ h_i₁_ne
  have hc2_no2 : c (K.vertex s i₂) ≠ (2 : Fin 3) := h_no2 i₂ h_i₂_ne
  refine ⟨fun ⟨h0, h1⟩ => ?_, fun h_ne => ?_⟩
  · -- Forward direction (contrapositive): if `c (vertex s i₁)` and
    -- `c (vertex s i₂)` were equal, the existence of color-`0` and
    -- color-`1` witnesses among non-`k` vertices `= {i₁, i₂}` would
    -- force `0 = 1`, contradicting `decide`.
    intro h_eq
    obtain ⟨j₀, hj₀_ne, hj₀_color⟩ := h0
    obtain ⟨j₁, hj₁_ne, hj₁_color⟩ := h1
    have hj₀_cases :=
      fin_three_other_eq k i₁ i₂ j₀ h_i₁_ne h_i₂_ne h_i_distinct hj₀_ne
    have hj₁_cases :=
      fin_three_other_eq k i₁ i₂ j₁ h_i₁_ne h_i₂_ne h_i_distinct hj₁_ne
    have h_j_colors_eq : c (K.vertex s j₀) = c (K.vertex s j₁) := by
      rcases hj₀_cases with rfl | rfl
      · rcases hj₁_cases with rfl | rfl
        · rfl
        · exact h_eq
      · rcases hj₁_cases with rfl | rfl
        · exact h_eq.symm
        · rfl
    rw [hj₀_color, hj₁_color] at h_j_colors_eq
    exact absurd h_j_colors_eq (by decide)
  · -- Reverse direction: distinct colors `c (vertex s i₁), c (vertex s i₂)`
    -- with both `≠ 2` forces one to be `0` and the other to be `1`,
    -- supplying the two existential witnesses required by
    -- `isDoor_dim_two_iff`. Pure `Fin 3` case enumeration via `decide`.
    have h_pair : ∀ x y : Fin 3, x ≠ 2 → y ≠ 2 → x ≠ y →
        (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 0) := by decide
    rcases h_pair _ _ hc1_no2 hc2_no2 h_ne with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · exact ⟨⟨i₁, h_i₁_ne, hc1⟩, ⟨i₂, h_i₂_ne, hc2⟩⟩
    · exact ⟨⟨i₂, h_i₂_ne, hc2⟩, ⟨i₁, h_i₁_ne, hc1⟩⟩

end SimplicialAdjFnHelper

-- ============================================================
-- (Session 19 part 3) `_hBoundaryOnFace` discharge for `simData2 N`.
--
-- Combines S19.1 (`adjFn_eq_none_iff_card_le_one`), S19.2 (the
-- `forall_vertex_ne_iff_forall_face_mem` bridge + 6 erase
-- computations), S18.1 (boundary container singletons +
-- `*_endpoints_on_face*`), S18.2 (interior neighbor existentials),
-- and S17 (diagonal interior bridge) to discharge the
-- `_hBoundaryOnFace` hypothesis of `Triangulation.boundary_doors_odd`
-- for `(simData2 N).toTriangulation`.
--
-- Strategy: case-split `S ∈ topSimps2 N` (t1 b vs t2 c) via
-- `topSimps2_mem_iff`, then case-split on which of the three
-- vertices is dropped via `vertexEnum_mem`. The S19.2 erase
-- lemmas identify the resulting edge in each case.
--
-- For `t2 c` cells, every edge has ≥ 2 containers via S18 part 2
-- (`t2_face*_card_ge_two`), contradicting card ≤ 1 (boundary).
--
-- For `t1 b` cells, the geometric boundary condition is forced by
-- contradiction: assuming the interior condition holds, S17/S18.2
-- supplies a distinct second container, contradicting card ≤ 1.
-- Once the boundary condition is established, S18.5
-- (`*_endpoints_on_face*`) supplies the `onFaceΔ2` witnesses.
-- ============================================================

-- NOTE (S33): this block used to re-open `namespace SpernerFreudSimp`
-- while the namespace opened before `SimplicialAdjFnHelper` was still
-- active, double-namespacing every declaration below
-- (`SpernerFreudSimp.SpernerFreudSimp.*`). The redundant re-open was
-- removed so the file-final `end SpernerFreudSimp` closes cleanly and
-- `sperner_panchromatic_two` gets its intended single-level name.
section N2HBoundaryOnFace

variable (N : ℕ)

/-- Helper: two distinct top-simplices both containing the same
codim-1 face yield container card ≥ 2. -/
private lemma containers_two_distinct
    {f : Finset (ℕ × ℕ)} {S₁ S₂ : Finset (ℕ × ℕ)}
    (hS₁_in : S₁ ∈ topSimps2 N) (hS₁_sub : f ⊆ S₁)
    (hS₂_in : S₂ ∈ topSimps2 N) (hS₂_sub : f ⊆ S₂)
    (h_ne : S₁ ≠ S₂) :
    2 ≤ ((topSimps2 N).filter (fun s => f ⊆ s)).card := by
  have h₁_in : S₁ ∈ (topSimps2 N).filter (fun s => f ⊆ s) :=
    Finset.mem_filter.mpr ⟨hS₁_in, hS₁_sub⟩
  have h₂_in : S₂ ∈ (topSimps2 N).filter (fun s => f ⊆ s) :=
    Finset.mem_filter.mpr ⟨hS₂_in, hS₂_sub⟩
  have h_pair_card : ({S₁, S₂} : Finset (Finset (ℕ × ℕ))).card = 2 := by
    rw [Finset.card_insert_of_notMem
        (by rw [Finset.mem_singleton]; exact h_ne),
        Finset.card_singleton]
  have h_pair_sub :
      ({S₁, S₂} : Finset (Finset (ℕ × ℕ))) ⊆
        (topSimps2 N).filter (fun s => f ⊆ s) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h₁_in
    · exact h₂_in
  calc 2 = _ := h_pair_card.symm
    _ ≤ _ := Finset.card_le_card h_pair_sub

/-- The `_hBoundaryOnFace` discharge for `(simData2 N).toTriangulation`:
every boundary door of the n=2 Type-1/Type-2 triangulation lies on a
geometric face of Δ². This is the concrete consumer of S16-S19's
combinatorial infrastructure. -/
private lemma boundaryOnFace_simData2 :
    ∀ (s : ((simData2 N).toTriangulation).Cell) (k : Fin 3),
      ((simData2 N).toTriangulation).adj s k = none →
      ∃ faceIdx : Fin 3, ∀ j : Fin 3, j ≠ k →
        onFaceΔ2_strict N (((simData2 N).toTriangulation).vertex s j) faceIdx := by
  intro ⟨S, hS⟩ k h_adj
  -- Step 1: Convert adj=none to containers card ≤ 1.
  have h_card_le :
      ((simData2 N).containersOf ((simData2 N).faceOf S hS k)).card ≤ 1 :=
    (SimplicialAdjFnHelper.adjFn_eq_none_iff_card_le_one
      (simData2 N) ⟨S, hS⟩ k).mp h_adj
  -- Step 2: In-range constraint on every face vertex.
  have h_in_range : ∀ v ∈ (simData2 N).faceOf S hS k, v.1 + v.2 ≤ N :=
    fun v hv =>
      topSimps2_vertex_in_range N hS ((simData2 N).faceOf_subset S hS k hv)
  -- Step 3: Convert ∀j≠k goal to ∀v∈face goal via S19.2 bridge.
  suffices h : ∃ faceIdx : Fin 3,
      ∀ v ∈ (simData2 N).faceOf S hS k, onFaceΔ2_strict N v faceIdx by
    obtain ⟨faceIdx, h_face⟩ := h
    refine ⟨faceIdx, ?_⟩
    exact (SimplicialAdjFnHelper.forall_vertex_ne_iff_forall_face_mem
      (simData2 N) S hS k _).mpr h_face
  -- Step 4: Definitional equation for containersOf in this concrete
  -- triangulation: `(simData2 N).containersOf f = topSimps2 N.filter (f ⊆ ·)`.
  have h_containers_eq : ∀ (f : Finset (ℕ × ℕ)),
      (simData2 N).containersOf f =
        (topSimps2 N).filter (fun s => f ⊆ s) := fun _ => rfl
  -- Step 5: Case-split on S ∈ topSimps2 N.
  rcases (topSimps2_mem_iff N S).mp hS with ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩
  · -- S = t1 b: case-split on which vertex is dropped.
    set vd := (simData2 N).vertexEnum (t1 b) hS k with hvd
    have h_drop : vd ∈ t1 b := (simData2 N).vertexEnum_mem (t1 b) hS k
    clear_value vd
    simp only [t1, Finset.mem_insert, Finset.mem_singleton] at h_drop
    rcases h_drop with hd | hd | hd
    · -- (S19.3.1) dropped = (b.1+1, b.2): face = vertical edge {b, (b.1, b.2+1)}.
      have h_face_eq :
          (simData2 N).faceOf (t1 b) hS k =
            ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) := by
        show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
        rw [← hvd, hd]; exact t1_erase_first b
      -- Force boundary condition b.1 = 0 by interior contradiction.
      have h_b1_zero : b.1 = 0 := by
        by_contra h_pos
        have h_b1_pos : 1 ≤ b.1 := Nat.one_le_iff_ne_zero.mpr h_pos
        obtain ⟨s2, h_s2_in, h_s2_ne, h_s2_sub⟩ :=
          vertical_neighbor_topSimps2 N hb h_b1_pos
        have h_t1b_sub :
            ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) ⊆ t1 b := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;>
            · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
              first | omega | tauto
        have h_two : 2 ≤ ((simData2 N).containersOf
            ((simData2 N).faceOf (t1 b) hS k)).card := by
          rw [h_face_eq, h_containers_eq]
          exact containers_two_distinct N
            (t1_in_topSimps2_of_base N hb) h_t1b_sub
            h_s2_in h_s2_sub h_s2_ne.symm
        omega
      -- Boundary case: faceIdx = 0; vertical edge endpoints on face 0.
      refine ⟨0, ?_⟩
      intro v hv
      have h_in_v : v.1 + v.2 ≤ N := h_in_range v hv
      rw [h_face_eq] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      obtain ⟨h_b_face, h_b'_face⟩ := vertical_endpoints_on_face0 N b h_b1_zero
      rcases hv with rfl | rfl
      · exact ⟨h_in_v, h_b_face⟩
      · exact ⟨h_in_v, h_b'_face⟩
    · -- (S19.3.2) dropped = (b.1, b.2+1): face = horizontal edge {b, (b.1+1, b.2)}.
      have h_face_eq :
          (simData2 N).faceOf (t1 b) hS k =
            ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) := by
        show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
        rw [← hvd, hd]; exact t1_erase_second b
      have h_b2_zero : b.2 = 0 := by
        by_contra h_pos
        have h_b2_pos : 1 ≤ b.2 := Nat.one_le_iff_ne_zero.mpr h_pos
        obtain ⟨s2, h_s2_in, h_s2_ne, h_s2_sub⟩ :=
          horizontal_neighbor_topSimps2 N hb h_b2_pos
        have h_t1b_sub :
            ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t1 b := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;>
            · simp only [t1, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, Prod.ext_iff]
              first | omega | tauto
        have h_two : 2 ≤ ((simData2 N).containersOf
            ((simData2 N).faceOf (t1 b) hS k)).card := by
          rw [h_face_eq, h_containers_eq]
          exact containers_two_distinct N
            (t1_in_topSimps2_of_base N hb) h_t1b_sub
            h_s2_in h_s2_sub h_s2_ne.symm
        omega
      refine ⟨1, ?_⟩
      intro v hv
      have h_in_v : v.1 + v.2 ≤ N := h_in_range v hv
      rw [h_face_eq] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      obtain ⟨h_b_face, h_b'_face⟩ := horizontal_endpoints_on_face1 N b h_b2_zero
      rcases hv with rfl | rfl
      · exact ⟨h_in_v, h_b_face⟩
      · exact ⟨h_in_v, h_b'_face⟩
    · -- (S19.3.3) dropped = b: face = diagonal edge {(b.1, b.2+1), (b.1+1, b.2)}.
      have h_face_eq :
          (simData2 N).faceOf (t1 b) hS k =
            ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) := by
        show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
        rw [← hvd, hd]; exact t1_erase_third b
      have h_b_diag : N ≤ b.1 + b.2 + 1 := by
        by_contra h_pos
        have h_b_lt : b.1 + b.2 + 1 < N := by omega
        have h_b_in_t2 : b ∈ t2Bases N :=
          t1Bases_diagonal_neighbor_in_t2Bases N hb h_b_lt
        have h_t1b_sub :
            ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t1 b :=
          (diagonal_in_t1_iff b b).mpr rfl
        have h_t2b_sub :
            ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) ⊆ t2 b :=
          (diagonal_in_t2_iff b b).mpr rfl
        have h_two : 2 ≤ ((simData2 N).containersOf
            ((simData2 N).faceOf (t1 b) hS k)).card := by
          rw [h_face_eq, h_containers_eq]
          exact containers_two_distinct N
            (t1_in_topSimps2_of_base N hb) h_t1b_sub
            (t2_in_topSimps2_of_base N h_b_in_t2) h_t2b_sub (t1_ne_t2 b b)
        omega
      refine ⟨2, ?_⟩
      intro v hv
      have h_in_v : v.1 + v.2 ≤ N := h_in_range v hv
      rw [h_face_eq] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      obtain ⟨h_b_face, h_b'_face⟩ := diagonal_endpoints_on_face2 N hb h_b_diag
      rcases hv with rfl | rfl
      · exact ⟨h_in_v, h_b_face⟩
      · exact ⟨h_in_v, h_b'_face⟩
  · -- S = t2 c case: every edge has ≥ 2 containers, contradicting card ≤ 1.
    exfalso
    set vd := (simData2 N).vertexEnum (t2 c) hS k with hvd
    have h_drop : vd ∈ t2 c := (simData2 N).vertexEnum_mem (t2 c) hS k
    clear_value vd
    simp only [t2, Finset.mem_insert, Finset.mem_singleton] at h_drop
    rcases h_drop with hd | hd | hd
    · -- dropped = (c.1+1, c.2+1): face = face2 of t2 c
      have h_face_eq :
          (simData2 N).faceOf (t2 c) hS k =
            ({(c.1, c.2+1), (c.1+1, c.2)} : Finset (ℕ × ℕ)) := by
        show (t2 c).erase ((simData2 N).vertexEnum (t2 c) hS k) = _
        rw [← hvd, hd]; exact t2_erase_first c
      have h_two := t2_face2_card_ge_two N hc
      have h_card : ((simData2 N).containersOf
          ((simData2 N).faceOf (t2 c) hS k)).card =
        ((topSimps2 N).filter
          (fun s => ({(c.1, c.2+1), (c.1+1, c.2)} : Finset (ℕ × ℕ)) ⊆ s)).card := by
        rw [h_face_eq, h_containers_eq]
      omega
    · -- dropped = (c.1+1, c.2): face = face1 of t2 c
      have h_face_eq :
          (simData2 N).faceOf (t2 c) hS k =
            ({(c.1, c.2+1), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) := by
        show (t2 c).erase ((simData2 N).vertexEnum (t2 c) hS k) = _
        rw [← hvd, hd]; exact t2_erase_second c
      have h_two := t2_face1_card_ge_two N hc
      have h_card : ((simData2 N).containersOf
          ((simData2 N).faceOf (t2 c) hS k)).card =
        ((topSimps2 N).filter
          (fun s => ({(c.1, c.2+1), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) ⊆ s)).card := by
        rw [h_face_eq, h_containers_eq]
      omega
    · -- dropped = (c.1, c.2+1): face = face0 of t2 c
      have h_face_eq :
          (simData2 N).faceOf (t2 c) hS k =
            ({(c.1+1, c.2), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) := by
        show (t2 c).erase ((simData2 N).vertexEnum (t2 c) hS k) = _
        rw [← hvd, hd]; exact t2_erase_third c
      have h_two := t2_face0_card_ge_two N hc
      have h_card : ((simData2 N).containersOf
          ((simData2 N).faceOf (t2 c) hS k)).card =
        ((topSimps2 N).filter
          (fun s => ({(c.1+1, c.2), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) ⊆ s)).card := by
        rw [h_face_eq, h_containers_eq]
      omega

end N2HBoundaryOnFace

-- ============================================================
-- (S20) Saturating-diagonal base set for `_hLastFace`.
--
-- The `_hLastFace` slot of `Triangulation.boundary_doors_odd`
-- requires the count of boundary doors `(s, k)` whose remaining
-- vertices all lie on geometric face 2 (`b.1 + b.2 = N`) to be
-- odd. By S18.1 + S18.5, the only boundary doors that can lie on
-- face 2 come from `t1 b` cells with the **saturating diagonal**
-- condition `b.1 + b.2 + 1 = N` (the cell's diagonal edge becomes
-- the boundary). T2 cells contribute no boundary doors (S18.2),
-- and the horizontal/vertical t1-boundary edges are on face 1 / 0
-- respectively (S18.5 `*_endpoints_on_face*`).
--
-- This section introduces `satDiagBases N` — the t1 bases meeting
-- the saturating-diagonal condition — and proves the basic
-- structural results that S21 will compose with `face2_path_odd`
-- to produce the bijection door ↔ color-changing diagonal edge.
--
-- Concretely, this section delivers:
-- * `satDiagBases N` definition + `satDiagBases_mem_iff`
-- * `satDiagBases_eq_image_range`: explicit equality with
--   `(Finset.range N).image (fun k => (k, N-1-k))`
-- * `satDiagBases_card`: cardinality = N
-- * `satDiagBases_subset_t1Bases`: subset relation
-- * `satDiagBases_endpoints_on_face2`: both diagonal endpoints
--   satisfy `onFaceΔ2_strict N · (2 : Fin 3)` (strict = in-range +
--   geometric face), supplying both halves of `_hLastFace`'s
--   condition (3) for the diagonal-cell case.
--
-- S21 will pin down the matching `vertexEnum` index `k` (via the
-- existing `vertexEnum (t1 b) hS k ∈ t1 b` 3-way case-split
-- pattern from S19.3), then bridge `IsDoor` to `face2_path_odd`'s
-- color-change predicate to discharge `_hLastFace`.
-- ============================================================

section N2LastFaceBases

/-- Saturating-diagonal t1 bases: `b ∈ t1Bases N` whose diagonal
edge sits exactly on the simplex's boundary (i.e., the diagonal
endpoints satisfy `v.1 + v.2 = N`). Equivalently
`b.1 + b.2 + 1 = N`, since the diagonal endpoints are
`(b.1+1, b.2)` and `(b.1, b.2+1)`. -/
private def satDiagBases (N : ℕ) : Finset (ℕ × ℕ) :=
  (t1Bases N).filter (fun b => b.1 + b.2 + 1 = N)

/-- Membership iff: clean form combining `t1Bases_mem_iff` with
the saturating-diagonal condition. The `b.1 < N ∧ b.2 < N` clauses
follow from `b.1 + b.2 + 1 = N` (since both summands are `≥ 0`),
but we keep them explicit so the iff matches the standard
`t1Bases_mem_iff` shape. -/
private lemma satDiagBases_mem_iff (N : ℕ) (b : ℕ × ℕ) :
    b ∈ satDiagBases N ↔
      b.1 < N ∧ b.2 < N ∧ b.1 + b.2 + 1 = N := by
  unfold satDiagBases
  rw [Finset.mem_filter, t1Bases_mem_iff]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, hsat⟩; exact ⟨h1, h2, hsat⟩
  · rintro ⟨h1, h2, hsat⟩
    refine ⟨⟨h1, h2, ?_⟩, hsat⟩
    omega

/-- Saturating diagonal bases are a subset of `t1Bases`. -/
private lemma satDiagBases_subset_t1Bases (N : ℕ) :
    satDiagBases N ⊆ t1Bases N := by
  intro b hb
  exact (Finset.mem_filter.mp hb).1

/-- The map `k ↦ (k, N-1-k)` is injective on `Finset.range N`. -/
private lemma satDiagBases_image_map_injOn (N : ℕ) :
    Set.InjOn (fun k => ((k, N - 1 - k) : ℕ × ℕ))
      (↑(Finset.range N) : Set ℕ) := by
  intro k₁ _ k₂ _ hkeq
  -- `congrArg Prod.fst` extracts the first-component equality from
  -- the pair equality `(k₁, N-1-k₁) = (k₂, N-1-k₂)`.
  exact congrArg Prod.fst hkeq

/-- The image of `Finset.range N` under `k ↦ (k, N-1-k)` is
exactly `satDiagBases N`. This is the explicit parametrization
that drives the cardinality computation and the future bijection
with `face2_path_odd`'s color-changing edges. -/
private lemma satDiagBases_eq_image_range (N : ℕ) :
    satDiagBases N =
      (Finset.range N).image (fun k => (k, N - 1 - k)) := by
  ext ⟨b1, b2⟩
  rw [satDiagBases_mem_iff, Finset.mem_image]
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, _h2, hsat⟩
    refine ⟨b1, Finset.mem_range.mpr h1, ?_⟩
    -- snd-component: `N - 1 - b1 = b2` from `b1 + b2 + 1 = N`.
    have hsnd : N - 1 - b1 = b2 := by omega
    exact (Prod.mk.injEq _ _ _ _).mpr ⟨rfl, hsnd⟩
  · rintro ⟨k, hk, hk_eq⟩
    rw [Finset.mem_range] at hk
    -- `(k, N - 1 - k) = (b1, b2)` ⟹ `b1 = k ∧ b2 = N - 1 - k`.
    have hfst : k = b1 := congrArg Prod.fst hk_eq
    have hsnd : N - 1 - k = b2 := congrArg Prod.snd hk_eq
    refine ⟨?_, ?_, ?_⟩ <;> omega

/-- The cardinality of `satDiagBases N` is exactly `N`. This is
the count side of the future `_hLastFace` bijection: there are
exactly `N` saturating-diagonal cells, matching the `N` edges of
`face2_path_odd`'s `Finset.range N` index set. -/
private lemma satDiagBases_card (N : ℕ) : (satDiagBases N).card = N := by
  rw [satDiagBases_eq_image_range,
      Finset.card_image_of_injOn (satDiagBases_image_map_injOn N),
      Finset.card_range]

/-- For `b ∈ satDiagBases N`, the diagonal endpoints
`(b.1, b.2+1)` and `(b.1+1, b.2)` lie in the in-range region
`v.1 + v.2 ≤ N`. (In fact they saturate, with equality.) This is
the in-range half of `onFaceΔ2_strict`. -/
private lemma satDiagBases_endpoints_in_range
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    (b.1 + (b.2 + 1) ≤ N) ∧ ((b.1 + 1) + b.2 ≤ N) := by
  rw [satDiagBases_mem_iff] at hb
  obtain ⟨_, _, hsat⟩ := hb
  refine ⟨?_, ?_⟩ <;> omega

/-- For `b ∈ satDiagBases N`, the diagonal endpoints both satisfy
the strict face-2 predicate `onFaceΔ2_strict N · (2 : Fin 3)`
(strict = in-range conjuncted with the geometric `b.1 + b.2 = N`
condition).

This is exactly the per-vertex content of the
`∀ j ≠ k, onFaceΔ2_strict N (T.vertex s j) (2 : Fin 3)` clause in
`_hLastFace` for the `s = t1 b, k = (the index dropping b)` case.
S21 will compose this with the `vertexEnum (t1 b) hs k ∈ t1 b`
3-way case-split (per the S19.3 pattern) to identify the unique
`k` that makes the dropped vertex equal `b`. -/
private lemma satDiagBases_endpoints_on_face2
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    onFaceΔ2_strict N (b.1, b.2 + 1) (2 : Fin 3) ∧
      onFaceΔ2_strict N (b.1 + 1, b.2) (2 : Fin 3) := by
  have hbt1 : b ∈ t1Bases N := satDiagBases_subset_t1Bases N hb
  have hsat : N ≤ b.1 + b.2 + 1 := by
    rw [satDiagBases_mem_iff] at hb
    omega
  have hgeom := diagonal_endpoints_on_face2 N hbt1 hsat
  have hrange := satDiagBases_endpoints_in_range N hb
  exact ⟨⟨hrange.1, hgeom.1⟩, ⟨hrange.2, hgeom.2⟩⟩

/-- `t1 b ∈ topSimps2 N` for `b ∈ satDiagBases N`. Convenience
alias used by S21 to feed the saturating-diagonal cells through
the `Triangulation.boundary_doors_odd` consumers. -/
private lemma satDiagBases_t1_in_topSimps2
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    t1 b ∈ topSimps2 N :=
  t1_in_topSimps2_of_base N (satDiagBases_subset_t1Bases N hb)

end N2LastFaceBases

-- ============================================================
-- (S21A) Forward extraction for `_hLastFace` (t1-side).
--
-- For `b ∈ t1Bases N` and any drop-index `k : Fin 3`, if all
-- non-`k` vertices of `t1 b` lie on geometric face 2 (the
-- per-vertex condition that defines membership in the
-- `_hLastFace` filter of `Triangulation.boundary_doors_odd`),
-- then the drop must be `b` itself and `b ∈ satDiagBases N`. The
-- two non-diagonal drop cases are eliminated by inconsistent
-- face-2 sums (`b.1+b.2 = N ∧ b.1+b.2+1 = N` is impossible);
-- the diagonal-drop case forces both endpoints to satisfy
-- `b.1+b.2+1 = N`, exactly the saturating-diagonal condition.
--
-- This is the t1-side of the eventual bijection between the
-- `_hLastFace` filter and `face2_path_odd`'s color-changing
-- edges. S21B will assemble the full discharge by combining
-- this with the existing t2-extinction (every t2 face has ≥ 2
-- containers, so `adj = none ∧ S = t2 c` is impossible — see
-- `boundaryOnFace_simData2` t2 branch) and an `IsDoor` ↔
-- `g k ≠ g (k+1)` color-change bridge.
-- ============================================================

section N2LastFaceExtract

/-- Forward extraction for `_hLastFace` (t1-side): for
`b ∈ t1Bases N` and `k : Fin 3`, if every non-`k` vertex of
`t1 b` lies on geometric face 2 (`onFaceΔ2_strict N · 2`), then
`b ∈ satDiagBases N` and the drop is `b` itself.

Proof: case-split on `vertexEnum (t1 b) hS k ∈ t1 b` (the S19.3
pattern). The drops `(b.1+1, b.2)` and `(b.1, b.2+1)` each leave
a face whose two endpoints differ in `b.1+b.2` sum by 1, so they
cannot simultaneously satisfy `(·).1+(·).2 = N`. The drop `b`
leaves the diagonal edge whose endpoints both satisfy
`b.1+b.2+1 = N`, exactly the `satDiagBases_mem_iff` condition. -/
private lemma t1_lastFace_implies_satDiag
    (N : ℕ) {b : ℕ × ℕ} (hb : b ∈ t1Bases N)
    (k : Fin 3)
    (h_face2 : ∀ j : Fin 3, j ≠ k →
      onFaceΔ2_strict N
        ((simData2 N).vertexEnum (t1 b)
          (t1_in_topSimps2_of_base N hb) j)
        (2 : Fin 3)) :
    b ∈ satDiagBases N ∧
      (simData2 N).vertexEnum (t1 b)
        (t1_in_topSimps2_of_base N hb) k = b := by
  set hS := t1_in_topSimps2_of_base N hb with hS_def
  -- Convert the `∀ j ≠ k`-on-vertexEnum hypothesis to the
  -- `∀ v ∈ faceOf` form via the S19.2 generic bridge.
  have h_face_v : ∀ v ∈ (simData2 N).faceOf (t1 b) hS k,
      onFaceΔ2_strict N v (2 : Fin 3) :=
    (SimplicialAdjFnHelper.forall_vertex_ne_iff_forall_face_mem
      (simData2 N) (t1 b) hS k _).mp h_face2
  -- Case-split on which vertex of `t1 b` is dropped (S19.3 pattern).
  set vd := (simData2 N).vertexEnum (t1 b) hS k with hvd
  have h_drop : vd ∈ t1 b := (simData2 N).vertexEnum_mem (t1 b) hS k
  clear_value vd
  simp only [t1, Finset.mem_insert, Finset.mem_singleton] at h_drop
  rcases h_drop with hd | hd | hd
  · -- Drop = `(b.1+1, b.2)`: face = `{b, (b.1, b.2+1)}` (vertical edge).
    -- Both must be on face 2: forces `b.1+b.2 = N ∧ b.1+(b.2+1) = N`.
    exfalso
    have h_face_eq : (simData2 N).faceOf (t1 b) hS k =
        ({b, (b.1, b.2+1)} : Finset (ℕ × ℕ)) := by
      show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
      rw [← hvd, hd]; exact t1_erase_first b
    have h_b_on : onFaceΔ2_strict N b (2 : Fin 3) := by
      apply h_face_v; rw [h_face_eq]; simp
    have h_v_on : onFaceΔ2_strict N (b.1, b.2+1) (2 : Fin 3) := by
      apply h_face_v; rw [h_face_eq]; simp
    have h_b_face := h_b_on.2
    have h_v_face := h_v_on.2
    rw [onFaceΔ2_two_iff] at h_b_face h_v_face
    omega
  · -- Drop = `(b.1, b.2+1)`: face = `{b, (b.1+1, b.2)}` (horizontal edge).
    -- Symmetric contradiction via `b.1+b.2 = N ∧ (b.1+1)+b.2 = N`.
    exfalso
    have h_face_eq : (simData2 N).faceOf (t1 b) hS k =
        ({b, (b.1+1, b.2)} : Finset (ℕ × ℕ)) := by
      show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
      rw [← hvd, hd]; exact t1_erase_second b
    have h_b_on : onFaceΔ2_strict N b (2 : Fin 3) := by
      apply h_face_v; rw [h_face_eq]; simp
    have h_v_on : onFaceΔ2_strict N (b.1+1, b.2) (2 : Fin 3) := by
      apply h_face_v; rw [h_face_eq]; simp
    have h_b_face := h_b_on.2
    have h_v_face := h_v_on.2
    rw [onFaceΔ2_two_iff] at h_b_face h_v_face
    omega
  · -- Drop = `b`: face = `{(b.1, b.2+1), (b.1+1, b.2)}` (diagonal edge).
    -- Endpoint `(b.1, b.2+1)` on face 2 ⟹ `b.1 + b.2 + 1 = N`,
    -- exactly the `satDiagBases` defining condition.
    have h_face_eq : (simData2 N).faceOf (t1 b) hS k =
        ({(b.1, b.2+1), (b.1+1, b.2)} : Finset (ℕ × ℕ)) := by
      show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
      rw [← hvd, hd]; exact t1_erase_third b
    have h_v_on : onFaceΔ2_strict N (b.1, b.2+1) (2 : Fin 3) := by
      apply h_face_v; rw [h_face_eq]; simp
    have h_v_face := h_v_on.2
    rw [onFaceΔ2_two_iff] at h_v_face
    rw [t1Bases_mem_iff] at hb
    have h_sat : b.1 + b.2 + 1 = N := by omega
    refine ⟨?_, hd⟩
    rw [satDiagBases_mem_iff]
    exact ⟨hb.1, hb.2.1, h_sat⟩

end N2LastFaceExtract

-- ============================================================
-- (S24) t2-side boundary extinction for `_hLastFace`.
--
-- For `c ∈ t2Bases N` and any drop-index `k : Fin 3`, the cell
-- `(t2 c, k)` is **never** in the `_hLastFace` filter of
-- `Triangulation.boundary_doors_odd`: every codim-1 face of a
-- `t2 c` simplex has at least two containers (`t2 c` itself plus
-- a sharing `t1` cell — see `t2_face*_card_ge_two`), so by S19.1's
-- `adjFn_eq_none_iff_card_le_one` the adjacency function returns
-- `some _` for every drop index.
--
-- This is the t2-counterpart to S21A's `t1_lastFace_implies_satDiag`:
-- together they show the only cells contributing to the
-- `_hLastFace` filter of `(simData2 N).toTriangulation` are
-- saturating-diagonal `t1` cells with the diagonal-drop index.
-- The proof is a direct extraction of the t2 branch of
-- `boundaryOnFace_simData2` (lines 2186–2230), packaged so that
-- S25's bijection assembly can dismiss the t2 case by a single
-- `match`/`rcases` rather than re-running the case-split.
-- ============================================================

section N2LastFaceT2Extinct

/-- t2-side boundary extinction: for `c ∈ t2Bases N` and any
`k : Fin 3`, the adjacency of the cell `⟨t2 c, _⟩` at face `k`
is never `none`. Every codim-1 face of `t2 c` has at least two
containers (`t2 c` itself plus a sharing `t1` cell), so the
generic `adjFn_eq_none_iff_card_le_one` fails the cardinality
direction.

This is the t2-companion to S21A's `t1_lastFace_implies_satDiag`:
together they show the only cells `(s, k)` with `adj = none` and
all non-`k` vertices on geometric face 2 are saturating-diagonal
`t1` cells with the diagonal-drop index. -/
private lemma t2_adj_ne_none
    (N : ℕ) {c : ℕ × ℕ} (hc : c ∈ t2Bases N) (k : Fin 3) :
    ((simData2 N).toTriangulation).adj
        ⟨t2 c, t2_in_topSimps2_of_base N hc⟩ k ≠ none := by
  intro h_adj
  set hS := t2_in_topSimps2_of_base N hc with hS_def
  -- Convert adj=none to containers card ≤ 1 (S19.1).
  have h_card_le :
      ((simData2 N).containersOf
        ((simData2 N).faceOf (t2 c) hS k)).card ≤ 1 :=
    (SimplicialAdjFnHelper.adjFn_eq_none_iff_card_le_one
      (simData2 N) ⟨t2 c, hS⟩ k).mp h_adj
  -- Definitional equation for `(simData2 N).containersOf`.
  have h_containers_eq : ∀ (f : Finset (ℕ × ℕ)),
      (simData2 N).containersOf f =
        (topSimps2 N).filter (fun s => f ⊆ s) := fun _ => rfl
  -- Case-split on which vertex of `t2 c` is dropped.
  set vd := (simData2 N).vertexEnum (t2 c) hS k with hvd
  have h_drop : vd ∈ t2 c := (simData2 N).vertexEnum_mem (t2 c) hS k
  clear_value vd
  simp only [t2, Finset.mem_insert, Finset.mem_singleton] at h_drop
  rcases h_drop with hd | hd | hd
  · -- dropped = `(c.1+1, c.2+1)`: face = `{(c.1, c.2+1), (c.1+1, c.2)}` (face 2 of t2 c).
    have h_face_eq :
        (simData2 N).faceOf (t2 c) hS k =
          ({(c.1, c.2+1), (c.1+1, c.2)} : Finset (ℕ × ℕ)) := by
      show (t2 c).erase ((simData2 N).vertexEnum (t2 c) hS k) = _
      rw [← hvd, hd]; exact t2_erase_first c
    have h_two := t2_face2_card_ge_two N hc
    rw [h_face_eq, h_containers_eq] at h_card_le
    omega
  · -- dropped = `(c.1+1, c.2)`: face = `{(c.1, c.2+1), (c.1+1, c.2+1)}` (face 1 of t2 c).
    have h_face_eq :
        (simData2 N).faceOf (t2 c) hS k =
          ({(c.1, c.2+1), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) := by
      show (t2 c).erase ((simData2 N).vertexEnum (t2 c) hS k) = _
      rw [← hvd, hd]; exact t2_erase_second c
    have h_two := t2_face1_card_ge_two N hc
    rw [h_face_eq, h_containers_eq] at h_card_le
    omega
  · -- dropped = `(c.1, c.2+1)`: face = `{(c.1+1, c.2), (c.1+1, c.2+1)}` (face 0 of t2 c).
    have h_face_eq :
        (simData2 N).faceOf (t2 c) hS k =
          ({(c.1+1, c.2), (c.1+1, c.2+1)} : Finset (ℕ × ℕ)) := by
      show (t2 c).erase ((simData2 N).vertexEnum (t2 c) hS k) = _
      rw [← hvd, hd]; exact t2_erase_third c
    have h_two := t2_face0_card_ge_two N hc
    rw [h_face_eq, h_containers_eq] at h_card_le
    omega

/-- Filter-membership form for direct S25 consumption: no element
of the `_hLastFace` filter of `(simData2 N).toTriangulation` has a
`t2`-cell first coordinate. Together with the `topSimps2_mem_iff`
case split this lets S25 reduce the bijection assembly to t1 cells
only (then S21A pins the t1 base to `satDiagBases N`). -/
private lemma t2_lastFace_filter_impossible
    (N : ℕ) {c : ℕ × ℕ} (hc : c ∈ t2Bases N) (k : Fin 3)
    (h_adj : ((simData2 N).toTriangulation).adj
        ⟨t2 c, t2_in_topSimps2_of_base N hc⟩ k = none) :
    False :=
  t2_adj_ne_none N hc k h_adj

end N2LastFaceT2Extinct

-- ============================================================
-- (S25-rev) Reverse of S21A: for `b ∈ satDiagBases N`, the
-- self-drop index exists, is unique, and witnesses the per-vertex
-- face-2 condition that `_hLastFace` filters on.
--
-- S21A (forward, `t1_lastFace_implies_satDiag`) shows that any
-- `(t1 b, k)` cell pair in the `_hLastFace` filter forces
-- `b ∈ satDiagBases N` with `vertexEnum (t1 b) hS k = b`. This
-- section establishes the matching backward direction:
--
--   * `satDiag_self_drop_index_exists` — `b ∈ satDiagBases N` ⟹
--     ∃ k : Fin 3, `vertexEnum (t1 b) hS k = b`. Existence via
--     `vertexEnum_image_univ` (`b ∈ t1 b` lies in the image).
--   * `satDiag_self_drop_index_unique` — the self-drop index is
--     unique via `vertexEnum_injective`.
--   * `satDiag_self_drop_face2` — at the self-drop index, the two
--     remaining vertices `(b.1, b.2+1)` and `(b.1+1, b.2)` both
--     satisfy `onFaceΔ2_strict N · 2`. Combines `t1_erase_third`
--     (S19.2) with `satDiagBases_endpoints_on_face2` (S20) via the
--     bridge `forall_vertex_ne_iff_forall_face_mem` (S19.2).
--
-- Together with S24's t2-side extinction and S20's
-- `satDiagBases_card_eq N`, this packages the `satDiagBases N →
-- _hLastFace filter` direction that S25 will compose with S23's
-- color-side wiring + S22's `IsDoor` ↔ color-change bridge.
-- Independent of the in-flight S23 (`N2LastFaceColors`,
-- PR #17571) and S25-prep (gridPt coordinate values, PR #17621)
-- contributions.
-- ============================================================

section N2LastFaceSelfDropIndex

variable (N : ℕ)

/-- For `b ∈ satDiagBases N`, there exists `k : Fin 3` such that
the vertex enumeration at index `k` returns `b` itself.

This is the backward existence companion to S21A's forward
extraction. Existence follows from the surjection
`vertexEnum_image_univ` because `b ∈ t1 b` (it is the third
vertex by the `t1` definition). -/
private lemma satDiag_self_drop_index_exists
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    ∃ k : Fin 3,
      (simData2 N).vertexEnum (t1 b)
        (satDiagBases_t1_in_topSimps2 N hb) k = b := by
  set hS := satDiagBases_t1_in_topSimps2 N hb with hS_def
  have hb_mem_t1 : b ∈ t1 b := by
    simp only [t1, Finset.mem_insert, Finset.mem_singleton]
    right; right; trivial
  have h_img := (simData2 N).vertexEnum_image_univ (t1 b) hS
  rw [← h_img] at hb_mem_t1
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hb_mem_t1
  exact ⟨k, hk⟩

/-- The self-drop index of `b ∈ satDiagBases N` is unique: any two
indices `k₁, k₂ : Fin 3` whose `vertexEnum` value equals `b` must
themselves be equal. Direct consequence of `vertexEnum_injective`. -/
private lemma satDiag_self_drop_index_unique
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N)
    {k₁ k₂ : Fin 3}
    (hk₁ : (simData2 N).vertexEnum (t1 b)
      (satDiagBases_t1_in_topSimps2 N hb) k₁ = b)
    (hk₂ : (simData2 N).vertexEnum (t1 b)
      (satDiagBases_t1_in_topSimps2 N hb) k₂ = b) :
    k₁ = k₂ :=
  (simData2 N).vertexEnum_injective (t1 b)
    (satDiagBases_t1_in_topSimps2 N hb) (hk₁.trans hk₂.symm)

/-- **Reverse of S21A.** For `b ∈ satDiagBases N` and any `k : Fin 3`
that is the self-drop index (`vertexEnum (t1 b) hS k = b`), every
non-`k` vertex of `t1 b` satisfies the geometric face-2 condition
`onFaceΔ2_strict N · 2` — i.e., the pair `(t1 b, k)` satisfies the
per-vertex condition of the `_hLastFace` filter of
`Triangulation.boundary_doors_odd`.

Proof: the dropped vertex is `b`, so `faceOf (t1 b) hS k =
(t1 b).erase b = {(b.1, b.2+1), (b.1+1, b.2)}` by S19.2's
`t1_erase_third`. Both diagonal endpoints satisfy
`onFaceΔ2_strict N · 2` by S20's `satDiagBases_endpoints_on_face2`.
The S19.2 bridge `forall_vertex_ne_iff_forall_face_mem` rewrites
the `∀ j ≠ k`-on-`vertexEnum` goal into the `∀ v ∈ faceOf` form
that the two-element membership case-split discharges.

Together with the existence + uniqueness lemmas above, this packages
the `b ∈ satDiagBases N → (t1 b, k_b) ∈ _hLastFace-style condition`
half of the eventual S25 bijection. -/
private lemma satDiag_self_drop_face2
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N)
    {k : Fin 3}
    (hk : (simData2 N).vertexEnum (t1 b)
      (satDiagBases_t1_in_topSimps2 N hb) k = b) :
    ∀ j : Fin 3, j ≠ k →
      onFaceΔ2_strict N
        ((simData2 N).vertexEnum (t1 b)
          (satDiagBases_t1_in_topSimps2 N hb) j)
        (2 : Fin 3) := by
  set hS := satDiagBases_t1_in_topSimps2 N hb with hS_def
  have h_face_eq : (simData2 N).faceOf (t1 b) hS k =
      ({(b.1, b.2 + 1), (b.1 + 1, b.2)} : Finset (ℕ × ℕ)) := by
    show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
    rw [hk]; exact t1_erase_third b
  have h_endpoints := satDiagBases_endpoints_on_face2 N hb
  show ∀ j : Fin (2 + 1), j ≠ k →
      onFaceΔ2_strict N ((simData2 N).vertexEnum (t1 b) hS j) (2 : Fin 3)
  exact (SimplicialAdjFnHelper.forall_vertex_ne_iff_forall_face_mem
    (simData2 N) (t1 b) hS k (fun v => onFaceΔ2_strict N v 2)).mpr (fun v hv => by
      rw [h_face_eq] at hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact h_endpoints.1
      · exact h_endpoints.2)

end N2LastFaceSelfDropIndex

-- ============================================================
-- (S25-prep-index) First-coordinate parametrization of `satDiagBases`.
--
-- The eventual S25 bijection between the `_hLastFace` filter and
-- `(Finset.range N).filter (fun k => g k ≠ g (k+1))` color-change
-- edges uses the natural map `b ↦ b.1` to identify a saturating-
-- diagonal base with its first coordinate. S20's
-- `satDiagBases_eq_image_range` parametrises in the FORWARD
-- direction (`k ↦ (k, N-1-k)`); this section packages the
-- corresponding INVERSE direction `b ↦ b.1` together with the
-- structural facts that drive the bijection assembly:
--
--   * `satDiagBases_fst_lt` — first coord is strictly < N
--   * `satDiagBases_snd_eq` — second coord = `N - 1 - b.1`
--   * `satDiagBases_eq_pair_fst` — base equals `(b.1, N-1-b.1)`
--   * `satDiagBases_image_fst` — `image Prod.fst = Finset.range N`
--   * `satDiagBases_fst_injOn` — `Prod.fst` is injective on `satDiagBases N`
--
-- Each is a one-line corollary of `satDiagBases_mem_iff` (S20).
-- Independent of the in-flight S23 (color wiring, PR #17571) and
-- S25-prep (gridPt coordinates, PR #17621) contributions, which
-- target the color side and the geometric coordinate side
-- respectively.
-- ============================================================

section N2SatDiagBasesIndex

variable (N : ℕ)

/-- For `b ∈ satDiagBases N`, the first coordinate is strictly < N. -/
private lemma satDiagBases_fst_lt {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    b.1 < N :=
  ((satDiagBases_mem_iff N b).mp hb).1

/-- For `b ∈ satDiagBases N`, the second coordinate is determined by the
first via `b.2 = N - 1 - b.1`. -/
private lemma satDiagBases_snd_eq {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    b.2 = N - 1 - b.1 := by
  obtain ⟨_, _, hsat⟩ := (satDiagBases_mem_iff N b).mp hb
  omega

/-- For `b ∈ satDiagBases N`, the base equals `(b.1, N - 1 - b.1)`. This is
the "ETA-form" sister of S20's `satDiagBases_eq_image_range`: the latter
parametrises by `k ↦ (k, N-1-k)`, this packages the inverse `b ↦ b.1`
that the S25 bijection consumes. -/
private lemma satDiagBases_eq_pair_fst {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    b = (b.1, N - 1 - b.1) :=
  Prod.ext rfl (satDiagBases_snd_eq N hb)

/-- The image of `satDiagBases N` under `Prod.fst` is exactly `Finset.range N`.
This is the count-side equality the S25 bijection ultimately turns into the
forward direction of the door ↔ color-change correspondence. -/
private lemma satDiagBases_image_fst :
    (satDiagBases N).image Prod.fst = Finset.range N := by
  ext k
  simp only [Finset.mem_image, Finset.mem_range]
  refine ⟨?_, ?_⟩
  · rintro ⟨b, hb, rfl⟩
    exact satDiagBases_fst_lt N hb
  · intro hk
    refine ⟨(k, N - 1 - k), ?_, rfl⟩
    rw [satDiagBases_mem_iff]
    refine ⟨hk, ?_, ?_⟩ <;> omega

/-- `Prod.fst` is injective on `satDiagBases N`: a saturating-diagonal base
is determined by its first coordinate (since the second is `N - 1 - b.1`).
Combined with `satDiagBases_image_fst`, this gives the bijection
`satDiagBases N ≃ Finset.range N` via `b ↔ b.1` that S25 will compose
with `face2_path_odd`'s color-change predicate. -/
private lemma satDiagBases_fst_injOn :
    Set.InjOn (Prod.fst : ℕ × ℕ → ℕ) (↑(satDiagBases N) : Set (ℕ × ℕ)) := by
  intro b₁ hb₁ b₂ hb₂ h_eq
  rw [Finset.mem_coe] at hb₁ hb₂
  rw [satDiagBases_eq_pair_fst N hb₁, satDiagBases_eq_pair_fst N hb₂, h_eq]

end N2SatDiagBasesIndex

-- ============================================================
-- (S25-prep-endpoint-form) Diagonal endpoints of `satDiagBases`
-- rewritten in `face2_path_odd`'s `(k, N - k)` parametrization.
--
-- `face2_path_odd` (in `N2Grid` section) defines its color path
-- function `g : ℕ → Fin 2` over vertices `(k, N - k)` for
-- `k : ℕ`. The eventual S25 bijection between the `_hLastFace`
-- filter and `(Finset.range N).filter (g · ≠ g · + 1)` color
-- changes will translate, for `b ∈ satDiagBases N` with self-
-- drop index `k`, the two non-`k` vertices of `t1 b` —
-- `(b.1, b.2 + 1)` and `(b.1 + 1, b.2)` — into the form
-- `(b.1, N - b.1)` and `(b.1 + 1, N - (b.1 + 1))` that
-- `face2_path_odd`'s parametrization expects.
--
-- The four lemmas in this section package those rewrites once
-- for reuse by S25:
--
--   * `satDiagBases_succ_le` — `b.1 + 1 ≤ N` (range bound for
--     `cN2` on the second endpoint).
--   * `satDiagBases_first_endpoint_face2_path_form` —
--     `(b.1, b.2 + 1) = (b.1, N - b.1)` (first endpoint at
--     `face2_path_odd`'s index `k = b.1`).
--   * `satDiagBases_second_endpoint_face2_path_form` —
--     `(b.1 + 1, b.2) = (b.1 + 1, N - (b.1 + 1))` (second
--     endpoint at index `k = b.1 + 1`).
--   * `satDiagBases_endpoints_pair_face2_path_form` — the
--     unordered pair of diagonal endpoints rewritten as a pair
--     of `(k, N - k)`-form vertices.
--
-- Each is a one-line corollary of `satDiagBases_mem_iff` (S20)
-- + `omega` + `Prod.ext`. Independent of the in-flight S23
-- (`N2LastFaceColors`, PR #17571) color wiring and S25-prep
-- (`N2GridCoord`, PR #17621) gridPt coordinate helpers.
-- ============================================================

section N2DiagonalEndpointForm

variable (N : ℕ)

/-- For `b ∈ satDiagBases N`, the successor of `b.1` is bounded by
`N`. This is the range hypothesis required to evaluate `cN2 N hN
f hf_map` (or `face2_path_odd`'s `g`) at the second diagonal
endpoint `(b.1 + 1, N - (b.1 + 1))`. -/
private lemma satDiagBases_succ_le
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    b.1 + 1 ≤ N := by
  obtain ⟨h1, _, _⟩ := (satDiagBases_mem_iff N b).mp hb
  omega

/-- For `b ∈ satDiagBases N`, the first diagonal endpoint
`(b.1, b.2 + 1)` is exactly `(b.1, N - b.1)` — the `k = b.1`
slice of `face2_path_odd`'s `(k, N - k)` parametrization. -/
private lemma satDiagBases_first_endpoint_face2_path_form
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    ((b.1, b.2 + 1) : ℕ × ℕ) = (b.1, N - b.1) := by
  obtain ⟨_, _, hsat⟩ := (satDiagBases_mem_iff N b).mp hb
  refine Prod.ext rfl ?_
  omega

/-- For `b ∈ satDiagBases N`, the second diagonal endpoint
`(b.1 + 1, b.2)` is exactly `(b.1 + 1, N - (b.1 + 1))` — the
`k = b.1 + 1` slice of `face2_path_odd`'s parametrization. -/
private lemma satDiagBases_second_endpoint_face2_path_form
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    ((b.1 + 1, b.2) : ℕ × ℕ) = (b.1 + 1, N - (b.1 + 1)) := by
  obtain ⟨_, _, hsat⟩ := (satDiagBases_mem_iff N b).mp hb
  refine Prod.ext rfl ?_
  omega

/-- For `b ∈ satDiagBases N`, the unordered pair of diagonal
endpoints `{(b.1, b.2 + 1), (b.1 + 1, b.2)}` equals the pair of
consecutive `face2_path_odd` slices `{(b.1, N - b.1),
(b.1 + 1, N - (b.1 + 1))}`. This is the convenient `Finset`-level
form S25 will consume when relating the door condition (acting on
the 2-element codim-1 face) to the color-change predicate
`g(b.1) ≠ g(b.1 + 1)`. -/
private lemma satDiagBases_endpoints_pair_face2_path_form
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) :
    (({(b.1, b.2 + 1), (b.1 + 1, b.2)} : Finset (ℕ × ℕ))) =
      ({(b.1, N - b.1), (b.1 + 1, N - (b.1 + 1))} : Finset (ℕ × ℕ)) := by
  rw [satDiagBases_first_endpoint_face2_path_form N hb,
      satDiagBases_second_endpoint_face2_path_form N hb]

end N2DiagonalEndpointForm

-- ============================================================
-- (S27-prep) Face-2 and color characterizations at the
-- `(k, N - k)` diagonal vertices of `face2_path_odd`.
--
-- The eventual S25/S27 bijection assembly between the
-- `_hLastFace` filter and `(Finset.range N).filter
-- (fun k => g k ≠ g (k + 1))` will need, for each `k ≤ N`, the
-- face-2 condition and the color-side `cN2 ... (k, N - k) ≠ 2`
-- predicate on the diagonal vertex of `face2_path_odd`. S26-prep
-- (`N2DiagonalEndpointForm`) translated `satDiagBases` endpoints
-- into the `(k, N - k)` parametrization; this section packages
-- the matching face/color facts on that side, so the bijection
-- consumer can stay entirely in `face2_path_odd`'s index form
-- without re-deriving the face/Sperner-condition glue.
--
--   * `onFaceΔ2_diag` — `(k, N - k)` is on geometric face 2.
--   * `onFaceΔ2_strict_diag` — strict version (with in-range
--     witness `k + (N - k) ≤ N`).
--   * `cN2_total_diag_eq` — `cN2_total` agrees with `cN2` at the
--     diagonal vertex (the `dif_pos` rewrite specialised).
--   * `cN2_diag_ne_two` — Sperner condition forbids color 2 at
--     the diagonal vertex (direct `cN2_ne_of_onFace`).
--   * `cN2_total_diag_ne_two` — wrapper-level corollary, the
--     shape consumed by S22's `h_no2` hypothesis when the
--     `_hLastFace` consumer carries `cN2_total` rather than the
--     in-range `cN2`.
--
-- Each is a one-line corollary of existing N2Grid lemmas
-- (`onFaceΔ2_two_iff`, `cN2_ne_of_onFace`, `cN2_total_eq`).
-- Independent of the in-flight S23 (`N2LastFaceColors`,
-- PR #17571) which packages the analogous color facts in the
-- `(b.1, b.2 + 1)`-endpoint form rather than the
-- `(k, N - k)`-diagonal form. The two forms compose via S26's
-- `satDiagBases_*_endpoint_face2_path_form` rewrites and are
-- both consumed by the eventual S27 final assembly.
-- ============================================================

section N2DiagFaceCondition

variable (N : ℕ) (hN : 0 < N)
variable (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
variable (hf_map : ∀ v, InSimplex v → InSimplex (f v))

/-- For `k ≤ N`, the diagonal vertex `(k, N - k)` lies on
geometric face 2 of `Δ²`: its coordinate sum equals `N`. -/
private lemma onFaceΔ2_diag (k : ℕ) (hk : k ≤ N) :
    onFaceΔ2 N (k, N - k) 2 := by
  rw [onFaceΔ2_two_iff]
  omega

/-- Strict version of `onFaceΔ2_diag`: bundles the in-range
witness `k + (N - k) ≤ N` (an equality in this case) with the
face-2 condition. This is the precise shape consumed by
`cN2_total_face2_color_ne_two`-style face/Sperner-condition
bridges. -/
private lemma onFaceΔ2_strict_diag (k : ℕ) (hk : k ≤ N) :
    onFaceΔ2_strict N (k, N - k) 2 :=
  ⟨by omega, onFaceΔ2_diag N k hk⟩

/-- `cN2_total` agrees with `cN2` at every `face2_path_odd`
diagonal vertex `(k, N - k)` for `k ≤ N`: the wrapper's
`dif_pos` branch fires because `k + (N - k) = N ≤ N`. This is the
`dif_pos`-specialised companion of `cN2_total_eq` for the S27
assembly's `g k`-evaluation. -/
private lemma cN2_total_diag_eq (k : ℕ) (hk : k ≤ N) :
    cN2_total N hN f hf_map (k, N - k) =
      cN2 N hN f hf_map (k, N - k) (by omega) :=
  cN2_total_eq N hN f hf_map (k, N - k) (by omega)

/-- Sperner condition at the diagonal: for `k ≤ N`, the in-range
coloring `cN2` cannot return color `2` at the `face2_path_odd`
vertex `(k, N - k)`, because that vertex lies on geometric face 2
(`onFaceΔ2_diag`). -/
private lemma cN2_diag_ne_two (k : ℕ) (hk : k ≤ N) :
    cN2 N hN f hf_map (k, N - k) (by omega) ≠ (2 : Fin 3) :=
  cN2_ne_of_onFace N hN f hf_map (k, N - k) (by omega) 2
    (onFaceΔ2_diag N k hk)

/-- Wrapper-level Sperner condition at the diagonal: for `k ≤ N`,
`cN2_total` cannot return color `2` at the `face2_path_odd`
vertex `(k, N - k)`. Direct composition of `cN2_total_diag_eq`
with `cN2_diag_ne_two`; the form consumed by `h_no2` hypotheses
of S22's `isDoor_dim_two_iff_color_change_of_no_color_two` when
the `_hLastFace` discharge carries `cN2_total` rather than the
in-range `cN2`. -/
private lemma cN2_total_diag_ne_two (k : ℕ) (hk : k ≤ N) :
    cN2_total N hN f hf_map (k, N - k) ≠ (2 : Fin 3) := by
  rw [cN2_total_diag_eq N hN f hf_map k hk]
  exact cN2_diag_ne_two N hN f hf_map k hk

end N2DiagFaceCondition

-- ============================================================
-- (S28-prep) `Fin 2`-promotion of the diagonal Sperner condition.
--
-- S27-prep's `cN2_diag_ne_two` / `cN2_total_diag_ne_two` package
-- the diagonal Sperner exclusion as `c ≠ (2 : Fin 3)`. The
-- eventual S27/S28 final-assembly bridge between
-- `face2_path_odd`'s `g : ℕ → Fin 2` and `cN2_total`'s
-- `Fin 3`-valued diagonal restriction needs the strictly
-- stronger `.val < 2` form: the witness that promotes a
-- diagonal color to a `Fin 2` value via the
-- `(0 : Fin 3) ↔ (0 : Fin 2)`, `(1 : Fin 3) ↔ (1 : Fin 2)`
-- identification. This section packages that promotion, mirroring
-- the `Fin.val_ne ⇒ val < bound` pattern already used in
-- `sperner_panchromatic_two`'s `hK_lt_N` / `hcK1` proofs.
--
--   * `cN2_diag_val_lt_two` — `.val < 2` form for in-range `cN2`.
--   * `cN2_total_diag_val_lt_two` — wrapper-level `.val < 2`.
--
-- Each proof reuses S27-prep's `≠ 2` lemma + the `.isLt` bound
-- + `omega`. Independent of in-flight #17571 (S23 color wiring
-- in `(b.1, b.2 + 1)`-endpoint form) and #17621 (S25-prep gridPt
-- coordinate helpers): these consume the wrapper at non-diagonal
-- form and the geometric simplex respectively. The promotion
-- here lives entirely on the `face2_path_odd` `(k, N - k)`-
-- parametrization side and unblocks the eventual `g k ≠ g (k+1)
-- ↔ cN2_total (k, N-k) ≠ cN2_total (k+1, N-(k+1))` color-change
-- correspondence S22's IsDoor bridge will consume.
-- ============================================================

section N2DiagValFinTwo

variable (N : ℕ) (hN : 0 < N)
variable (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
variable (hf_map : ∀ v, InSimplex v → InSimplex (f v))

/-- Strengthening of `cN2_diag_ne_two` (S27-prep) to a `.val < 2`
form: for `k ≤ N`, the in-range diagonal color's `.val` lies in
`{0, 1}`. The pattern matches `sperner_panchromatic_two`'s
`hK_lt_N`/`hcK1` proofs: combine `Fin.ext` to lift `.val ≠ n`
from `c ≠ n`, then `.isLt` + `omega`. -/
private lemma cN2_diag_val_lt_two (k : ℕ) (hk : k ≤ N) :
    (cN2 N hN f hf_map (k, N - k) (by omega)).val < 2 := by
  have hne : cN2 N hN f hf_map (k, N - k) (by omega) ≠ (2 : Fin 3) :=
    cN2_diag_ne_two N hN f hf_map k hk
  have hval_ne : (cN2 N hN f hf_map (k, N - k) (by omega)).val ≠ 2 :=
    fun h => hne (Fin.ext h)
  have hlt := (cN2 N hN f hf_map (k, N - k) (by omega)).isLt
  omega

/-- Wrapper-level companion of `cN2_diag_val_lt_two`: for `k ≤ N`,
`cN2_total`'s `.val` at the diagonal vertex `(k, N - k)` lies in
`{0, 1}`. Composes `cN2_total_diag_eq` (S27-prep) with
`cN2_diag_val_lt_two`. This is the exact form consumed when
defining the `Fin 2`-valued diagonal color function the S27
final-assembly bijection with `face2_path_odd`'s `g` will use. -/
private lemma cN2_total_diag_val_lt_two (k : ℕ) (hk : k ≤ N) :
    (cN2_total N hN f hf_map (k, N - k)).val < 2 := by
  rw [cN2_total_diag_eq N hN f hf_map k hk]
  exact cN2_diag_val_lt_two N hN f hf_map k hk

end N2DiagValFinTwo


-- ============================================================
-- (S29-prep) Top-level `Fin 2`-valued diagonal coloring `gDiag`
-- and its identification with `cN2_total` on the diagonal.
--
-- `face2_path_odd` (Section V) packages its color path via a
-- `let`-bound local `g : ℕ → Fin 2`. To bridge S22's IsDoor
-- correspondence — which carries `cN2_total`-shaped color-change
-- predicates — into `face2_path_odd`'s `g k ≠ g (k + 1)` filter
-- form, the eventual S27/S28 final assembly needs an extracted
-- top-level companion of that `g` plus the equivalence
--
--   gDiag k ≠ gDiag (k + 1)
--     ↔ cN2_total (k, N - k) ≠ cN2_total (k + 1, N - (k + 1)).
--
-- This section packages exactly that bridge. The equivalence
-- rewrites only the right-hand side (the `cN2_total`-side); no
-- refactoring of `face2_path_odd` itself or of in-flight S25/S26
-- work that consumes `face2_path_odd` directly. A future session
-- can substitute `gDiag` into `face2_path_odd`'s `let g := ...`
-- with a definitionally-equal body.
--
--   * `gDiag` — `noncomputable def` matching `face2_path_odd`'s
--     local `g` body verbatim.
--   * `gDiag_out_of_range` — out-of-range default `gDiag k = 1`.
--   * `gDiag_in_range_eq_zero_iff` — for `k ≤ N`, `gDiag k = 0`
--     iff the in-range diagonal `cN2`'s `.val = 0`.
--   * `gDiag_in_range_eq_zero_iff_cN2_total` — wrapper variant
--     reading the discriminant off `cN2_total` via S27-prep's
--     `cN2_total_diag_eq`.
--   * `gDiag_val_eq_cN2_total_diag_val` — the central val
--     identification. Uses S28-prep's `cN2_total_diag_val_lt_two`
--     to force both `cN2_total`'s `.val` and `gDiag`'s `.val`
--     into `{0, 1}`, where the discriminator is order-preserving.
--   * `gDiag_eq_iff_cN2_total_diag_eq` — for `k, m ≤ N`,
--     `gDiag k = gDiag m ↔ cN2_total (k, N - k) =
--     cN2_total (m, N - m)`. Pulled back from the val
--     identification via `Fin.ext`.
--   * `gDiag_ne_iff_cN2_total_diag_ne` — contrapositive
--     specialised to consecutive indices `k, k + 1` (the form
--     S22's IsDoor bridge consumes).
--
-- All proofs reuse S27-prep's `cN2_total_diag_eq` and S28-prep's
-- `cN2_total_diag_val_lt_two`; no new Mathlib dependencies.
-- Each lemma is short (3-10 lines) and syntactically isolated
-- (additions append below the existing `N2DiagValFinTwo` section,
-- not touching the broken `t1_ne_t2` / `diagonal_in_t1_iff` block
-- at lines 1068/1085/1093 in `N2BoundaryAnalysis` — so this PR
-- does not interact with the parent file's pre-existing build
-- break per the established (build pending) precedent).
-- ============================================================

section N2DiagFin2Coloring

variable (N : ℕ) (hN : 0 < N)
variable (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
variable (hf_map : ∀ v, InSimplex v → InSimplex (f v))

/-- `Fin 2`-valued color along the anti-diagonal of `Δ²`. Mirrors
the local `g` defined inside `face2_path_odd` (Section V): for
in-range indices `k ≤ N`, the discriminator `(cN2 ...).val = 0 ↦
0, ≠ 0 ↦ 1` compresses the diagonal vertex color to `{0, 1}` (the
`.val = 2` case is excluded by Sperner on face 2 — see
`cN2_diag_ne_two`). Out-of-range indices default to `1`. -/
private noncomputable def gDiag : ℕ → Fin 2 := fun k =>
  if hk : k ≤ N then
    if (cN2 N hN f hf_map (k, N - k) (by omega)).val = 0 then 0 else 1
  else 1

/-- Out-of-range default: for `N < k`, `gDiag k = 1`. -/
private lemma gDiag_out_of_range (k : ℕ) (hk : N < k) :
    gDiag N hN f hf_map k = 1 := by
  unfold gDiag
  rw [dif_neg (by omega)]

/-- In-range `gDiag = 0` characterised via the in-range `cN2`'s
`.val = 0`. Direct from the definition. -/
private lemma gDiag_in_range_eq_zero_iff (k : ℕ) (hk : k ≤ N) :
    gDiag N hN f hf_map k = 0 ↔
      (cN2 N hN f hf_map (k, N - k) (by omega)).val = 0 := by
  unfold gDiag
  rw [dif_pos hk]
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · refine ⟨fun heq => ?_, fun heq => (h heq).elim⟩
    exact absurd heq (by decide)

/-- Wrapper-level characterisation: for `k ≤ N`, `gDiag k = 0`
iff `cN2_total`'s `.val = 0` at the diagonal vertex
`(k, N - k)`. Composes `gDiag_in_range_eq_zero_iff` with
S27-prep's `cN2_total_diag_eq`. -/
private lemma gDiag_in_range_eq_zero_iff_cN2_total (k : ℕ) (hk : k ≤ N) :
    gDiag N hN f hf_map k = 0 ↔
      (cN2_total N hN f hf_map (k, N - k)).val = 0 := by
  rw [gDiag_in_range_eq_zero_iff N hN f hf_map k hk,
      cN2_total_diag_eq N hN f hf_map k hk]

/-- Central val identification: for `k ≤ N`,
`(gDiag k).val = (cN2_total (k, N - k)).val`. The proof case-
splits on whether the diagonal `cN2_total`'s `.val` is `0` or
`1` (both possibilities by S28-prep's `cN2_total_diag_val_lt_two`);
in each case `gDiag` takes the matching `Fin 2` value. -/
private lemma gDiag_val_eq_cN2_total_diag_val (k : ℕ) (hk : k ≤ N) :
    (gDiag N hN f hf_map k).val =
      (cN2_total N hN f hf_map (k, N - k)).val := by
  have hkv := cN2_total_diag_val_lt_two N hN f hf_map k hk
  rcases Decidable.em
      ((cN2_total N hN f hf_map (k, N - k)).val = 0) with h0 | h0
  · have hg0 : gDiag N hN f hf_map k = 0 :=
      (gDiag_in_range_eq_zero_iff_cN2_total N hN f hf_map k hk).mpr h0
    rw [hg0, h0]
    rfl
  · have hgne : gDiag N hN f hf_map k ≠ 0 := fun h =>
      h0 ((gDiag_in_range_eq_zero_iff_cN2_total N hN f hf_map k hk).mp h)
    have hg_val_ne : (gDiag N hN f hf_map k).val ≠ 0 :=
      fun h => hgne (Fin.ext h)
    have hg_lt : (gDiag N hN f hf_map k).val < 2 :=
      (gDiag N hN f hf_map k).isLt
    omega

/-- For `k, m ≤ N`, `gDiag` agrees at `k, m` iff `cN2_total`
agrees at the diagonal vertices `(k, N - k), (m, N - m)`. Pulled
back from `gDiag_val_eq_cN2_total_diag_val` via `Fin.ext` /
`congrArg Fin.val`. -/
private lemma gDiag_eq_iff_cN2_total_diag_eq
    (k m : ℕ) (hk : k ≤ N) (hm : m ≤ N) :
    gDiag N hN f hf_map k = gDiag N hN f hf_map m ↔
      cN2_total N hN f hf_map (k, N - k) =
        cN2_total N hN f hf_map (m, N - m) := by
  have hgk := gDiag_val_eq_cN2_total_diag_val N hN f hf_map k hk
  have hgm := gDiag_val_eq_cN2_total_diag_val N hN f hf_map m hm
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have hv := congrArg Fin.val h
    rw [hgk, hgm] at hv
    exact Fin.ext hv
  · have hv := congrArg Fin.val h
    rw [← hgk, ← hgm] at hv
    exact Fin.ext hv

/-- Contrapositive of `gDiag_eq_iff_cN2_total_diag_eq`, specialised
to consecutive indices `k, k + 1` (the precise form S22's IsDoor
bridge consumes when relating `face2_path_odd`'s color-change
filter to the `cN2_total`-side color predicate). -/
private lemma gDiag_ne_iff_cN2_total_diag_ne (k : ℕ) (hk1 : k + 1 ≤ N) :
    gDiag N hN f hf_map k ≠ gDiag N hN f hf_map (k + 1) ↔
      cN2_total N hN f hf_map (k, N - k) ≠
        cN2_total N hN f hf_map (k + 1, N - (k + 1)) := by
  rw [Ne, Ne, not_iff_not]
  exact gDiag_eq_iff_cN2_total_diag_eq
    N hN f hf_map k (k + 1) (by omega) hk1

end N2DiagFin2Coloring

-- ============================================================
-- SECTION (S30-prep): face2_path_odd restated via gDiag
-- ============================================================
-- S29-prep (PR #17985, merged) introduced the top-level
-- `gDiag : ℕ → Fin 2` whose body matches the local `let g`
-- inside `face2_path_odd` (Section V) verbatim. This section
-- packages the immediate corollary: the odd-cardinality
-- conclusion of `face2_path_odd` also holds for the filter
-- expressed via `gDiag` directly, freeing downstream consumers
-- (S22's IsDoor color-change bridge, the eventual `_hLastFace`
-- assembly) from having to re-unfold the local `let` binding
-- at every use site.
--
-- Proof is a one-liner: `unfold gDiag` exposes the same body
-- as `face2_path_odd`'s local `g`, so the two filter predicates
-- are definitionally equal (proof terms `(by omega)` differ
-- only at the proof-irrelevant `b.1+b.2 ≤ N` premise of `cN2`).
-- Composes with S29-prep's
-- `gDiag_ne_iff_cN2_total_diag_ne` to give the eventual
-- odd-count statement in `cN2_total`-form that S22 +
-- S25's `_hLastFace`-filter ↔ `satDiagBases` correspondence
-- consume.
--
-- Independent of in-flight S23 (PR #17571, N2LastFaceColors
-- color wiring in `(b.1, b.2 + 1)`-endpoint form), S25-prep
-- (PR #17621, gridPt coordinate helpers), and S28-prep-
-- color-change-iff (PR #17984, pointwise `if-shape ≠ ↔
-- cN2_total ≠` bridge in `N2DiagColorChangeIff`): the new
-- section lives entirely on the `face2_path_odd`-output side
-- and consumes only the merged top-level `gDiag`.
--
-- Build status: pending per the persistent `t1_ne_t2` /
-- `diagonal_in_t1_iff` drift in `N2BoundaryAnalysis` (lines
-- 1068/1085/1093). The new section is at the very end of the
-- file (lines 3360–3387 post-this-PR), well past the broken
-- `omega` lines, matching the established "build pending"
-- precedent for additions in disjoint file regions.
-- ============================================================

section N2GDiagPathOdd

variable (N : ℕ) (hN : 0 < N)
variable (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
variable (hf_map : ∀ v, InSimplex v → InSimplex (f v))

/-- Restated `face2_path_odd` using the top-level `gDiag`
(S29-prep) in place of its internal `let g`. The two have
identical bodies, so the filter predicates coincide after
`unfold gDiag`. -/
private lemma face2_path_odd_gDiag :
    Odd ((Finset.range N).filter
      (fun k => gDiag N hN f hf_map k ≠ gDiag N hN f hf_map (k + 1))).card := by
  unfold gDiag
  exact face2_path_odd N hN f hf_map

end N2GDiagPathOdd

-- ============================================================
-- (S33) Final assembly: `_hLastFace` discharge + n=2 Sperner
-- panchromatic theorem.
--
-- The bijection: pairs `(s, k)` in the `_hLastFace` filter of
-- `Triangulation.boundary_doors_odd` for `simData2 N` correspond
-- exactly to the color-changing diagonal edges counted by
-- `face2_path_odd_gDiag`, via `p ↦ (vertex p.1 p.2).1` (the first
-- coordinate of the dropped vertex):
--
--   * forward: S21A (`t1_lastFace_implies_satDiag`) + S24
--     (`t2_adj_ne_none`) pin the cell to `t1 b` with
--     `b ∈ satDiagBases N` and `p.2` the self-drop index; the S22
--     IsDoor bridge converts the door condition into the gDiag
--     color change `gDiag b.1 ≠ gDiag (b.1 + 1)`.
--   * backward: S25-rev (`satDiag_self_drop_*`) reconstructs the
--     filter member from `k ∈ Finset.range N`.
--
-- `face2_path_odd_gDiag` (S30) supplies oddness; then
-- `Triangulation.boundary_doors_odd` + `Triangulation.sperner`
-- produce the panchromatic cell, and witness extraction mirrors
-- the n=1 proof (`spernerColor_le` + `gridPt_topSimps2_coord_diameter`).
-- ============================================================

section N2LastFaceAssembly

variable (N : ℕ) (hN : 0 < N)
variable (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
variable (hf_map : ∀ v, InSimplex v → InSimplex (f v))

/-- At the self-drop index of a saturating-diagonal base, the
adjacency is `none`: the diagonal face has exactly one container
(`diagonal_card_eq_one_of_t1_boundary`). -/
private lemma satDiag_self_drop_adj_none
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) {k : Fin 3}
    (hk : (simData2 N).vertexEnum (t1 b)
      (satDiagBases_t1_in_topSimps2 N hb) k = b) :
    ((simData2 N).toTriangulation).adj
      ⟨t1 b, satDiagBases_t1_in_topSimps2 N hb⟩ k = none := by
  set hS := satDiagBases_t1_in_topSimps2 N hb with hS_def
  apply (SimplicialAdjFnHelper.adjFn_eq_none_iff_card_le_one
    (simData2 N) ⟨t1 b, hS⟩ k).mpr
  have h_face_eq : (simData2 N).faceOf (t1 b) hS k =
      ({(b.1, b.2 + 1), (b.1 + 1, b.2)} : Finset (ℕ × ℕ)) := by
    show (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) = _
    rw [hk]; exact t1_erase_third b
  have h_containers_eq : ∀ (f' : Finset (ℕ × ℕ)),
      (simData2 N).containersOf f' =
        (topSimps2 N).filter (fun s => f' ⊆ s) := fun _ => rfl
  rw [h_face_eq, h_containers_eq]
  have hbd : N ≤ b.1 + b.2 + 1 := by
    obtain ⟨_, _, hsat⟩ := (satDiagBases_mem_iff N b).mp hb
    omega
  exact le_of_eq (diagonal_card_eq_one_of_t1_boundary N
    (satDiagBases_subset_t1Bases N hb) hbd)

/-- At the self-drop configuration, there are two distinct non-drop
indices enumerating the diagonal endpoints `(b.1, b.2+1)` and
`(b.1+1, b.2)`. -/
private lemma satDiag_self_drop_endpoint_indices
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) {k : Fin 3}
    (hk : (simData2 N).vertexEnum (t1 b)
      (satDiagBases_t1_in_topSimps2 N hb) k = b) :
    ∃ i₁ i₂ : Fin 3, i₁ ≠ k ∧ i₂ ≠ k ∧ i₁ ≠ i₂ ∧
      (simData2 N).vertexEnum (t1 b)
        (satDiagBases_t1_in_topSimps2 N hb) i₁ = (b.1, b.2 + 1) ∧
      (simData2 N).vertexEnum (t1 b)
        (satDiagBases_t1_in_topSimps2 N hb) i₂ = (b.1 + 1, b.2) := by
  set hS := satDiagBases_t1_in_topSimps2 N hb with hS_def
  have h_img := (simData2 N).vertexEnum_image_univ (t1 b) hS
  have h1_mem : ((b.1, b.2 + 1) : ℕ × ℕ) ∈ t1 b := by
    simp only [t1, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have h2_mem : ((b.1 + 1, b.2) : ℕ × ℕ) ∈ t1 b := by
    simp only [t1, Finset.mem_insert, Finset.mem_singleton]
    tauto
  rw [← h_img] at h1_mem h2_mem
  obtain ⟨i₁, _, hi₁⟩ := Finset.mem_image.mp h1_mem
  obtain ⟨i₂, _, hi₂⟩ := Finset.mem_image.mp h2_mem
  refine ⟨i₁, i₂, ?_, ?_, ?_, hi₁, hi₂⟩
  · rintro rfl
    rw [hk] at hi₁
    exact absurd (congrArg Prod.snd hi₁) (by omega)
  · rintro rfl
    rw [hk] at hi₂
    exact absurd (congrArg Prod.fst hi₂) (by omega)
  · rintro rfl
    rw [hi₁] at hi₂
    exact absurd (congrArg Prod.fst hi₂) (by omega)

/-- At the self-drop configuration, the door condition for the
coloring `cN2_total` is equivalent to a `gDiag` color change
across the diagonal edge. -/
private lemma satDiag_self_drop_isDoor_iff
    {b : ℕ × ℕ} (hb : b ∈ satDiagBases N) {k : Fin 3}
    (hk : (simData2 N).vertexEnum (t1 b)
      (satDiagBases_t1_in_topSimps2 N hb) k = b) :
    CellComplex.IsDoor (cN2_total N hN f hf_map)
        (((simData2 N).toTriangulation).toCellComplex)
        ⟨t1 b, satDiagBases_t1_in_topSimps2 N hb⟩ k ↔
      gDiag N hN f hf_map b.1 ≠ gDiag N hN f hf_map (b.1 + 1) := by
  set hS := satDiagBases_t1_in_topSimps2 N hb with hS_def
  obtain ⟨i₁, i₂, hi₁k, hi₂k, hi₁₂, hv₁, hv₂⟩ :=
    satDiag_self_drop_endpoint_indices N hb hk
  have hb1_le : b.1 ≤ N := (satDiagBases_fst_lt N hb).le
  have hb1s_le : b.1 + 1 ≤ N := satDiagBases_succ_le N hb
  have he₁ := satDiagBases_first_endpoint_face2_path_form N hb
  have he₂ := satDiagBases_second_endpoint_face2_path_form N hb
  have h_no2 : ∀ i : Fin 3, i ≠ k →
      cN2_total N hN f hf_map
        ((((simData2 N).toTriangulation).toCellComplex).vertex
          ⟨t1 b, hS⟩ i) ≠ (2 : Fin 3) := by
    intro i hik
    have h_mem : (simData2 N).vertexEnum (t1 b) hS i ∈
        (t1 b).erase ((simData2 N).vertexEnum (t1 b) hS k) :=
      Finset.mem_erase.mpr
        ⟨fun heq => hik ((simData2 N).vertexEnum_injective (t1 b) hS heq),
         (simData2 N).vertexEnum_mem (t1 b) hS i⟩
    rw [hk, t1_erase_third b] at h_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at h_mem
    show cN2_total N hN f hf_map
        ((simData2 N).vertexEnum (t1 b) hS i) ≠ (2 : Fin 3)
    rcases h_mem with heq | heq
    · rw [heq, he₁]
      exact cN2_total_diag_ne_two N hN f hf_map b.1 hb1_le
    · rw [heq, he₂]
      exact cN2_total_diag_ne_two N hN f hf_map (b.1 + 1) hb1s_le
  rw [SimplicialAdjFnHelper.isDoor_dim_two_iff_color_change_of_no_color_two
    (((simData2 N).toTriangulation).toCellComplex)
    (cN2_total N hN f hf_map) ⟨t1 b, hS⟩ k h_no2 hi₁k hi₂k hi₁₂]
  have hv₁' : (((simData2 N).toTriangulation).toCellComplex).vertex
      ⟨t1 b, hS⟩ i₁ = ((b.1 : ℕ), N - b.1) := by
    show (simData2 N).vertexEnum (t1 b) hS i₁ = _
    rw [hv₁]; exact he₁
  have hv₂' : (((simData2 N).toTriangulation).toCellComplex).vertex
      ⟨t1 b, hS⟩ i₂ = ((b.1 + 1 : ℕ), N - (b.1 + 1)) := by
    show (simData2 N).vertexEnum (t1 b) hS i₂ = _
    rw [hv₂]; exact he₂
  rw [hv₁', hv₂']
  exact (gDiag_ne_iff_cN2_total_diag_ne N hN f hf_map b.1 hb1s_le).symm

/-- Forward extraction for members of the `_hLastFace` filter: the
cell is a `t1 b` with `b ∈ satDiagBases N` and the face index is
the self-drop index. Composes S21A (t1 side) with S24 (t2
extinction). -/
private lemma lastFace_filter_extract
    (s : ((simData2 N).toTriangulation).Cell) (k : Fin 3)
    (h_adj : ((simData2 N).toTriangulation).adj s k = none)
    (h_face2 : ∀ j : Fin 3, j ≠ k →
      onFaceΔ2_strict N (((simData2 N).toTriangulation).vertex s j)
        (2 : Fin 3)) :
    ∃ (b : ℕ × ℕ) (hb : b ∈ satDiagBases N),
      s = ⟨t1 b, satDiagBases_t1_in_topSimps2 N hb⟩ ∧
      (simData2 N).vertexEnum (t1 b)
        (satDiagBases_t1_in_topSimps2 N hb) k = b := by
  obtain ⟨S, hS⟩ := s
  rcases (topSimps2_mem_iff N S).mp hS with ⟨b, hb, rfl⟩ | ⟨c, hc, rfl⟩
  · obtain ⟨hb_sat, h_drop⟩ := t1_lastFace_implies_satDiag N hb k h_face2
    exact ⟨b, hb_sat, Subtype.ext rfl, h_drop⟩
  · exact absurd h_adj (t2_adj_ne_none N hc k)

/-- **The `_hLastFace` cardinality identity**: boundary doors on
geometric face 2 biject with `gDiag` color changes on
`Finset.range N`, via `p ↦ (vertex p.1 p.2).1` (the first
coordinate of the dropped vertex). -/
private lemma lastFace_card_eq :
    (Finset.univ.filter
      (fun p : ((simData2 N).toTriangulation).Cell × Fin 3 =>
        CellComplex.IsDoor (cN2_total N hN f hf_map)
          (((simData2 N).toTriangulation).toCellComplex) p.1 p.2 ∧
        ((simData2 N).toTriangulation).adj p.1 p.2 = none ∧
        (∀ j : Fin 3, j ≠ p.2 →
          onFaceΔ2_strict N
            (((simData2 N).toTriangulation).vertex p.1 j)
            (2 : Fin 3)))).card =
    ((Finset.range N).filter
      (fun k => gDiag N hN f hf_map k ≠ gDiag N hN f hf_map (k + 1))).card := by
  apply Finset.card_bij
    (fun p _ => (((simData2 N).toTriangulation).vertex p.1 p.2).1)
  · -- maps into the target filter
    rintro ⟨s, k⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hDoor, hAdj, hFace2⟩ := hp
    obtain ⟨b, hb, rfl, hdrop⟩ := lastFace_filter_extract N s k hAdj hFace2
    have hvk : (((simData2 N).toTriangulation).vertex
        ⟨t1 b, satDiagBases_t1_in_topSimps2 N hb⟩ k) = b := hdrop
    show (((simData2 N).toTriangulation).vertex
        ⟨t1 b, satDiagBases_t1_in_topSimps2 N hb⟩ k).1 ∈ _
    rw [hvk, Finset.mem_filter, Finset.mem_range]
    exact ⟨satDiagBases_fst_lt N hb,
      (satDiag_self_drop_isDoor_iff N hN f hf_map hb hdrop).mp hDoor⟩
  · -- injective
    rintro ⟨s₁, k₁⟩ hp₁ ⟨s₂, k₂⟩ hp₂ h_eq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp₁ hp₂
    obtain ⟨_, hAdj₁, hFace₁⟩ := hp₁
    obtain ⟨_, hAdj₂, hFace₂⟩ := hp₂
    obtain ⟨b₁, hb₁, rfl, hdrop₁⟩ :=
      lastFace_filter_extract N s₁ k₁ hAdj₁ hFace₁
    obtain ⟨b₂, hb₂, rfl, hdrop₂⟩ :=
      lastFace_filter_extract N s₂ k₂ hAdj₂ hFace₂
    have hv₁ : (((simData2 N).toTriangulation).vertex
        ⟨t1 b₁, satDiagBases_t1_in_topSimps2 N hb₁⟩ k₁) = b₁ := hdrop₁
    have hv₂ : (((simData2 N).toTriangulation).vertex
        ⟨t1 b₂, satDiagBases_t1_in_topSimps2 N hb₂⟩ k₂) = b₂ := hdrop₂
    have h_fst : b₁.1 = b₂.1 := by
      have h' : (((simData2 N).toTriangulation).vertex
          ⟨t1 b₁, satDiagBases_t1_in_topSimps2 N hb₁⟩ k₁).1 =
        (((simData2 N).toTriangulation).vertex
          ⟨t1 b₂, satDiagBases_t1_in_topSimps2 N hb₂⟩ k₂).1 := h_eq
      rwa [hv₁, hv₂] at h'
    have hb_eq : b₁ = b₂ := by
      rw [satDiagBases_eq_pair_fst N hb₁, satDiagBases_eq_pair_fst N hb₂,
        h_fst]
    subst hb_eq
    have hk_eq : k₁ = k₂ :=
      satDiag_self_drop_index_unique N hb₁ hdrop₁ hdrop₂
    subst hk_eq
    rfl
  · -- surjective
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, hgne⟩ := hk
    have hb : ((k, N - 1 - k) : ℕ × ℕ) ∈ satDiagBases N := by
      rw [satDiagBases_mem_iff]
      exact ⟨hkN, by show N - 1 - k < N; omega,
        by show k + (N - 1 - k) + 1 = N; omega⟩
    obtain ⟨kb, hkb⟩ := satDiag_self_drop_index_exists N hb
    refine ⟨(⟨t1 (k, N - 1 - k), satDiagBases_t1_in_topSimps2 N hb⟩, kb),
      ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _,
        (satDiag_self_drop_isDoor_iff N hN f hf_map hb hkb).mpr hgne,
        satDiag_self_drop_adj_none N hb hkb,
        satDiag_self_drop_face2 N hb hkb⟩
    · show ((simData2 N).vertexEnum (t1 (k, N - 1 - k))
          (satDiagBases_t1_in_topSimps2 N hb) kb).1 = k
      rw [hkb]

/-- Oddness of the `_hLastFace` filter for `simData2 N`: transported
from `face2_path_odd_gDiag` across `lastFace_card_eq`. -/
private lemma lastFace_odd :
    Odd (Finset.univ.filter
      (fun p : ((simData2 N).toTriangulation).Cell × Fin 3 =>
        CellComplex.IsDoor (cN2_total N hN f hf_map)
          (((simData2 N).toTriangulation).toCellComplex) p.1 p.2 ∧
        ((simData2 N).toTriangulation).adj p.1 p.2 = none ∧
        (∀ j : Fin 3, j ≠ p.2 →
          onFaceΔ2_strict N
            (((simData2 N).toTriangulation).vertex p.1 j)
            (2 : Fin 3)))).card := by
  rw [lastFace_card_eq N hN f hf_map]
  exact face2_path_odd_gDiag N hN f hf_map

end N2LastFaceAssembly

-- ============================================================
-- (S33 final) n=2 Sperner panchromatic — fully proved.
-- ============================================================

section N2Panchromatic

/-- **n=2 sperner_panchromatic**, fully proved (no sorry, no axiom).

The Type-1/Type-2 triangulation of Δ² (`simData2 N`) carries the
Sperner coloring `cN2_total`. Boundary doors are odd
(`Triangulation.boundary_doors_odd` with the four slots discharged
by `cN2_total_isSpernerColoring`, `boundaryOnFace_simData2`,
`SpernerLowerDimHelper.sperner_lowerDim_card_even`, and
`lastFace_odd`), so `Triangulation.sperner` yields a panchromatic
cell; its three vertices give witnesses with pairwise coordinate
distance ≤ 2/N. -/
theorem sperner_panchromatic_two (N : ℕ) (hN : 0 < N)
    (f : (Fin 3 → ℝ) → Fin 3 → ℝ)
    (hf_map : ∀ v, InSimplex v → InSimplex (f v)) :
    ∃ v : Fin 3 → Fin 3 → ℝ,
        (∀ i, InSimplex (v i)) ∧
        (∀ i : Fin 3, f (v i) i ≤ v i i) ∧
        (∀ (i j : Fin 3) (l : Fin 3), |v i l - v j l| ≤ (2 : ℝ) / N) := by
  have h_bdry :
      Odd (Finset.univ.filter
        (fun p : ((simData2 N).toTriangulation).Cell × Fin 3 =>
          CellComplex.IsDoor (cN2_total N hN f hf_map)
            (((simData2 N).toTriangulation).toCellComplex) p.1 p.2 ∧
          ((simData2 N).toTriangulation).adj p.1 p.2 = none)).card :=
    Triangulation.boundary_doors_odd
      ((simData2 N).toTriangulation)
      (cN2_total N hN f hf_map)
      (onFaceΔ2_strict N)
      (cN2_total_isSpernerColoring N hN f hf_map)
      (boundaryOnFace_simData2 N)
      (fun faceIdx hlt =>
        SpernerLowerDimHelper.sperner_lowerDim_card_even
          ((simData2 N).toTriangulation) (cN2_total N hN f hf_map)
          (onFaceΔ2_strict N)
          (cN2_total_isSpernerColoring N hN f hf_map) faceIdx hlt)
      (lastFace_odd N hN f hf_map)
  obtain ⟨s, hs_pan⟩ :=
    Triangulation.sperner ((simData2 N).toTriangulation)
      (cN2_total N hN f hf_map) h_bdry
  have h_surj : Function.Surjective
      (cN2_total N hN f hf_map ∘
        (((simData2 N).toTriangulation).toCellComplex).vertex s) := hs_pan
  choose idx hidx using h_surj
  have hvb_mem : ∀ i : Fin 3,
      (simData2 N).vertexEnum s.1 s.2 (idx i) ∈ s.1 := fun i =>
    (simData2 N).vertexEnum_mem s.1 s.2 (idx i)
  have hvb_range : ∀ i : Fin 3,
      ((simData2 N).vertexEnum s.1 s.2 (idx i)).1 +
        ((simData2 N).vertexEnum s.1 s.2 (idx i)).2 ≤ N := fun i =>
    topSimps2_vertex_in_range N s.2 (hvb_mem i)
  refine ⟨fun i => gridPt N ((simData2 N).vertexEnum s.1 s.2 (idx i)),
    ?_, ?_, ?_⟩
  · intro i
    exact gridPt_inSimplex N hN _ (hvb_range i)
  · intro i
    have hcolor : cN2 N hN f hf_map
        ((simData2 N).vertexEnum s.1 s.2 (idx i)) (hvb_range i) = i := by
      rw [← cN2_total_eq N hN f hf_map _ (hvb_range i)]
      exact hidx i
    have h_le := spernerColor_le
      (gridPt_inSimplex N hN _ (hvb_range i))
      (hf_map _ (gridPt_inSimplex N hN _ (hvb_range i)))
    rw [show spernerColor
        (gridPt N ((simData2 N).vertexEnum s.1 s.2 (idx i)))
        (f (gridPt N ((simData2 N).vertexEnum s.1 s.2 (idx i))))
        (gridPt_inSimplex N hN _ (hvb_range i))
        (hf_map _ (gridPt_inSimplex N hN _ (hvb_range i))) =
      cN2 N hN f hf_map ((simData2 N).vertexEnum s.1 s.2 (idx i))
        (hvb_range i) from rfl, hcolor] at h_le
    exact h_le
  · intro i j l
    exact gridPt_topSimps2_coord_diameter N hN s.1 s.2 _ _
      (hvb_mem i) (hvb_mem j) l

end N2Panchromatic

end SpernerFreudSimp
