/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# Sperner's Lemma via Abstract Cell Complex

This file proves Sperner's lemma for any abstract cell complex satisfying
adjacency axioms, using the door-counting parity argument.

## Main definitions

* `SpernerAbstract.CellComplex`: Abstract cell complex with adjacency.
* `SpernerAbstract.IsFC`: Fully colored (panchromatic) cell.
* `SpernerAbstract.isDoorAt`: Door predicate for a facet.

## Main statements

* `SpernerAbstract.even_card_fpf_invol`: Fixed-point-free involution parity.
* `SpernerAbstract.abstract_door_parity`: Per-cell door parity.
* `SpernerAbstract.sperner_parity`: **Sperner Parity Theorem**.
* `SpernerAbstract.sperner`: **Sperner's Lemma**.

## Tags

Sperner, combinatorics, parity, triangulation, door-counting
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace SpernerAbstract

open Finset BigOperators

-- ============================================================
-- SECTION I: ZMod 2 Parity Helpers
-- ============================================================

private lemma odd_of_zmod2_one (m : ℕ) (h : (m : ZMod 2) = 1) : Odd m := by
  rw [Nat.odd_iff]
  have hval := ZMod.val_natCast (n := 2) m
  rw [h] at hval; simpa using hval.symm

-- ============================================================
-- SECTION II: Abstract Cell Complex
-- ============================================================

/-- An abstract cell complex with adjacency. Each cell has `d + 1` vertices
from type `V`. Interior facets pair up via `adj`; boundary facets have
`adj = none`. -/
structure CellComplex (V : Type*) [DecidableEq V] (d : ℕ) where
  Simplex : Type
  simplex_decidableEq : DecidableEq Simplex
  simplex_fintype : Fintype Simplex
  vertices : Simplex → Fin (d + 1) → V
  vertices_injective : ∀ s, Function.Injective (vertices s)
  adj : Simplex → Fin (d + 1) → Option (Simplex × Fin (d + 1))
  adj_symm : ∀ s k s' k', adj s k = some (s', k') → adj s' k' = some (s, k)
  adj_vertices : ∀ s k s' k', adj s k = some (s', k') →
    (Finset.univ.erase k).image (vertices s) =
    (Finset.univ.erase k').image (vertices s')
  adj_ne : ∀ s k s' k', adj s k = some (s', k') → s ≠ s'

attribute [instance] SpernerAbstract.CellComplex.simplex_decidableEq
attribute [instance] SpernerAbstract.CellComplex.simplex_fintype

-- ============================================================
-- SECTION III: Door and FC Definitions
-- ============================================================

variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- A cell is fully colored: the coloring is surjective on its vertices. -/
def IsFC (c : V → Fin (d + 1)) (K : CellComplex V d) (s : K.Simplex) : Prop :=
  Function.Surjective (c ∘ K.vertices s)

/-- A facet `(s, k)` is a "door": removing vertex `k`, the remaining `d` vertices
carry all colors in `{0, ..., d-1}`. -/
def isDoorAt (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Simplex) (k : Fin (d + 1)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ c (K.vertices s i) = Fin.castSucc j

instance decIsFC (c : V → Fin (d + 1)) (K : CellComplex V d) (s : K.Simplex) :
    Decidable (IsFC c K s) := by
  unfold IsFC Function.Surjective; exact inferInstance

instance decIsDoorAt (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Simplex) (k : Fin (d + 1)) :
    Decidable (isDoorAt c K s k) := by
  unfold isDoorAt; exact inferInstance

-- ============================================================
-- SECTION IV: Abstract Involution Parity
-- ============================================================

/-- A fixed-point-free involution on a finite set has even cardinality. -/
theorem even_card_fpf_invol {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α)
    (hInv : ∀ x ∈ S, f (f x) = x)
    (hMem : ∀ x ∈ S, f x ∈ S)
    (hNe  : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hempty : S = ∅
    · rw [hempty]; simp
    · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hempty
      set y := f x with hy_def
      have hy : y ∈ S := hMem x hx
      have hxy : x ≠ y := (hNe x hx).symm
      set S' := (S.erase y).erase x
      have hS'_sub : S' ⊂ S := by
        apply ssubset_of_subset_of_ne
        · intro a ha; simp [S'] at ha; exact ha.2.2
        · intro heq; have := heq ▸ hx; simp [S'] at this
      have hcard : S.card = S'.card + 2 := by
        have hcard1 : S.card ≥ 1 := Finset.one_le_card.mpr ⟨x, hx⟩
        have h1 : (S.erase y).card = S.card - 1 := Finset.card_erase_of_mem hy
        have h2 : x ∈ S.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
        have h3 : S'.card = (S.erase y).card - 1 := Finset.card_erase_of_mem h2
        have hcard2 : (S.erase y).card ≥ 1 := Finset.one_le_card.mpr ⟨x, h2⟩
        omega
      rw [hcard]
      have hf_S' : ∀ a ∈ S', f a ∈ S' := by
        intro a ha
        simp only [S', Finset.mem_erase] at ha ⊢
        refine ⟨?_, ?_, hMem a ha.2.2⟩
        · -- f a ≠ x
          intro h
          have hinv_a := hInv a ha.2.2
          rw [h] at hinv_a
          exact ha.2.1 (hy_def.symm ▸ hinv_a).symm
        · -- f a ≠ y
          intro h
          have hinv_a := hInv a ha.2.2
          rw [h, show f y = x from by rw [hy_def]; exact hInv x hx] at hinv_a
          exact ha.1 hinv_a.symm
      have hS'_sub_le : S' ⊆ S := hS'_sub.subset
      have hS'_even := ih S' hS'_sub
          (fun a ha => hInv a (hS'_sub_le ha))
          hf_S'
          (fun a ha => hNe a (hS'_sub_le ha))
      exact hS'_even.add ⟨1, rfl⟩

-- ============================================================
-- SECTION V: Abstract Door Parity
-- ============================================================

private lemma door_parity_all_small (d : ℕ) (f : Fin (d + 1) → Fin d)
    (hcov : ∀ j : Fin d, ∃ i, f i = j) :
    Even (Finset.univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = j)).card := by
  have hcard_ge : ∀ c : Fin d,
      (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card ≥ 1 := by
    intro c; obtain ⟨i, hi⟩ := hcov c
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have htotal : ∑ c : Fin d,
      (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card = d + 1 := by
    rw [← Finset.card_biUnion (by
      intro x _ y _ hxy
      apply Finset.disjoint_filter.mpr
      intro i _ h1 h2; exact hxy (h1.symm.trans h2))]
    have hbU : Finset.biUnion Finset.univ (fun c : Fin d =>
        Finset.univ.filter (fun i : Fin (d + 1) => f i = c)) = Finset.univ := by
      ext i; constructor
      · intro _; exact Finset.mem_univ _
      · intro _
        rw [Finset.mem_biUnion]
        exact ⟨f i, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩⟩
    rw [hbU, Finset.card_univ, Fintype.card_fin]
  have hexcess : ∑ c : Fin d,
      ((Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1) = 1 := by
    have hadd : ∀ c : Fin d, (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1 +
        1 = (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card := by
      intro c; have := hcard_ge c; omega
    have := Finset.sum_congr (show (Finset.univ : Finset (Fin d)) = Finset.univ from rfl)
      (fun c _ => hadd c)
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      htotal, smul_eq_mul] at this
    omega
  obtain ⟨c₀, hc₀_eq, hc₀_rest⟩ : ∃ c₀ : Fin d,
      (Finset.univ.filter (fun i : Fin (d + 1) => f i = c₀)).card = 2 ∧
      ∀ c ≠ c₀, (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card = 1 := by
    have : ∃ c₀ ∈ Finset.univ,
        0 < (Finset.univ.filter (fun i : Fin (d + 1) => f i = c₀)).card - 1 := by
      by_contra hall; push_neg at hall
      have h0 := fun c => Nat.eq_zero_of_le_zero (hall c (Finset.mem_univ _))
      simp [h0] at hexcess
    obtain ⟨c₀, _, hc₀⟩ := this
    refine ⟨c₀, ?_, ?_⟩
    · by_contra hne2
      have hge2 : (Finset.univ.filter (fun i : Fin (d + 1) => f i = c₀)).card - 1 ≥ 2 := by omega
      let F : Fin d → ℕ := fun c => (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1
      have hFc₀ : F c₀ ≥ 2 := hge2
      have hle : F c₀ ≤ ∑ x : Fin d, F x :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c₀)
      have hexcess' : ∑ c : Fin d, F c = 1 := hexcess
      omega
    · intro c hc; by_contra hne1
      have hge1_card : (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card ≥ 2 := by
        have := hcard_ge c; omega
      have hge1 : (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1 ≥ 1 := by omega
      let F : Fin d → ℕ := fun c => (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1
      have hFc₀ : F c₀ ≥ 1 := by have := hc₀; show _ - 1 ≥ 1; omega
      have hFc : F c ≥ 1 := hge1
      have h₁ : F c₀ ≤ ∑ x : Fin d, F x :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c₀)
      have h₂ : F c ≤ ∑ x : Fin d, F x :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have hsum := Finset.sum_le_sum_of_subset (f := F)
          (Finset.subset_univ ({c₀, c} : Finset (Fin d)))
      rw [Finset.sum_pair hc.symm] at hsum
      have hexcess' : ∑ c : Fin d, F c = 1 := hexcess
      omega
  obtain ⟨k₁, k₂, hk₁, hk₂, hne12, hpair⟩ : ∃ k₁ k₂ : Fin (d + 1),
      f k₁ = c₀ ∧ f k₂ = c₀ ∧ k₁ ≠ k₂ ∧
      Finset.univ.filter (fun i : Fin (d + 1) => f i = c₀) = {k₁, k₂} := by
    rw [Finset.card_eq_two] at hc₀_eq
    obtain ⟨a, b, hab, habset⟩ := hc₀_eq
    have ha := (Finset.mem_filter.mp (habset ▸ Finset.mem_insert_self a {b})).2
    have hb := (Finset.mem_filter.mp (habset ▸ Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr rfl)))).2
    exact ⟨a, b, ha, hb, hab, habset⟩
  suffices hset : Finset.univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = j) = {k₁, k₂} by
    rw [hset, Finset.card_pair hne12]; exact even_two
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hk
    obtain ⟨i, hi_ne, hi_eq⟩ := hk (f k)
    have hfk : f k = c₀ := by
      by_contra hne
      have hmult1 := hc₀_rest (f k) hne
      rw [Finset.card_eq_one] at hmult1
      obtain ⟨a, ha⟩ := hmult1
      have hk_in : k ∈ Finset.univ.filter (fun i : Fin (d + 1) => f i = f k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
      have hi_in : i ∈ Finset.univ.filter (fun i : Fin (d + 1) => f i = f k) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_eq⟩
      rw [ha] at hk_in hi_in; simp at hk_in hi_in
      exact hi_ne (hk_in ▸ hi_in)
    have hk_mem : k ∈ Finset.univ.filter (fun i : Fin (d + 1) => f i = c₀) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfk⟩
    rw [hpair] at hk_mem; simp at hk_mem; exact hk_mem
  · intro hk j
    obtain ⟨i₀, hi₀⟩ := hcov j
    by_cases hik : i₀ = k
    · rcases hk with heq | heq
      · have hfk : f k = c₀ := heq ▸ hk₁
        have hj_c0 : j = c₀ := by rw [← hi₀, hik, hfk]
        exact ⟨k₂, (heq ▸ hne12).symm, by rw [hj_c0, hk₂]⟩
      · have hfk : f k = c₀ := heq ▸ hk₂
        have hj_c0 : j = c₀ := by rw [← hi₀, hik, hfk]
        exact ⟨k₁, heq ▸ hne12, by rw [hj_c0, hk₁]⟩
    · exact ⟨i₀, hik, hi₀⟩

/-- **Abstract door parity**: door count parity equals surjectivity. -/
theorem abstract_door_parity (d : ℕ) (f : Fin (d + 1) → Fin (d + 1)) :
    (Finset.univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card % 2 =
    if Function.Surjective f then 1 else 0 := by
  by_cases hsurj : Function.Surjective f
  · rw [if_pos hsurj]
    have hinj := Finite.injective_iff_surjective.mpr hsurj
    obtain ⟨k₀, hk₀⟩ := hsurj ⟨d, by omega⟩
    have huniq : ∀ k, f k = ⟨d, by omega⟩ → k = k₀ := fun k hk => hinj (hk.trans hk₀.symm)
    suffices hset : Finset.univ.filter (fun k : Fin (d + 1) =>
        ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = ⟨j.val, by omega⟩) = {k₀} by
      rw [hset, Finset.card_singleton]
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hk; by_contra hne
      have hfk_ne : f k ≠ ⟨d, by omega⟩ := fun h => hne (huniq k h)
      have hfk_val_ne : (f k).val ≠ d := fun h => hfk_ne (Fin.ext h)
      have hfk_lt : (f k).val < d := by have := (f k).isLt; omega
      obtain ⟨i, hi_ne, hi_eq⟩ := hk ⟨(f k).val, hfk_lt⟩
      have hval : (f i).val = (f k).val := by
        have h1 := congr_arg Fin.val hi_eq
        simp at h1
        exact h1
      exact hi_ne (hinj (Fin.ext hval))
    · intro hk; subst hk; intro ⟨j, hj⟩
      obtain ⟨i, hi⟩ := hsurj ⟨j, by omega⟩
      exact ⟨i, fun hik => by subst hik; rw [hk₀] at hi; exact absurd hi (by simp; omega),
             by rw [hi]⟩
  · rw [if_neg hsurj]
    by_cases hd_app : ∃ i, f i = ⟨d, by omega⟩
    · have ⟨j₀, hj₀⟩ : ∃ j : Fin d, ¬ ∃ i, f i = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
        by_contra hall; push_neg at hall; apply hsurj
        intro ⟨y, hy⟩; by_cases hyd : y = d
        · subst hyd; exact hd_app
        · exact hall ⟨y, by omega⟩
      suffices h0 : (Finset.univ.filter (fun k : Fin (d + 1) =>
          ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = ⟨j.val, by omega⟩)).card = 0 by
        rw [h0]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _; push_neg; exact ⟨j₀, fun i _ h => hj₀ ⟨i, h⟩⟩
    · push_neg at hd_app
      have hlt : ∀ i, (f i).val < d := by
        intro i; have := (f i).isLt
        by_contra h; push_neg at h
        have hlt2 := (f i).isLt
        have : (f i).val = d := by omega
        exact hd_app i (Fin.ext this)
      let g : Fin (d + 1) → Fin d := fun i => ⟨(f i).val, hlt i⟩
      by_cases hgsurj : Function.Surjective g
      · have heven := door_parity_all_small d g hgsurj
        suffices heq : Finset.univ.filter (fun k : Fin (d + 1) =>
            ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = ⟨j.val, by omega⟩) =
          Finset.univ.filter (fun k : Fin (d + 1) =>
            ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ g i = j) by
          rw [heq]; exact Nat.even_iff.mp heven
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> intro h j
        · obtain ⟨i, hi, hfi⟩ := h j
          exact ⟨i, hi, Fin.ext (by simp [g]; exact congr_arg Fin.val hfi)⟩
        · obtain ⟨i, hi, hgi⟩ := h j
          exact ⟨i, hi, Fin.ext (by have := congr_arg Fin.val hgi; simp [g] at this; exact this)⟩
      · have ⟨j₀, hj₀⟩ : ∃ j : Fin d, ¬ ∃ i, g i = j := by
          by_contra h; push_neg at h; exact hgsurj h
        suffices h0 : (Finset.univ.filter (fun k : Fin (d + 1) =>
            ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = ⟨j.val, by omega⟩)).card = 0 by
          rw [h0]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _; push_neg
        exact ⟨j₀, fun i _ h =>
          hj₀ ⟨i, Fin.ext (by have := congr_arg Fin.val h; simp at this; exact this)⟩⟩

-- ============================================================
-- SECTION VI: Interior Door Pairing
-- ============================================================

private def adjMap {V : Type*} [DecidableEq V] {d : ℕ} (K : CellComplex V d)
    (p : K.Simplex × Fin (d + 1)) : K.Simplex × Fin (d + 1) :=
  match K.adj p.1 p.2 with
  | some (s', k') => (s', k')
  | none => p

private lemma door_transfer_one_dir {V : Type*} [DecidableEq V] {d : ℕ}
    {c : V → Fin (d + 1)} {K : CellComplex V d}
    {s : K.Simplex} {k : Fin (d + 1)} {s' : K.Simplex} {k' : Fin (d + 1)}
    (hvert : (Finset.univ.erase k).image (K.vertices s) =
             (Finset.univ.erase k').image (K.vertices s'))
    (h : isDoorAt c K s k) : isDoorAt c K s' k' := by
  intro j
  obtain ⟨i, hi_ne, hi_eq⟩ := h j
  have hmem : K.vertices s i ∈ (Finset.univ.erase k').image (K.vertices s') := by
    rw [← hvert]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_erase.mpr ⟨hi_ne, Finset.mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := Finset.mem_image.mp hmem
  exact ⟨i', (Finset.mem_erase.mp hi'_mem).1, by rw [hi'_eq]; exact hi_eq⟩

private lemma door_transfer {V : Type*} [DecidableEq V] {d : ℕ}
    {c : V → Fin (d + 1)} {K : CellComplex V d}
    {s : K.Simplex} {k : Fin (d + 1)} {s' : K.Simplex} {k' : Fin (d + 1)}
    (hadj : K.adj s k = some (s', k')) :
    isDoorAt c K s k ↔ isDoorAt c K s' k' :=
  ⟨door_transfer_one_dir (K.adj_vertices s k s' k' hadj),
   door_transfer_one_dir (K.adj_vertices s k s' k' hadj).symm⟩

/-- Interior doors pair up via adjacency involution. -/
theorem interior_doors_even (c : V → Fin (d + 1)) (K : CellComplex V d) :
    Even (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 ≠ none)).card := by
  set S := Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
    isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 ≠ none)
  apply even_card_fpf_invol S (adjMap K)
  · intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back := K.adj_symm p.1 p.2 s' k' hadj_eq
      show adjMap K (adjMap K p) = p
      simp only [adjMap, hadj_eq, hadj_back]
  · intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back := K.adj_symm p.1 p.2 s' k' hadj_eq
      show isDoorAt c K (adjMap K p).1 (adjMap K p).2 ∧
           K.adj (adjMap K p).1 (adjMap K p).2 ≠ none
      simp only [adjMap, hadj_eq]
      exact ⟨(door_transfer hadj_eq).mp hdoor, by rw [hadj_back]; exact Option.noConfusion⟩
  · intro p hp
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      show adjMap K p ≠ p
      simp only [adjMap, hadj_eq]
      intro heq
      exact K.adj_ne p.1 p.2 s' k' hadj_eq (congr_arg Prod.fst heq).symm

-- ============================================================
-- SECTION VII: Parity Theorem
-- ============================================================

private lemma per_simplex_door_parity (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Simplex) :
    (Finset.univ.filter (fun k : Fin (d + 1) => isDoorAt c K s k)).card % 2 =
    if IsFC c K s then 1 else 0 := by
  have h := abstract_door_parity d (c ∘ K.vertices s)
  have h1 : (Finset.univ.filter (fun k : Fin (d + 1) => isDoorAt c K s k)) =
      (Finset.univ.filter (fun k : Fin (d + 1) =>
        ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ (c ∘ K.vertices s) i = ⟨j.val, by omega⟩)) := by
    ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rfl
  rw [h1]
  have h2 : IsFC c K s ↔ Function.Surjective (c ∘ K.vertices s) := Iff.rfl
  simp only [h2]
  convert h using 2

private lemma sum_mod_congr {ι : Type*} (S : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ S, a i % 2 = b i % 2) :
    (∑ i ∈ S, a i) % 2 = (∑ i ∈ S, b i) % 2 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih =>
    rw [Finset.sum_cons, Finset.sum_cons]
    have hx_eq := h x (Finset.mem_cons_self x s)
    have hs_eq := ih (fun i hi => h i (Finset.mem_cons.mpr (Or.inr hi)))
    omega

private lemma card_doors_eq_sum (c : V → Fin (d + 1)) (K : CellComplex V d) :
    (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2)).card =
    ∑ s : K.Simplex, (Finset.univ.filter (fun k : Fin (d + 1) =>
      isDoorAt c K s k)).card := by
  have hlhs : (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2)).card =
    ∑ p : K.Simplex × Fin (d + 1), if isDoorAt c K p.1 p.2 then 1 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have hrhs : ∀ s : K.Simplex, (Finset.univ.filter (fun k : Fin (d + 1) =>
      isDoorAt c K s k)).card =
    ∑ k : Fin (d + 1), if isDoorAt c K s k then 1 else 0 := by
    intro s
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  rw [hlhs, Finset.sum_congr rfl (fun s _ => hrhs s)]
  rw [← Fintype.sum_prod_type']

private lemma doors_partition (c : V → Fin (d + 1)) (K : CellComplex V d) :
    (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2)).card =
    (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 ≠ none)).card +
    (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none)).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · intro h; by_cases hadj : K.adj p.1 p.2 = none
      · right; exact ⟨h, hadj⟩
      · left; exact ⟨h, hadj⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · rw [Finset.disjoint_left]
    intro p h₁ h₂
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact h₁.2 h₂.2

/-- **Sperner Parity Theorem**: FC count ≡ boundary doors (mod 2). -/
theorem sperner_parity (c : V → Fin (d + 1)) (K : CellComplex V d) :
    (Finset.univ.filter (fun s : K.Simplex => IsFC c K s)).card % 2 =
    (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none)).card % 2 := by
  have hper := per_simplex_door_parity c K
  have hsum : (∑ s : K.Simplex, (Finset.univ.filter (fun k => isDoorAt c K s k)).card) % 2 =
      (∑ s : K.Simplex, if IsFC c K s then 1 else 0) % 2 :=
    sum_mod_congr Finset.univ _ _ (fun s _ => by
      rw [hper s]; split <;> simp)
  have hfc_sum : (∑ s : K.Simplex, if IsFC c K s then (1 : ℕ) else 0) =
      (Finset.univ.filter (fun s => IsFC c K s)).card := by
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul, mul_one]
  have hdoor_sum := card_doors_eq_sum c K
  have hpart := doors_partition c K
  have heven := interior_doors_even c K
  obtain ⟨m, hm⟩ := heven
  calc (Finset.univ.filter (fun s => IsFC c K s)).card % 2
      = (∑ s : K.Simplex, if IsFC c K s then 1 else 0) % 2 := by rw [hfc_sum]
    _ = (∑ s : K.Simplex, (Finset.univ.filter (fun k => isDoorAt c K s k)).card) % 2 := hsum.symm
    _ = (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
          isDoorAt c K p.1 p.2)).card % 2 := by rw [hdoor_sum]
    _ = ((Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
          isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 ≠ none)).card +
         (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
          isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none)).card) % 2 := by rw [hpart]
    _ = (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
          isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none)).card % 2 := by
        rw [hm, Nat.add_mod, show (m + m) % 2 = 0 from by omega,
            Nat.zero_add, Nat.mod_mod_of_dvd]; exact ⟨1, rfl⟩

-- ============================================================
-- SECTION VIII: Main Theorem
-- ============================================================

/-- **Sperner's Lemma**: If boundary doors are odd, a fully-colored cell exists. -/
theorem sperner (c : V → Fin (d + 1)) (K : CellComplex V d)
    (hbdry : Odd (Finset.univ.filter (fun p : K.Simplex × Fin (d + 1) =>
      isDoorAt c K p.1 p.2 ∧ K.adj p.1 p.2 = none)).card) :
    ∃ s : K.Simplex, IsFC c K s := by
  have hparity := sperner_parity c K
  have hodd : Odd (Finset.univ.filter (fun s : K.Simplex => IsFC c K s)).card := by
    rwa [Nat.odd_iff, hparity, ← Nat.odd_iff]
  have hpos : 0 < (Finset.univ.filter (fun s => IsFC c K s)).card := by
    obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, (Finset.mem_filter.mp hs).2⟩

end SpernerAbstract
