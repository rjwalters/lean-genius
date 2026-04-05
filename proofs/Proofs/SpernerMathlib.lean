/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# Sperner's Lemma via Door Counting

We prove Sperner's lemma for finite cell families equipped with
adjacency satisfying local face-sharing axioms, using a
door-counting parity argument.

The adjacency interface: each cell has `d+1` faces indexed by
`Fin (d+1)`. For each face, `adj s k` returns either `some (s', k')`
(the unique adjacent cell sharing that face) or `none` (boundary).

The proof proceeds by:
1. Showing interior doors pair via the adjacency involution (even count).
2. A per-cell parity argument: the number of door positions of a
   coloring `f : Fin (d+1) → Fin (d+1)` is odd iff `f` is surjective.
3. Summing to conclude: panchromatic cell count ≡ boundary door
   count (mod 2).

## Main results

* `Sperner.even_card_fpf_invol`: fixed-point-free involution on a
  finset yields even cardinality. Useful beyond Sperner (Tucker's
  lemma, Borsuk-Ulam, etc.).
* `Sperner.door_count_parity`: door count parity equals the
  surjectivity indicator.
* `Sperner.sperner_parity`: panchromatic count ≡ boundary door
  count (mod 2).
* `Sperner.exists_panchromatic`: if boundary doors are odd, a
  panchromatic cell exists.
* `Sperner.boundary_doors_on_last_face`: with a Sperner coloring,
  every boundary door lies on the last face.

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]
-/

namespace Sperner

open Finset

/-!
## Fixed-point-free involution parity

A fixed-point-free involution on a finset has even cardinality. -/

/-- A fixed-point-free involution on a finset has even cardinality:
every element pairs with its distinct image. -/
theorem even_card_fpf_invol {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α)
    (hInv : ∀ x ∈ S, f (f x) = x)
    (hMem : ∀ x ∈ S, f x ∈ S)
    (hNe : ∀ x ∈ S, f x ≠ x) :
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
        have h1 : (S.erase y).card = S.card - 1 :=
          Finset.card_erase_of_mem hy
        have h2 : x ∈ S.erase y :=
          Finset.mem_erase.mpr ⟨hxy, hx⟩
        have h3 : S'.card = (S.erase y).card - 1 :=
          Finset.card_erase_of_mem h2
        have hcard2 : (S.erase y).card ≥ 1 :=
          Finset.one_le_card.mpr ⟨x, h2⟩
        omega
      rw [hcard]
      have hf_S' : ∀ a ∈ S', f a ∈ S' := by
        intro a ha
        simp only [S', Finset.mem_erase] at ha ⊢
        refine ⟨?_, ?_, hMem a ha.2.2⟩
        · intro h
          have hinv_a := hInv a ha.2.2
          rw [h] at hinv_a; exact ha.2.1 (hy_def.symm ▸ hinv_a).symm
        · intro h
          have hinv_a := hInv a ha.2.2
          rw [h, show f y = x from by rw [hy_def]; exact hInv x hx] at hinv_a
          exact ha.1 hinv_a.symm
      exact (ih S' hS'_sub
        (fun a ha => hInv a (hS'_sub.subset ha))
        hf_S'
        (fun a ha => hNe a (hS'_sub.subset ha))).add ⟨1, rfl⟩

/-!
## Door count parity

The number of door positions of a coloring `f : Fin (d+1) → Fin (d+1)`
has parity equal to the surjectivity indicator of `f`. -/

section DoorCountParity

/-- If a lower color has no preimage, no position is a door. -/
private lemma door_filter_empty_of_missing_color (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1))
    (j₀ : Fin d)
    (hmiss : ¬∃ i : Fin (d + 1), f i = ⟨j₀.val, by omega⟩) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)) = ∅ := by
  rw [filter_eq_empty_iff]
  intro k _; push_neg
  exact ⟨j₀, fun i _ h => hmiss ⟨i, h⟩⟩

/-- If naturals indexed by a finset sum to 1, exactly one equals 1. -/
private lemma exists_of_sum_eq_one {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {f : ι → ℕ}
    (hsum : ∑ i ∈ s, f i = 1) :
    ∃ a ∈ s, f a = 1 ∧ ∀ b ∈ s, b ≠ a → f b = 0 := by
  have ⟨a, ha, hfa⟩ : ∃ a ∈ s, 0 < f a := by
    by_contra h; push_neg at h
    have := Finset.sum_eq_zero (fun i hi => Nat.eq_zero_of_le_zero (h i hi))
    omega
  have hle : f a ≤ 1 :=
    hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha
  have hfa_eq : f a = 1 := le_antisymm hle hfa
  have hrest : ∑ x ∈ s.erase a, f x = 0 := by
    have := Finset.add_sum_erase s f ha; linarith
  exact ⟨a, ha, hfa_eq, fun b hb hne =>
    Nat.eq_zero_of_le_zero
      ((Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_erase.mpr ⟨hne, hb⟩)).trans hrest.le)⟩

/-- Pigeonhole: a surjection `Fin (d+1) → Fin d` has exactly one
fiber of size 2 and all others of size 1. -/
private lemma surjection_unique_dup_fiber (d : ℕ)
    (f : Fin (d + 1) → Fin d)
    (hcov : ∀ j : Fin d, ∃ i, f i = j) :
    ∃ c₀ : Fin d,
      (univ.filter (fun i : Fin (d + 1) => f i = c₀)).card = 2 ∧
      ∀ c ≠ c₀,
        (univ.filter (fun i : Fin (d + 1) => f i = c)).card = 1 := by
  have hcard_ge : ∀ c : Fin d,
      (univ.filter (fun i : Fin (d + 1) => f i = c)).card ≥ 1 := by
    intro c; obtain ⟨i, hi⟩ := hcov c
    exact Finset.card_pos.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have htotal : ∑ c : Fin d,
      (univ.filter (fun i : Fin (d + 1) => f i = c)).card = d + 1 := by
    rw [← Finset.card_biUnion (by
      intro x _ y _ hxy
      apply Finset.disjoint_filter.mpr
      intro i _ h1 h2; exact hxy (h1.symm.trans h2))]
    have hbU : Finset.biUnion univ (fun c : Fin d =>
        univ.filter (fun i : Fin (d + 1) => f i = c)) = univ := by
      ext i; constructor
      · intro _; exact mem_univ _
      · intro _; rw [mem_biUnion]
        exact ⟨f i, mem_univ _, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    rw [hbU, card_univ, Fintype.card_fin]
  have hexcess : ∑ c : Fin d,
      ((univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1) = 1 := by
    have hadd : ∀ c : Fin d,
        (univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1 + 1 =
        (univ.filter (fun i : Fin (d + 1) => f i = c)).card := by
      intro c; have := hcard_ge c; omega
    have := Finset.sum_congr (show (univ : Finset (Fin d)) = univ from rfl)
      (fun c _ => hadd c)
    simp only [Finset.sum_add_distrib, Finset.sum_const, card_univ,
      Fintype.card_fin, htotal, smul_eq_mul] at this
    omega
  obtain ⟨c₀, _, hc₀_eq, hc₀_rest⟩ := exists_of_sum_eq_one hexcess
  exact ⟨c₀, by have := hcard_ge c₀; omega,
    fun c hc => by have := hc₀_rest c (mem_univ _) hc; have := hcard_ge c; omega⟩

/-- When `f : Fin (d+1) → Fin d` is surjective, the door count is
even (doors pair via the duplicated fiber). -/
private lemma even_card_doors_of_surjective (d : ℕ)
    (f : Fin (d + 1) → Fin d)
    (hcov : ∀ j : Fin d, ∃ i, f i = j) :
    Even (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = j)).card := by
  obtain ⟨c₀, hc₀_eq, hc₀_rest⟩ := surjection_unique_dup_fiber d f hcov
  obtain ⟨k₁, k₂, hk₁, hk₂, hne12, hpair⟩ :
      ∃ k₁ k₂ : Fin (d + 1),
        f k₁ = c₀ ∧ f k₂ = c₀ ∧ k₁ ≠ k₂ ∧
        univ.filter (fun i : Fin (d + 1) => f i = c₀) = {k₁, k₂} := by
    rw [Finset.card_eq_two] at hc₀_eq
    obtain ⟨a, b, hab, habset⟩ := hc₀_eq
    have ha := (mem_filter.mp (habset ▸ mem_insert_self a {b})).2
    have hb := (mem_filter.mp
      (habset ▸ mem_insert.mpr (Or.inr (mem_singleton.mpr rfl)))).2
    exact ⟨a, b, ha, hb, hab, habset⟩
  suffices hset : univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = j) = {k₁, k₂} by
    rw [hset, card_pair hne12]; exact even_two
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · intro hk
    obtain ⟨i, hi_ne, hi_eq⟩ := hk (f k)
    have hfk : f k = c₀ := by
      by_contra hne
      have hmult1 := hc₀_rest (f k) hne
      rw [Finset.card_eq_one] at hmult1
      obtain ⟨a, ha⟩ := hmult1
      have hk_in : k ∈ univ.filter (fun i : Fin (d + 1) => f i = f k) :=
        mem_filter.mpr ⟨mem_univ _, rfl⟩
      have hi_in : i ∈ univ.filter (fun i : Fin (d + 1) => f i = f k) :=
        mem_filter.mpr ⟨mem_univ i, hi_eq⟩
      rw [ha] at hk_in hi_in; simp at hk_in hi_in
      exact hi_ne (hk_in ▸ hi_in)
    have hk_mem : k ∈ univ.filter (fun i : Fin (d + 1) => f i = c₀) :=
      mem_filter.mpr ⟨mem_univ k, hfk⟩
    rw [hpair] at hk_mem; simp at hk_mem; exact hk_mem
  · intro hk j
    obtain ⟨i₀, hi₀⟩ := hcov j
    by_cases hik : i₀ = k
    · rcases hk with heq | heq <;> subst heq
      · have hj_c0 : j = c₀ := by rw [← hi₀, hik, hk₁]
        exact ⟨k₂, hne12.symm, by rw [hj_c0, hk₂]⟩
      · have hj_c0 : j = c₀ := by rw [← hi₀, hik, hk₂]
        exact ⟨k₁, hne12, by rw [hj_c0, hk₁]⟩
    · exact ⟨i₀, hik, hi₀⟩

/-- A bijection has exactly one door position: the preimage of the
top color. -/
private lemma door_count_of_surj (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1))
    (hsurj : Function.Surjective f) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card = 1 := by
  have hinj := Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨k₀, hk₀⟩ := hsurj ⟨d, by omega⟩
  have huniq : ∀ k, f k = ⟨d, by omega⟩ → k = k₀ :=
    fun k hk => hinj (hk.trans hk₀.symm)
  suffices hset : univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩) = {k₀} by
    rw [hset, card_singleton]
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · intro hk; by_contra hne
    have hfk_ne : f k ≠ ⟨d, by omega⟩ := fun h => hne (huniq k h)
    have hfk_val_ne : (f k).val ≠ d := fun h => hfk_ne (Fin.ext h)
    have hfk_lt : (f k).val < d := by have := (f k).isLt; omega
    obtain ⟨i, hi_ne, hi_eq⟩ := hk ⟨(f k).val, hfk_lt⟩
    have hval : (f i).val = (f k).val := by
      have h1 := congr_arg Fin.val hi_eq; simp at h1; exact h1
    exact hi_ne (hinj (Fin.ext hval))
  · intro hk; subst hk; intro ⟨j, hj⟩
    obtain ⟨i, hi⟩ := hsurj ⟨j, by omega⟩
    exact ⟨i,
      fun hik => by subst hik; rw [hk₀] at hi; exact absurd hi (by simp; omega),
      by rw [hi]⟩

/-- A non-surjection has an even number of door positions. -/
private lemma door_count_even_of_not_surj (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1))
    (hnsurj : ¬Function.Surjective f) :
    Even (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card := by
  by_cases hd_app : ∃ i, f i = ⟨d, by omega⟩
  · have ⟨j₀, hj₀⟩ : ∃ j : Fin d,
        ¬∃ i, f i = ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
      by_contra hall; push_neg at hall; apply hnsurj
      intro ⟨y, hy⟩; by_cases hyd : y = d
      · subst hyd; exact hd_app
      · exact hall ⟨y, by omega⟩
    rw [Finset.card_eq_zero.mpr (door_filter_empty_of_missing_color d f j₀ hj₀)]
    exact ⟨0, rfl⟩
  · push_neg at hd_app
    have hlt : ∀ i, (f i).val < d := by
      intro i; have := (f i).isLt
      by_contra h; push_neg at h
      have : (f i).val = d := by omega
      exact hd_app i (Fin.ext this)
    let g : Fin (d + 1) → Fin d := fun i => ⟨(f i).val, hlt i⟩
    by_cases hgsurj : Function.Surjective g
    · have heven := even_card_doors_of_surjective d g hgsurj
      suffices heq : univ.filter (fun k : Fin (d + 1) =>
          ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
            f i = ⟨j.val, by omega⟩) =
        univ.filter (fun k : Fin (d + 1) =>
          ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ g i = j) by
        rw [heq]; exact heven
      ext k; simp only [mem_filter, mem_univ, true_and]
      constructor <;> intro h j
      · obtain ⟨i, hi, hfi⟩ := h j
        exact ⟨i, hi, Fin.ext (by simp [g]; exact congr_arg Fin.val hfi)⟩
      · obtain ⟨i, hi, hgi⟩ := h j
        exact ⟨i, hi, Fin.ext (by have := congr_arg Fin.val hgi; simp [g] at this; exact this)⟩
    · have ⟨j₀, hj₀⟩ : ∃ j : Fin d, ¬∃ i, g i = j := by
        by_contra h; push_neg at h; exact hgsurj h
      suffices h0 : (univ.filter (fun k : Fin (d + 1) =>
          ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
            f i = ⟨j.val, by omega⟩)).card = 0 by
        rw [h0]; exact ⟨0, rfl⟩
      rw [Finset.card_eq_zero, filter_eq_empty_iff]
      intro k _; push_neg
      exact ⟨j₀, fun i _ h =>
        hj₀ ⟨i, Fin.ext (by have := congr_arg Fin.val h; simp at this; exact this)⟩⟩

/-- **Door count parity**: the number of door positions of a coloring
`f : Fin (d+1) → Fin (d+1)` is odd iff `f` is surjective. -/
theorem door_count_parity (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1)) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card % 2 =
    if Function.Surjective f then 1 else 0 := by
  by_cases hsurj : Function.Surjective f
  · rw [if_pos hsurj, door_count_of_surj d f hsurj]
  · rw [if_neg hsurj]
    exact Nat.even_iff.mp (door_count_even_of_not_surj d f hsurj)

end DoorCountParity

/-!
## Door counting for abstract cell complexes

We work with an abstract cell type `Cell` equipped with a vertex map
and adjacency, using hypotheses rather than a structure. -/

section DoorCounting

variable {V : Type*} [DecidableEq V] {d : ℕ}
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]

/-- A cell is *panchromatic*: the coloring restricted to its vertices
is surjective onto `Fin (d+1)`. -/
def IsPanchromatic (vertex : Cell → Fin (d + 1) → V)
    (c : V → Fin (d + 1)) (s : Cell) : Prop :=
  Function.Surjective (c ∘ vertex s)

/-- A facet `(s, k)` is a *door* (standard terminology in Sperner
arguments): removing vertex `k`, the remaining `d` vertices carry
all lower colors `{0, ..., d-1}`. -/
def IsDoor (vertex : Cell → Fin (d + 1) → V)
    (c : V → Fin (d + 1)) (s : Cell) (k : Fin (d + 1)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ c (vertex s i) = Fin.castSucc j

instance decidableIsPanchromatic (vertex : Cell → Fin (d + 1) → V)
    (c : V → Fin (d + 1)) (s : Cell) :
    Decidable (IsPanchromatic vertex c s) := by
  unfold IsPanchromatic Function.Surjective; exact inferInstance

instance decidableIsDoor (vertex : Cell → Fin (d + 1) → V)
    (c : V → Fin (d + 1)) (s : Cell) (k : Fin (d + 1)) :
    Decidable (IsDoor vertex c s k) := by
  unfold IsDoor; exact inferInstance

/-- Extend adjacency to a total involution by fixing boundary faces:
sends `(s, k)` to its adjacent cell-face pair if interior, or to
itself if on the boundary. -/
private def adjMap
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (p : Cell × Fin (d + 1)) : Cell × Fin (d + 1) :=
  match adj p.1 p.2 with
  | some (s', k') => (s', k')
  | none => p

omit [DecidableEq Cell] [Fintype Cell] in
/-- A door transfers through a shared face. -/
lemma isDoor_of_shared_face
    (vertex : Cell → Fin (d + 1) → V)
    {c : V → Fin (d + 1)} {s : Cell} {k : Fin (d + 1)}
    {s' : Cell} {k' : Fin (d + 1)}
    (hvert : (univ.erase k).image (vertex s) =
      (univ.erase k').image (vertex s'))
    (h : IsDoor vertex c s k) : IsDoor vertex c s' k' := by
  intro j
  obtain ⟨i, hi_ne, hi_eq⟩ := h j
  have hmem : vertex s i ∈ (univ.erase k').image (vertex s') := by
    rw [← hvert]
    exact mem_image.mpr ⟨i, mem_erase.mpr ⟨hi_ne, mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := mem_image.mp hmem
  exact ⟨i', (mem_erase.mp hi'_mem).1, by rw [hi'_eq]; exact hi_eq⟩

omit [DecidableEq Cell] [Fintype Cell] in
/-- A door transfers through adjacency (iff version). -/
lemma isDoor_iff_of_adj
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some (s', k') →
      (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s'))
    {c : V → Fin (d + 1)} {s : Cell} {k : Fin (d + 1)}
    {s' : Cell} {k' : Fin (d + 1)}
    (hadj_eq : adj s k = some (s', k')) :
    IsDoor vertex c s k ↔ IsDoor vertex c s' k' :=
  ⟨isDoor_of_shared_face vertex (hadj_vertex s k s' k' hadj_eq),
   isDoor_of_shared_face vertex (hadj_vertex s k s' k' hadj_eq).symm⟩

/-- Interior doors pair up via the adjacency involution,
so their count is even. -/
theorem even_card_interior_doors
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_symm : ∀ s k s' k',
      adj s k = some (s', k') → adj s' k' = some (s, k))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some (s', k') →
      (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s'))
    (hadj_ne : ∀ s k s' k',
      adj s k = some (s', k') → s ≠ s')
    (c : V → Fin (d + 1)) :
    Even (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card := by
  set S := univ.filter
    (fun p : Cell × Fin (d + 1) =>
      IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 ≠ none)
  apply even_card_fpf_invol S (adjMap adj)
  · intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    cases hadj_eq : adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne'
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
      show adjMap adj (adjMap adj p) = p
      simp only [adjMap, hadj_eq, hadj_back]
  · intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne'⟩ := hp
    cases hadj_eq : adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne'
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back := hadj_symm p.1 p.2 s' k' hadj_eq
      show IsDoor vertex c (adjMap adj p).1 (adjMap adj p).2 ∧
        adj (adjMap adj p).1 (adjMap adj p).2 ≠ none
      simp only [adjMap, hadj_eq]
      exact ⟨(isDoor_iff_of_adj vertex adj hadj_vertex hadj_eq).mp hdoor,
        by rw [hadj_back]; exact Option.noConfusion⟩
  · intro p hp
    simp only [S, mem_filter, mem_univ, true_and] at hp
    obtain ⟨_, hadj_ne'⟩ := hp
    cases hadj_eq : adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne'
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      show adjMap adj p ≠ p
      simp only [adjMap, hadj_eq]
      intro heq
      exact hadj_ne p.1 p.2 s' k' hadj_eq (congr_arg Prod.fst heq).symm

omit [DecidableEq V] [DecidableEq Cell] [Fintype Cell] in
/-- Per-cell door parity: the door count of a single cell has the same
parity as its panchromaticity indicator. -/
lemma per_cell_door_parity
    (vertex : Cell → Fin (d + 1) → V)
    (c : V → Fin (d + 1)) (s : Cell) :
    (univ.filter (fun k : Fin (d + 1) =>
      IsDoor vertex c s k)).card % 2 =
    if IsPanchromatic vertex c s then 1 else 0 := by
  have h := door_count_parity d (c ∘ vertex s)
  have h1 : (univ.filter (fun k : Fin (d + 1) =>
      IsDoor vertex c s k)) =
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        (c ∘ vertex s) i = ⟨j.val, by omega⟩)) := by
    ext k; simp only [mem_filter, mem_univ, true_and]; rfl
  rw [h1]
  have h2 : IsPanchromatic vertex c s ↔
      Function.Surjective (c ∘ vertex s) := Iff.rfl
  simp only [h2]; convert h using 2

private lemma sum_mod_congr {ι : Type*}
    (S : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ S, a i % 2 = b i % 2) :
    (∑ i ∈ S, a i) % 2 = (∑ i ∈ S, b i) % 2 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih =>
    rw [sum_cons, sum_cons]
    have hx_eq := h x (mem_cons_self x s)
    have hs_eq := ih (fun i hi => h i (mem_cons.mpr (Or.inr hi)))
    omega

omit [DecidableEq V] [DecidableEq Cell] in
lemma card_doors_eq_sum
    (vertex : Cell → Fin (d + 1) → V)
    (c : V → Fin (d + 1)) :
    (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2)).card =
    ∑ s : Cell, (univ.filter
      (fun k : Fin (d + 1) => IsDoor vertex c s k)).card := by
  have hlhs : (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2)).card =
    ∑ p : Cell × Fin (d + 1),
      if IsDoor vertex c p.1 p.2 then 1 else 0 := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  have hrhs : ∀ s : Cell,
      (univ.filter (fun k : Fin (d + 1) =>
        IsDoor vertex c s k)).card =
      ∑ k : Fin (d + 1),
        if IsDoor vertex c s k then 1 else 0 := by
    intro s
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  rw [hlhs, sum_congr rfl (fun s _ => hrhs s), ← Fintype.sum_prod_type']

omit [DecidableEq V] in
lemma doors_partition
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (c : V → Fin (d + 1)) :
    (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2)).card =
    (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card +
    (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext p
    simp only [mem_filter, mem_univ, true_and, mem_union]
    constructor
    · intro h
      by_cases hadj_eq : adj p.1 p.2 = none
      · right; exact ⟨h, hadj_eq⟩
      · left; exact ⟨h, hadj_eq⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · rw [disjoint_left]
    intro p h₁ h₂
    simp only [mem_filter, mem_univ, true_and] at h₁ h₂
    exact h₁.2 h₂.2

/-- **Sperner Parity Theorem**: the panchromatic cell count is
congruent mod 2 to the boundary door count. -/
theorem sperner_parity
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_symm : ∀ s k s' k',
      adj s k = some (s', k') → adj s' k' = some (s, k))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some (s', k') →
      (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s'))
    (hadj_ne : ∀ s k s' k',
      adj s k = some (s', k') → s ≠ s')
    (c : V → Fin (d + 1)) :
    (univ.filter (fun s : Cell =>
      IsPanchromatic vertex c s)).card % 2 =
    (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)).card % 2 := by
  have hper := per_cell_door_parity vertex c
  have hsum :
      (∑ s : Cell, (univ.filter
        (fun k => IsDoor vertex c s k)).card) % 2 =
      (∑ s : Cell, if IsPanchromatic vertex c s then 1 else 0) % 2 :=
    sum_mod_congr univ _ _ (fun s _ => by rw [hper s]; split <;> simp)
  have hfc_sum :
      (∑ s : Cell,
        if IsPanchromatic vertex c s then (1 : ℕ) else 0) =
      (univ.filter (fun s => IsPanchromatic vertex c s)).card := by
    rw [sum_ite, sum_const_zero, add_zero, sum_const, smul_eq_mul, mul_one]
  have hdoor_sum := card_doors_eq_sum vertex c
  have hpart := doors_partition vertex adj c
  have heven := even_card_interior_doors vertex adj hadj_symm hadj_vertex hadj_ne c
  obtain ⟨m, hm⟩ := heven
  calc (univ.filter (fun s => IsPanchromatic vertex c s)).card % 2
    _ = (∑ s : Cell,
        if IsPanchromatic vertex c s then 1 else 0) % 2 := by rw [hfc_sum]
    _ = (∑ s : Cell, (univ.filter
        (fun k => IsDoor vertex c s k)).card) % 2 := hsum.symm
    _ = (univ.filter
        (fun p : Cell × Fin (d + 1) =>
          IsDoor vertex c p.1 p.2)).card % 2 := by rw [hdoor_sum]
    _ = ((univ.filter
        (fun p : Cell × Fin (d + 1) =>
          IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card +
       (univ.filter
        (fun p : Cell × Fin (d + 1) =>
          IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)).card) % 2 := by
      rw [hpart]
    _ = (univ.filter
        (fun p : Cell × Fin (d + 1) =>
          IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)).card % 2 := by
      rw [hm, Nat.add_mod, show (m + m) % 2 = 0 from by simp [← Nat.two_mul, Nat.mul_mod_right],
        Nat.zero_add, Nat.mod_mod_of_dvd]
      exact ⟨1, rfl⟩

/-- **Sperner's Lemma**: if boundary doors are odd, a panchromatic
cell exists. -/
theorem exists_panchromatic
    (vertex : Cell → Fin (d + 1) → V)
    (adj : Cell → Fin (d + 1) → Option (Cell × Fin (d + 1)))
    (hadj_symm : ∀ s k s' k',
      adj s k = some (s', k') → adj s' k' = some (s, k))
    (hadj_vertex : ∀ s k s' k',
      adj s k = some (s', k') →
      (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s'))
    (hadj_ne : ∀ s k s' k',
      adj s k = some (s', k') → s ≠ s')
    (c : V → Fin (d + 1))
    (hbdry : Odd (univ.filter
      (fun p : Cell × Fin (d + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)).card) :
    ∃ s : Cell, IsPanchromatic vertex c s := by
  have hparity := sperner_parity vertex adj hadj_symm hadj_vertex hadj_ne c
  have hodd : Odd (univ.filter
      (fun s : Cell => IsPanchromatic vertex c s)).card := by
    rwa [Nat.odd_iff, hparity, ← Nat.odd_iff]
  have hpos : 0 < (univ.filter
      (fun s => IsPanchromatic vertex c s)).card :=
    hodd.pos
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, (mem_filter.mp hs).2⟩

end DoorCounting

/-!
## Boundary reduction

With a Sperner coloring, every boundary door lies on the last face.
This eliminates the need to sum over all faces. -/

section BoundaryReduction

variable {V : Type*} [DecidableEq V] {n : ℕ}
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]

/-- A Sperner coloring: if vertex `v` is on face `k`, then `c v` is
not `k`. -/
def IsSpernerColoring
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop) : Prop :=
  ∀ v k, onFace v k → c v ≠ k

omit [DecidableEq V] [DecidableEq Cell] [Fintype Cell] in
/-- **Boundary doors on the last face**: given a Sperner coloring, every
boundary door must lie on face `n` (the last face). Any door on a lower
face `faceIdx < n` leads to a contradiction between the door condition
(which requires color `faceIdx` on some non-omitted vertex) and the
Sperner condition (which forbids color `faceIdx` on vertices of face
`faceIdx`). -/
theorem boundary_doors_on_last_face
    (vertex : Cell → Fin (n + 1) → V)
    (adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1)))
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (hSperner : IsSpernerColoring c onFace)
    (hBoundaryOnFace : ∀ s k, adj s k = none →
      ∃ faceIdx : Fin (n + 1), ∀ j : Fin (n + 1),
        j ≠ k → onFace (vertex s j) faceIdx)
    {s : Cell} {k : Fin (n + 1)}
    (hDoor : IsDoor vertex c s k)
    (hAdj : adj s k = none) :
    ∀ j : Fin (n + 1), j ≠ k →
      onFace (vertex s j) ⟨n, by omega⟩ := by
  obtain ⟨faceIdx, hOnFace⟩ := hBoundaryOnFace s k hAdj
  by_cases hlt : faceIdx.val < n
  · exfalso
    have hDoor' := hDoor ⟨faceIdx.val, hlt⟩
    obtain ⟨i, hi_ne, hi_color⟩ := hDoor'
    have hOnFace_i := hOnFace i hi_ne
    have hSperner_i := hSperner (vertex s i) faceIdx hOnFace_i
    have hcast : (⟨faceIdx.val, hlt⟩ : Fin n).castSucc = faceIdx :=
      Fin.ext (by simp [Fin.castSucc])
    rw [hcast] at hi_color
    exact hSperner_i hi_color
  · have hval : faceIdx.val = n := by have := faceIdx.isLt; omega
    have heq : faceIdx = ⟨n, by omega⟩ := Fin.ext hval
    rw [heq] at hOnFace
    exact hOnFace

omit [DecidableEq V] in
/-- **Boundary door parity for Sperner colorings**: given that all
boundary doors lie on the last face, the boundary door set equals
the last-face door set, so its parity is determined by the last
face alone. -/
theorem boundary_doors_odd_of_last_face
    (vertex : Cell → Fin (n + 1) → V)
    (adj : Cell → Fin (n + 1) → Option (Cell × Fin (n + 1)))
    (c : V → Fin (n + 1))
    (onFace : V → Fin (n + 1) → Prop)
    [∀ v k, Decidable (onFace v k)]
    (hSperner : IsSpernerColoring c onFace)
    (hBoundaryOnFace : ∀ s k, adj s k = none →
      ∃ faceIdx : Fin (n + 1), ∀ j : Fin (n + 1),
        j ≠ k → onFace (vertex s j) faceIdx)
    (hLastFace : Odd (univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧
        adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (vertex p.1 j) ⟨n, by omega⟩))).card) :
    Odd (univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none)).card := by
  suffices h : univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none) =
    univ.filter
      (fun p : Cell × Fin (n + 1) =>
        IsDoor vertex c p.1 p.2 ∧ adj p.1 p.2 = none ∧
        (∀ j : Fin (n + 1), j ≠ p.2 →
          onFace (vertex p.1 j) ⟨n, by omega⟩)) by
    rw [h]; exact hLastFace
  ext ⟨s, k⟩
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro ⟨hDoor, hAdj⟩
    exact ⟨hDoor, hAdj,
      boundary_doors_on_last_face vertex adj c onFace hSperner
        hBoundaryOnFace hDoor hAdj⟩
  · intro ⟨hDoor, hAdj, _⟩
    exact ⟨hDoor, hAdj⟩

end BoundaryReduction

end Sperner
