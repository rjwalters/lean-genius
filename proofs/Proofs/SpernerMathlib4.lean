/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# Abstract Sperner's Lemma

We prove Sperner's lemma for an abstract cell complex satisfying
adjacency axioms, via the door-counting parity argument.

## Main definitions

* `CellComplex`: An abstract cell complex with adjacency.
* `CellComplex.IsPanchromatic`: A cell whose vertices receive
  all `d + 1` colors.
* `CellComplex.IsDoor`: A codimension-1 face (door) whose
  remaining vertices receive colors `{0, ..., d - 1}`.

## Main results

* `CellComplex.sperner_parity`: The panchromatic cell count is
  congruent mod 2 to the boundary door count.
* `CellComplex.sperner`: If boundary doors are odd, a
  panchromatic cell exists.

## Implementation notes

The `CellComplex` structure axiomatizes exactly the adjacency
properties needed for the door-counting proof, without assuming
any geometric embedding. This follows the approach suggested by
Yaël Dillies on mathlib4#25231: prove the combinatorial core
abstractly, then separately verify that geometric simplicial
complexes satisfy the axioms.

Interior doors pair via the adjacency involution (even count).
Boundary doors are unpaired. A per-cell parity argument shows
total doors ≡ panchromatic cells (mod 2).

## References

* [M. De Longueville, *A Course in Topological Combinatorics*]

## Tags

Sperner, combinatorics, parity, triangulation, door-counting
-/

set_option maxHeartbeats 1600000

open Finset

/-- A fixed-point-free involution on a finset has even
cardinality: every element pairs with its distinct image. -/
theorem Finset.even_card_of_fpf_invol {α : Type*}
    [DecidableEq α] (S : Finset α) (f : α → α)
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
        · intro heq
          have := heq ▸ hx; simp [S'] at this
      have hcard : S.card = S'.card + 2 := by
        have hcard1 : S.card ≥ 1 :=
          Finset.one_le_card.mpr ⟨x, hx⟩
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
          rw [h] at hinv_a
          exact ha.2.1
            (hy_def.symm ▸ hinv_a).symm
        · intro h
          have hinv_a := hInv a ha.2.2
          rw [h, show f y = x from
            by rw [hy_def]; exact hInv x hx] at hinv_a
          exact ha.1 hinv_a.symm
      have hS'_sub_le : S' ⊆ S := hS'_sub.subset
      have hS'_even := ih S' hS'_sub
        (fun a ha => hInv a (hS'_sub_le ha))
        hf_S'
        (fun a ha => hNe a (hS'_sub_le ha))
      exact hS'_even.add ⟨1, rfl⟩

section DoorCountParity

/-! ### Door count parity

The central combinatorial fact: the number of "door positions"
of a coloring `f : Fin (d+1) → Fin (d+1)` has parity equal to
the surjectivity indicator of `f`.

The key invariant is the **fiber structure** of the coloring.
A surjection `Fin (d+1) → Fin d` has exactly one fiber of
size 2 (by pigeonhole), giving two door positions (even).
A bijection `Fin (d+1) → Fin (d+1)` has exactly one door
position. A non-surjection missing some lower color has none.
-/

/-- If a lower color `j₀ : Fin d` has no preimage under `f`,
then no position is a door: we cannot cover all of
`{0, ..., d-1}` while omitting any vertex. -/
private lemma door_filter_empty_of_missing_color (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1))
    (j₀ : Fin d)
    (hmiss : ¬∃ i : Fin (d + 1),
      f i = ⟨j₀.val, by omega⟩) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)) = ∅ := by
  rw [filter_eq_empty_iff]
  intro k _; push_neg
  exact ⟨j₀, fun i _ h => hmiss ⟨i, h⟩⟩

/-- When `f : Fin (d+1) → Fin d` is surjective, the door
positions are exactly the two elements of the unique fiber of
size 2 (pigeonhole). In particular, the door count is even. -/
private lemma even_card_doors_of_surjective (d : ℕ)
    (f : Fin (d + 1) → Fin d)
    (hcov : ∀ j : Fin d, ∃ i, f i = j) :
    Even (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d,
        ∃ i : Fin (d + 1), i ≠ k ∧ f i = j)).card := by
  -- Step 1: Each fiber has ≥ 1 element (surjectivity).
  -- Step 2: Total fiber sizes = d + 1, excess over 1 sums
  --   to exactly 1, so exactly one fiber has size 2.
  -- Step 3: The two elements of that fiber are precisely
  --   the two door positions.
  have hcard_ge : ∀ c : Fin d,
      (univ.filter
        (fun i : Fin (d + 1) => f i = c)).card ≥ 1 := by
    intro c; obtain ⟨i, hi⟩ := hcov c
    exact Finset.card_pos.mpr
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  have htotal : ∑ c : Fin d,
      (univ.filter
        (fun i : Fin (d + 1) => f i = c)).card =
      d + 1 := by
    rw [← Finset.card_biUnion (by
      intro x _ y _ hxy
      apply Finset.disjoint_filter.mpr
      intro i _ h1 h2; exact hxy (h1.symm.trans h2))]
    have hbU : Finset.biUnion univ (fun c : Fin d =>
        univ.filter
          (fun i : Fin (d + 1) => f i = c)) =
        univ := by
      ext i; constructor
      · intro _; exact mem_univ _
      · intro _
        rw [mem_biUnion]
        exact ⟨f i, mem_univ _,
          mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
    rw [hbU, card_univ, Fintype.card_fin]
  have hexcess : ∑ c : Fin d,
      ((univ.filter
        (fun i : Fin (d + 1) => f i = c)).card - 1) =
      1 := by
    have hadd : ∀ c : Fin d,
        (univ.filter
          (fun i : Fin (d + 1) => f i = c)).card -
          1 + 1 =
        (univ.filter
          (fun i : Fin (d + 1) => f i = c)).card := by
      intro c; have := hcard_ge c; omega
    have := Finset.sum_congr
      (show (univ : Finset (Fin d)) = univ from rfl)
      (fun c _ => hadd c)
    simp only [Finset.sum_add_distrib,
      Finset.sum_const, card_univ, Fintype.card_fin,
      htotal, smul_eq_mul] at this
    omega
  -- Unique duplicate fiber: exactly one color c₀ has
  -- fiber of size 2; all others have size 1.
  obtain ⟨c₀, hc₀_eq, hc₀_rest⟩ : ∃ c₀ : Fin d,
      (univ.filter
        (fun i : Fin (d + 1) => f i = c₀)).card = 2 ∧
      ∀ c ≠ c₀, (univ.filter
        (fun i : Fin (d + 1) => f i = c)).card = 1 := by
    have : ∃ c₀ ∈ univ,
        0 < (univ.filter
          (fun i : Fin (d + 1) => f i = c₀)).card -
          1 := by
      by_contra hall; push_neg at hall
      have h0 := fun c =>
        Nat.eq_zero_of_le_zero (hall c (mem_univ _))
      simp [h0] at hexcess
    obtain ⟨c₀, _, hc₀⟩ := this
    refine ⟨c₀, ?_, ?_⟩
    · by_contra hne2
      have hge2 :
          (univ.filter
            (fun i : Fin (d + 1) =>
              f i = c₀)).card - 1 ≥ 2 := by
        omega
      let F : Fin d → ℕ := fun c =>
        (univ.filter
          (fun i : Fin (d + 1) => f i = c)).card - 1
      have hFc₀ : F c₀ ≥ 2 := hge2
      have hle : F c₀ ≤ ∑ x : Fin d, F x :=
        single_le_sum
          (fun _ _ => Nat.zero_le _) (mem_univ c₀)
      have hexcess' : ∑ c : Fin d, F c = 1 := hexcess
      omega
    · intro c hc; by_contra hne1
      have hge1_card :
          (univ.filter
            (fun i : Fin (d + 1) =>
              f i = c)).card ≥ 2 := by
        have := hcard_ge c; omega
      have hge1 :
          (univ.filter
            (fun i : Fin (d + 1) =>
              f i = c)).card - 1 ≥ 1 := by
        omega
      let F : Fin d → ℕ := fun c =>
        (univ.filter
          (fun i : Fin (d + 1) => f i = c)).card - 1
      have hFc₀ : F c₀ ≥ 1 := by
        have := hc₀; show _ - 1 ≥ 1; omega
      have hFc : F c ≥ 1 := hge1
      have h₁ : F c₀ ≤ ∑ x : Fin d, F x :=
        single_le_sum
          (fun _ _ => Nat.zero_le _) (mem_univ c₀)
      have h₂ : F c ≤ ∑ x : Fin d, F x :=
        single_le_sum
          (fun _ _ => Nat.zero_le _) (mem_univ c)
      have hsum := sum_le_sum_of_subset (f := F)
        (subset_univ ({c₀, c} : Finset (Fin d)))
      rw [sum_pair hc.symm] at hsum
      have hexcess' : ∑ c : Fin d, F c = 1 := hexcess
      omega
  obtain ⟨k₁, k₂, hk₁, hk₂, hne12, hpair⟩ :
      ∃ k₁ k₂ : Fin (d + 1),
        f k₁ = c₀ ∧ f k₂ = c₀ ∧ k₁ ≠ k₂ ∧
        univ.filter
          (fun i : Fin (d + 1) => f i = c₀) =
          {k₁, k₂} := by
    rw [Finset.card_eq_two] at hc₀_eq
    obtain ⟨a, b, hab, habset⟩ := hc₀_eq
    have ha := (mem_filter.mp
      (habset ▸ mem_insert_self a {b})).2
    have hb := (mem_filter.mp
      (habset ▸ mem_insert.mpr
        (Or.inr (mem_singleton.mpr rfl)))).2
    exact ⟨a, b, ha, hb, hab, habset⟩
  suffices hset : univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d,
        ∃ i : Fin (d + 1), i ≠ k ∧ f i = j) =
      {k₁, k₂} by
    rw [hset, card_pair hne12]; exact even_two
  ext k
  simp only [mem_filter, mem_univ, true_and,
    mem_insert, mem_singleton]
  constructor
  · intro hk
    obtain ⟨i, hi_ne, hi_eq⟩ := hk (f k)
    have hfk : f k = c₀ := by
      by_contra hne
      have hmult1 := hc₀_rest (f k) hne
      rw [Finset.card_eq_one] at hmult1
      obtain ⟨a, ha⟩ := hmult1
      have hk_in : k ∈ univ.filter
          (fun i : Fin (d + 1) => f i = f k) :=
        mem_filter.mpr ⟨mem_univ _, rfl⟩
      have hi_in : i ∈ univ.filter
          (fun i : Fin (d + 1) => f i = f k) :=
        mem_filter.mpr ⟨mem_univ i, hi_eq⟩
      rw [ha] at hk_in hi_in
      simp at hk_in hi_in
      exact hi_ne (hk_in ▸ hi_in)
    have hk_mem : k ∈ univ.filter
        (fun i : Fin (d + 1) => f i = c₀) :=
      mem_filter.mpr ⟨mem_univ k, hfk⟩
    rw [hpair] at hk_mem; simp at hk_mem; exact hk_mem
  · intro hk j
    obtain ⟨i₀, hi₀⟩ := hcov j
    by_cases hik : i₀ = k
    · rcases hk with heq | heq
      · have hfk : f k = c₀ := heq ▸ hk₁
        have hj_c0 : j = c₀ := by
          rw [← hi₀, hik, hfk]
        exact ⟨k₂, (heq ▸ hne12).symm,
          by rw [hj_c0, hk₂]⟩
      · have hfk : f k = c₀ := heq ▸ hk₂
        have hj_c0 : j = c₀ := by
          rw [← hi₀, hik, hfk]
        exact ⟨k₁, heq ▸ hne12,
          by rw [hj_c0, hk₁]⟩
    · exact ⟨i₀, hik, hi₀⟩

/-- **Door count parity**: the number of door positions of a
coloring `f : Fin (d+1) → Fin (d+1)` has parity equal to 1
if `f` is surjective, and 0 otherwise. -/
theorem door_count_parity (d : ℕ)
    (f : Fin (d + 1) → Fin (d + 1)) :
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card % 2 =
    if Function.Surjective f then 1 else 0 := by
  by_cases hsurj : Function.Surjective f
  · -- Case 1: f is surjective (bijective).
    -- The unique preimage of d is the sole door position.
    rw [if_pos hsurj]
    have hinj :=
      Finite.injective_iff_surjective.mpr hsurj
    obtain ⟨k₀, hk₀⟩ := hsurj ⟨d, by omega⟩
    have huniq : ∀ k, f k = ⟨d, by omega⟩ → k = k₀ :=
      fun k hk => hinj (hk.trans hk₀.symm)
    suffices hset : univ.filter
        (fun k : Fin (d + 1) =>
          ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
            f i = ⟨j.val, by omega⟩) = {k₀} by
      rw [hset, card_singleton]
    ext k
    simp only [mem_filter, mem_univ, true_and,
      mem_singleton]
    constructor
    · intro hk; by_contra hne
      have hfk_ne : f k ≠ ⟨d, by omega⟩ :=
        fun h => hne (huniq k h)
      have hfk_val_ne : (f k).val ≠ d :=
        fun h => hfk_ne (Fin.ext h)
      have hfk_lt : (f k).val < d := by
        have := (f k).isLt; omega
      obtain ⟨i, hi_ne, hi_eq⟩ :=
        hk ⟨(f k).val, hfk_lt⟩
      have hval : (f i).val = (f k).val := by
        have h1 := congr_arg Fin.val hi_eq
        simp at h1; exact h1
      exact hi_ne (hinj (Fin.ext hval))
    · intro hk; subst hk; intro ⟨j, hj⟩
      obtain ⟨i, hi⟩ := hsurj ⟨j, by omega⟩
      exact ⟨i,
        fun hik => by
          subst hik; rw [hk₀] at hi
          exact absurd hi (by simp; omega),
        by rw [hi]⟩
  · rw [if_neg hsurj]
    by_cases hd_app : ∃ i, f i = ⟨d, by omega⟩
    · -- Case 2: Not surjective, but top color d has a
      -- preimage. Some lower color j₀ must be missing,
      -- so no door positions exist.
      have ⟨j₀, hj₀⟩ : ∃ j : Fin d,
          ¬∃ i, f i =
            ⟨j.val, Nat.lt_succ_of_lt j.isLt⟩ := by
        by_contra hall; push_neg at hall; apply hsurj
        intro ⟨y, hy⟩; by_cases hyd : y = d
        · subst hyd; exact hd_app
        · exact hall ⟨y, by omega⟩
      rw [Finset.card_eq_zero.mpr
        (door_filter_empty_of_missing_color d f j₀ hj₀)]
    · -- Case 3: Top color d never appears. Truncate f to
      -- g : Fin (d+1) → Fin d and analyze g's surjectivity.
      push_neg at hd_app
      have hlt : ∀ i, (f i).val < d := by
        intro i; have := (f i).isLt
        by_contra h; push_neg at h
        have hlt2 := (f i).isLt
        have : (f i).val = d := by omega
        exact hd_app i (Fin.ext this)
      let g : Fin (d + 1) → Fin d :=
        fun i => ⟨(f i).val, hlt i⟩
      by_cases hgsurj : Function.Surjective g
      · -- Case 3a: g is surjective. By pigeonhole, g has
        -- a unique duplicated fiber, giving two door
        -- positions (even count).
        have heven :=
          even_card_doors_of_surjective d g hgsurj
        suffices heq : univ.filter
            (fun k : Fin (d + 1) =>
              ∀ j : Fin d,
                ∃ i : Fin (d + 1), i ≠ k ∧
                  f i = ⟨j.val, by omega⟩) =
            univ.filter (fun k : Fin (d + 1) =>
              ∀ j : Fin d,
                ∃ i : Fin (d + 1),
                  i ≠ k ∧ g i = j) by
          rw [heq]; exact Nat.even_iff.mp heven
        ext k
        simp only [mem_filter, mem_univ, true_and]
        constructor <;> intro h j
        · obtain ⟨i, hi, hfi⟩ := h j
          exact ⟨i, hi, Fin.ext (by
            simp [g]
            exact congr_arg Fin.val hfi)⟩
        · obtain ⟨i, hi, hgi⟩ := h j
          exact ⟨i, hi, Fin.ext (by
            have := congr_arg Fin.val hgi
            simp [g] at this; exact this)⟩
      · -- Case 3b: g is not surjective. Some lower color
        -- j₀ has no preimage under g (hence under f),
        -- so no door positions exist.
        have ⟨j₀, hj₀⟩ :
            ∃ j : Fin d, ¬∃ i, g i = j := by
          by_contra h; push_neg at h; exact hgsurj h
        suffices h0 : (univ.filter
            (fun k : Fin (d + 1) =>
              ∀ j : Fin d,
                ∃ i : Fin (d + 1), i ≠ k ∧
                  f i = ⟨j.val, by omega⟩)).card =
            0 by rw [h0]
        rw [Finset.card_eq_zero, filter_eq_empty_iff]
        intro k _; push_neg
        exact ⟨j₀, fun i _ h =>
          hj₀ ⟨i, Fin.ext (by
            have := congr_arg Fin.val h
            simp at this; exact this)⟩⟩

end DoorCountParity

/-- An abstract cell complex with adjacency, parametrized by
vertex type `V` and dimension `d`. Each cell has `d + 1`
vertices from `V`. Interior codimension-1 faces pair via
`adj`; boundary faces have `adj = none`. -/
structure CellComplex (V : Type*) [DecidableEq V]
    (d : ℕ) where
  /-- The type of top-dimensional cells. -/
  Cell : Type
  /-- Decidable equality on cells. -/
  cellDecEq : DecidableEq Cell
  /-- Finiteness of cells. -/
  cellFintype : Fintype Cell
  /-- The `d + 1` vertices of each cell. -/
  vertex : Cell → Fin (d + 1) → V
  /-- Vertices of each cell are distinct. Not used in the
  abstract parity proof, but required by geometric instances
  (e.g., simplicial complexes satisfy this). -/
  vertex_injective :
    ∀ s, Function.Injective (vertex s)
  /-- Adjacency: the face opposite vertex `k` in cell `s`
  is shared with another cell, or is a boundary face. -/
  adj : Cell → Fin (d + 1) →
    Option (Cell × Fin (d + 1))
  /-- Adjacency is symmetric. -/
  adj_symm : ∀ s k s' k',
    adj s k = some (s', k') →
    adj s' k' = some (s, k)
  /-- Adjacent cells share the codimension-1 face. -/
  adj_vertex : ∀ s k s' k',
    adj s k = some (s', k') →
    (univ.erase k).image (vertex s) =
    (univ.erase k').image (vertex s')
  /-- Adjacent cells are distinct. -/
  adj_ne : ∀ s k s' k',
    adj s k = some (s', k') → s ≠ s'

attribute [instance] CellComplex.cellDecEq
attribute [instance] CellComplex.cellFintype

namespace CellComplex

variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- A cell is *panchromatic* (fully colored): the coloring
restricted to its vertices is surjective onto `Fin (d+1)`. -/
def IsPanchromatic (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell) : Prop :=
  Function.Surjective (c ∘ K.vertex s)

/-- A facet `(s, k)` is a *door*: removing vertex `k`, the
remaining `d` vertices carry all colors `{0, ..., d-1}`. -/
def IsDoor (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell)
    (k : Fin (d + 1)) : Prop :=
  ∀ j : Fin d, ∃ i : Fin (d + 1),
    i ≠ k ∧ c (K.vertex s i) = Fin.castSucc j

instance decidableIsPanchromatic
    (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Cell) :
    Decidable (IsPanchromatic c K s) := by
  unfold IsPanchromatic Function.Surjective
  exact inferInstance

instance decidableIsDoor (c : V → Fin (d + 1))
    (K : CellComplex V d) (s : K.Cell)
    (k : Fin (d + 1)) :
    Decidable (IsDoor c K s k) := by
  unfold IsDoor; exact inferInstance

/-- The adjacency map: sends `(s, k)` to its adjacent
cell-face pair, or to itself if on the boundary. -/
private def adjMap (K : CellComplex V d)
    (p : K.Cell × Fin (d + 1)) :
    K.Cell × Fin (d + 1) :=
  match K.adj p.1 p.2 with
  | some (s', k') => (s', k')
  | none => p

/-- A door transfers through a shared face (one direction). -/
private lemma isDoor_of_shared_face
    {c : V → Fin (d + 1)} {K : CellComplex V d}
    {s : K.Cell} {k : Fin (d + 1)}
    {s' : K.Cell} {k' : Fin (d + 1)}
    (hvert :
      (univ.erase k).image (K.vertex s) =
      (univ.erase k').image (K.vertex s'))
    (h : IsDoor c K s k) : IsDoor c K s' k' := by
  intro j
  obtain ⟨i, hi_ne, hi_eq⟩ := h j
  have hmem : K.vertex s i ∈
      (univ.erase k').image (K.vertex s') := by
    rw [← hvert]
    exact mem_image.mpr
      ⟨i, mem_erase.mpr ⟨hi_ne, mem_univ _⟩, rfl⟩
  obtain ⟨i', hi'_mem, hi'_eq⟩ := mem_image.mp hmem
  exact ⟨i', (mem_erase.mp hi'_mem).1,
    by rw [hi'_eq]; exact hi_eq⟩

/-- A door transfers through adjacency (iff version). -/
private lemma isDoor_iff_of_adj
    {c : V → Fin (d + 1)} {K : CellComplex V d}
    {s : K.Cell} {k : Fin (d + 1)}
    {s' : K.Cell} {k' : Fin (d + 1)}
    (hadj : K.adj s k = some (s', k')) :
    IsDoor c K s k ↔ IsDoor c K s' k' :=
  ⟨isDoor_of_shared_face
    (K.adj_vertex s k s' k' hadj),
   isDoor_of_shared_face
    (K.adj_vertex s k s' k' hadj).symm⟩

/-- Interior doors pair up via the adjacency involution,
so their count is even. -/
theorem even_card_interiorDoors
    (c : V → Fin (d + 1)) (K : CellComplex V d) :
    Even (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 ≠ none)).card := by
  set S := univ.filter
    (fun p : K.Cell × Fin (d + 1) =>
      IsDoor c K p.1 p.2 ∧ K.adj p.1 p.2 ≠ none)
  apply Finset.even_card_of_fpf_invol S (adjMap K)
  · intro p hp
    simp only [S, mem_filter, mem_univ,
      true_and] at hp
    obtain ⟨_, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back :=
        K.adj_symm p.1 p.2 s' k' hadj_eq
      show adjMap K (adjMap K p) = p
      simp only [adjMap, hadj_eq, hadj_back]
  · intro p hp
    simp only [S, mem_filter, mem_univ,
      true_and] at hp ⊢
    obtain ⟨hdoor, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      have hadj_back :=
        K.adj_symm p.1 p.2 s' k' hadj_eq
      show IsDoor c K (adjMap K p).1
          (adjMap K p).2 ∧
        K.adj (adjMap K p).1 (adjMap K p).2 ≠ none
      simp only [adjMap, hadj_eq]
      exact ⟨(isDoor_iff_of_adj hadj_eq).mp hdoor,
        by rw [hadj_back]; exact Option.noConfusion⟩
  · intro p hp
    simp only [S, mem_filter, mem_univ,
      true_and] at hp
    obtain ⟨_, hadj_ne⟩ := hp
    cases hadj_eq : K.adj p.1 p.2 with
    | none => exact absurd hadj_eq hadj_ne
    | some sk =>
      obtain ⟨s', k'⟩ := sk
      show adjMap K p ≠ p
      simp only [adjMap, hadj_eq]
      intro heq
      exact K.adj_ne p.1 p.2 s' k' hadj_eq
        (congr_arg Prod.fst heq).symm

/-- Per-cell door parity: the door count of a single cell
has the same parity as its panchromaticity indicator. -/
private lemma per_cell_door_parity
    (c : V → Fin (d + 1)) (K : CellComplex V d)
    (s : K.Cell) :
    (univ.filter (fun k : Fin (d + 1) =>
      IsDoor c K s k)).card % 2 =
    if IsPanchromatic c K s then 1 else 0 := by
  have h := door_count_parity d (c ∘ K.vertex s)
  have h1 : (univ.filter (fun k : Fin (d + 1) =>
      IsDoor c K s k)) =
    (univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        (c ∘ K.vertex s) i =
          ⟨j.val, by omega⟩)) := by
    ext k
    simp only [mem_filter, mem_univ, true_and]; rfl
  rw [h1]
  have h2 : IsPanchromatic c K s ↔
      Function.Surjective (c ∘ K.vertex s) := Iff.rfl
  simp only [h2]
  convert h using 2

private lemma sum_mod_congr {ι : Type*}
    (S : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ S, a i % 2 = b i % 2) :
    (∑ i ∈ S, a i) % 2 =
    (∑ i ∈ S, b i) % 2 := by
  induction S using Finset.cons_induction with
  | empty => simp
  | cons x s hx ih =>
    rw [sum_cons, sum_cons]
    have hx_eq :=
      h x (mem_cons_self x s)
    have hs_eq := ih
      (fun i hi => h i (mem_cons.mpr (Or.inr hi)))
    omega

private lemma card_doors_eq_sum
    (c : V → Fin (d + 1)) (K : CellComplex V d) :
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2)).card =
    ∑ s : K.Cell, (univ.filter
      (fun k : Fin (d + 1) =>
        IsDoor c K s k)).card := by
  have hlhs : (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2)).card =
    ∑ p : K.Cell × Fin (d + 1),
      if IsDoor c K p.1 p.2 then 1 else 0 := by
    rw [sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul, mul_one]
  have hrhs : ∀ s : K.Cell,
      (univ.filter (fun k : Fin (d + 1) =>
        IsDoor c K s k)).card =
      ∑ k : Fin (d + 1),
        if IsDoor c K s k then 1 else 0 := by
    intro s
    rw [sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul, mul_one]
  rw [hlhs, sum_congr rfl (fun s _ => hrhs s)]
  rw [← Fintype.sum_prod_type']

private lemma doors_partition
    (c : V → Fin (d + 1)) (K : CellComplex V d) :
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2)).card =
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 ≠ none)).card +
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 = none)).card := by
  rw [← card_union_of_disjoint]
  · congr 1; ext p
    simp only [mem_filter, mem_univ, true_and,
      mem_union]
    constructor
    · intro h
      by_cases hadj : K.adj p.1 p.2 = none
      · right; exact ⟨h, hadj⟩
      · left; exact ⟨h, hadj⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  · rw [disjoint_left]
    intro p h₁ h₂
    simp only [mem_filter, mem_univ,
      true_and] at h₁ h₂
    exact h₁.2 h₂.2

/-- **Sperner Parity Theorem**: the panchromatic cell count
is congruent mod 2 to the boundary door count. -/
theorem sperner_parity (c : V → Fin (d + 1))
    (K : CellComplex V d) :
    (univ.filter (fun s : K.Cell =>
      IsPanchromatic c K s)).card % 2 =
    (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 = none)).card % 2 := by
  have hper := per_cell_door_parity c K
  have hsum :
      (∑ s : K.Cell, (univ.filter
        (fun k => IsDoor c K s k)).card) % 2 =
      (∑ s : K.Cell,
        if IsPanchromatic c K s
        then 1 else 0) % 2 :=
    sum_mod_congr univ _ _ (fun s _ => by
      rw [hper s]; split <;> simp)
  have hfc_sum :
      (∑ s : K.Cell,
        if IsPanchromatic c K s
        then (1 : ℕ) else 0) =
      (univ.filter
        (fun s => IsPanchromatic c K s)).card := by
    rw [sum_ite, sum_const_zero, add_zero,
      sum_const, smul_eq_mul, mul_one]
  have hdoor_sum := card_doors_eq_sum c K
  have hpart := doors_partition c K
  have heven := even_card_interiorDoors c K
  obtain ⟨m, hm⟩ := heven
  calc (univ.filter
      (fun s => IsPanchromatic c K s)).card % 2
    _ = (∑ s : K.Cell,
        if IsPanchromatic c K s
        then 1 else 0) % 2 := by rw [hfc_sum]
    _ = (∑ s : K.Cell, (univ.filter
        (fun k => IsDoor c K s k)).card) % 2 :=
      hsum.symm
    _ = (univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2)).card % 2 := by
      rw [hdoor_sum]
    _ = ((univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2 ∧
          K.adj p.1 p.2 ≠ none)).card +
       (univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2 ∧
          K.adj p.1 p.2 = none)).card) % 2 := by
      rw [hpart]
    _ = (univ.filter
        (fun p : K.Cell × Fin (d + 1) =>
          IsDoor c K p.1 p.2 ∧
          K.adj p.1 p.2 = none)).card % 2 := by
      rw [hm, Nat.add_mod,
        show (m + m) % 2 = 0 from by omega,
        Nat.zero_add, Nat.mod_mod_of_dvd]
      exact ⟨1, rfl⟩

/-- **Sperner's Lemma**: if boundary doors are odd, a
panchromatic cell exists. -/
theorem sperner (c : V → Fin (d + 1))
    (K : CellComplex V d)
    (hbdry : Odd (univ.filter
      (fun p : K.Cell × Fin (d + 1) =>
        IsDoor c K p.1 p.2 ∧
        K.adj p.1 p.2 = none)).card) :
    ∃ s : K.Cell, IsPanchromatic c K s := by
  have hparity := sperner_parity c K
  have hodd : Odd (univ.filter
      (fun s : K.Cell =>
        IsPanchromatic c K s)).card := by
    rwa [Nat.odd_iff, hparity, ← Nat.odd_iff]
  have hpos : 0 < (univ.filter
      (fun s => IsPanchromatic c K s)).card := by
    obtain ⟨k, hk⟩ := hodd; omega
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
  exact ⟨s, (mem_filter.mp hs).2⟩

end CellComplex
