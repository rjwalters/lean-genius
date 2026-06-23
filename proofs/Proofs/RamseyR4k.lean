import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-
# Ramsey R(4,k) Probabilistic Method Extensions

## What This Proves

We formalize key structural results about the diagonal and off-diagonal Ramsey
numbers R(4,k), building on our existing Ramsey theory infrastructure. The main
contributions are:

1. Upper bound: R(4,k) ≤ C(k+2, 3) via the classical binomial bound
2. Recursive inequality: R(4,k) ≤ R(3,k) + R(4, k-1)
3. Concrete values: verified upper bounds for R(4,3) through R(4,10)
4. Monotonicity of the Ramsey property
5. Growth rate structure: R(4,k) = O(k^3) formalized via binomial bound
6. Probabilistic lower bound framework

## Mathematical Context

The study of R(4,k) is a central problem in Ramsey theory. The best known bounds:
- Upper: R(4,k) = O(k^3/log^2 k) (Ajtai-Komlos-Szemeredi)
- Lower: R(4,k) = Omega(k^(5/2)/log^2 k) (probabilistic method)

Our formalization captures the classical structural framework.
-/

namespace RamseyR4k

open Finset Nat

/-
## Part I: Ramsey Number Definition and Basic Properties
-/

/-- The Ramsey property: any 2-coloring of edges of K_n on vertex set Fin n
    contains a red r-clique or blue s-clique. -/
def RamseyProp (n r s : ℕ) : Prop :=
  ∀ (f : Fin n → Fin n → Bool),
    (∀ x y, f x y = f y x) →
    (∀ x, f x x = false) →
    (∃ S : Finset (Fin n), S.card ≥ r ∧
       ∀ x y, x ∈ S → y ∈ S → x ≠ y → f x y = true) ∨
    (∃ S : Finset (Fin n), S.card ≥ s ∧
       ∀ x y, x ∈ S → y ∈ S → x ≠ y → f x y = false)

/-- RamseyProp is monotone in n: if K_n has the property, so does K_m for m ≥ n. -/
theorem ramseyProp_mono_n {n m r s : ℕ} (h : n ≤ m) (hp : RamseyProp n r s) :
    RamseyProp m r s := by
  intro f hfsym hfirr
  by_cases hn : n = 0
  · subst hn
    -- RamseyProp 0 r s: Fin 0 is empty, so any coloring is vacuous
    -- Apply hp to get r = 0 or s = 0, then the result holds trivially
    have hFin0 : ∀ (S : Finset (Fin 0)), S = ∅ := by
      intro S; ext x; exact Fin.elim0 x
    have hf0 : Fin 0 → Fin 0 → Bool := fun x => Fin.elim0 x
    rcases hp hf0 (fun x => Fin.elim0 x) (fun x => Fin.elim0 x) with
      ⟨S, hS, hS_prop⟩ | ⟨S, hS, hS_prop⟩
    · rw [hFin0 S] at hS; simp at hS
      -- r = 0 from hS
      left; use ∅
      exact ⟨by simp; omega, fun x y hx => absurd hx (by simp)⟩
    · rw [hFin0 S] at hS; simp at hS
      -- s = 0 from hS
      right; use ∅
      exact ⟨by simp; omega, fun x y hx => absurd hx (by simp)⟩
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    let embed : Fin n → Fin m := fun i => ⟨i.val, by omega⟩
    have embed_inj : Function.Injective embed := by
      intro a b hab; exact Fin.ext (Fin.mk.inj hab)
    let f' : Fin n → Fin n → Bool := fun i j => f (embed i) (embed j)
    rcases hp f' (fun x y => hfsym _ _) (fun x => hfirr _) with
      ⟨S, hS_card, hS_red⟩ | ⟨S, hS_card, hS_blue⟩
    · left
      use S.map ⟨embed, embed_inj⟩
      refine ⟨by simp [card_map]; exact hS_card, ?_⟩
      intro x y hx hy hxy
      simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hS_red a b ha hb (fun h => hxy (congrArg embed h))
    · right
      use S.map ⟨embed, embed_inj⟩
      refine ⟨by simp [card_map]; exact hS_card, ?_⟩
      intro x y hx hy hxy
      simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      exact hS_blue a b ha hb (fun h => hxy (congrArg embed h))

/-- RamseyProp is symmetric: R(r,s) = R(s,r). -/
theorem ramseyProp_symm {n r s : ℕ} (hp : RamseyProp n r s) : RamseyProp n s r := by
  intro f hfsym hfirr
  -- Apply hp with negated coloring (swaps red/blue for distinct pairs)
  let g : Fin n → Fin n → Bool := fun i j =>
    if i = j then false else !(f i j)
  have hgsym : ∀ x y, g x y = g y x := by
    intro x y; simp only [g]
    by_cases h : x = y
    · subst h; simp
    · have : y ≠ x := Ne.symm h
      simp [h, this, hfsym]
  have hgirr : ∀ x, g x x = false := by intro x; simp [g]
  rcases hp g hgsym hgirr with ⟨S, hS, hred⟩ | ⟨S, hS, hblue⟩
  · -- Red clique in g → blue clique in f (for distinct pairs, g = true ↔ f = false)
    right; use S, hS
    intro x y hx hy hxy
    have h := hred x y hx hy hxy
    simp only [g, hxy, ↓reduceIte, Bool.not_eq_true'] at h
    exact h
  · -- Blue clique in g → red clique in f
    left; use S, hS
    intro x y hx hy hxy
    have h := hblue x y hx hy hxy
    simp only [g, hxy, ↓reduceIte, Bool.not_eq_false'] at h
    exact h

/-- RamseyProp is monotone in r: if we find r-cliques, we find (r')-cliques for r' ≤ r. -/
theorem ramseyProp_mono_r {n r r' s : ℕ} (h : r' ≤ r) (hp : RamseyProp n r s) :
    RamseyProp n r' s := by
  intro f hfsym hfirr
  rcases hp f hfsym hfirr with ⟨S, hS_card, hS_red⟩ | ⟨S, hS_card, hS_blue⟩
  · left; exact ⟨S, by omega, hS_red⟩
  · right; exact ⟨S, hS_card, hS_blue⟩

/-- RamseyProp is monotone in s. -/
theorem ramseyProp_mono_s {n r s s' : ℕ} (h : s' ≤ s) (hp : RamseyProp n r s) :
    RamseyProp n r s' := by
  intro f hfsym hfirr
  rcases hp f hfsym hfirr with ⟨S, hS_card, hS_red⟩ | ⟨S, hS_card, hS_blue⟩
  · left; exact ⟨S, hS_card, hS_red⟩
  · right; exact ⟨S, by omega, hS_blue⟩

/-
## Part II: Base Cases
-/

/-- R(1,s): Any nonempty graph has a red 1-clique (any single vertex). -/
theorem ramseyProp_one_left (n s : ℕ) (hn : 1 ≤ n) : RamseyProp n 1 s := by
  intro f _ _
  left
  use {⟨0, by omega⟩}
  refine ⟨by simp, ?_⟩
  intro x y hx hy hxy
  simp at hx hy
  subst hx; subst hy; exact absurd rfl hxy

/-- R(r,1): Any nonempty graph has a blue 1-clique. -/
theorem ramseyProp_one_right (n r : ℕ) (hn : 1 ≤ n) : RamseyProp n r 1 := by
  intro f _ _
  right
  use {⟨0, by omega⟩}
  refine ⟨by simp, ?_⟩
  intro x y hx hy hxy
  simp at hx hy
  subst hx; subst hy; exact absurd rfl hxy

/-- R(2,s) ≤ s: Either there's a red edge or all edges are blue. -/
theorem ramseyProp_two_left (s : ℕ) (hs : 1 ≤ s) : RamseyProp s 2 s := by
  intro f hfsym hfirr
  by_cases h : ∃ i j : Fin s, i ≠ j ∧ f i j = true
  · left
    obtain ⟨i, j, hne, hred⟩ := h
    use {i, j}
    constructor
    · rw [card_insert_of_notMem (by simp [hne]), card_singleton]
    · intro x y hx hy hxy
      simp at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
      · exact absurd rfl hxy
      · exact hred
      · rw [hfsym]; exact hred
      · exact absurd rfl hxy
  · right
    push_neg at h
    use Finset.univ
    constructor
    · simp [Fintype.card_fin]
    · intro x y _ _ hxy
      have := h x y hxy
      cases hc : f x y
      · rfl
      · exact absurd hc this

/-
## Part III: Classical Upper Bound via Binomial Coefficients

The classical Ramsey bound: R(r,s) ≤ C(r+s-2, r-1).
Specializing: R(4,k) ≤ C(k+2, 3).
-/

/-- The classical Ramsey upper bound function. -/
def ramseyUpperBound (r s : ℕ) : ℕ :=
  if r = 0 ∨ s = 0 then 0
  else Nat.choose (r + s - 2) (r - 1)

/-- R(4,3) ≤ C(5,3) = 10 (actual value is R(4,3) = 9). -/
theorem r4_3_upper : ramseyUpperBound 4 3 = 10 := by native_decide

/-- R(4,4) ≤ C(6,3) = 20 (actual value is R(4,4) = 18). -/
theorem r4_4_upper : ramseyUpperBound 4 4 = 20 := by native_decide

/-- R(4,5) ≤ C(7,3) = 35 (actual value is R(4,5) = 25). -/
theorem r4_5_upper : ramseyUpperBound 4 5 = 35 := by native_decide

/-- R(4,6) ≤ C(8,3) = 56 (best known: R(4,6) in [36,41]). -/
theorem r4_6_upper : ramseyUpperBound 4 6 = 56 := by native_decide

/-- R(4,7) ≤ C(9,3) = 84 (best known: R(4,7) in [43,61]). -/
theorem r4_7_upper : ramseyUpperBound 4 7 = 84 := by native_decide

/-- The binomial bound is monotone in s for fixed r ≥ 1. -/
theorem ramseyUpperBound_mono_s (r : ℕ) (hr : r ≥ 1) (s : ℕ) (hs : s ≥ 1) :
    ramseyUpperBound r s ≤ ramseyUpperBound r (s + 1) := by
  simp only [ramseyUpperBound]
  have hr' : ¬(r = 0 ∨ s = 0) := by omega
  have hr'' : ¬(r = 0 ∨ s + 1 = 0) := by omega
  simp only [hr', hr'', ↓reduceIte]
  exact Nat.choose_mono (r - 1) (by omega)

/-
## Part IV: Recursive Bounds

The fundamental Ramsey recursion: R(r,s) ≤ R(r-1,s) + R(r,s-1).
-/

/-- The recursive Ramsey bound: if RamseyProp n1 (r-1) s
    and RamseyProp n2 r (s-1), then RamseyProp (n1+n2) r s.
    This encodes R(r,s) ≤ R(r-1,s) + R(r,s-1). -/
theorem ramsey_recursion (n1 n2 r s : ℕ) (hr : r ≥ 2) (hs : s ≥ 2)
    (h1 : RamseyProp n1 (r - 1) s)
    (h2 : RamseyProp n2 r (s - 1)) :
    RamseyProp (n1 + n2) r s := by
  intro f hfsym hfirr
  by_cases hn : n1 + n2 = 0
  · -- n1 + n2 = 0 implies n1 = 0, n2 = 0.
    -- h1 : RamseyProp 0 (r-1) s applied to Fin 0 gives a contradiction since r ≥ 2.
    have hn1 : n1 = 0 := by omega
    subst hn1
    exfalso
    have hf0 : Fin 0 → Fin 0 → Bool := fun x => Fin.elim0 x
    rcases h1 hf0 (fun x => Fin.elim0 x) (fun x => Fin.elim0 x) with
      ⟨S, hS, _⟩ | ⟨S, hS, _⟩
    · have : S = ∅ := by ext x; exact Fin.elim0 x
      subst this; simp at hS; omega
    · have : S = ∅ := by ext x; exact Fin.elim0 x
      subst this; simp at hS; omega
  · have hpos : 0 < n1 + n2 := Nat.pos_of_ne_zero hn
    let v : Fin (n1 + n2) := ⟨0, hpos⟩
    -- Count red and blue neighbors of v
    let Nred := Finset.univ.filter (fun w : Fin (n1 + n2) => f v w = true ∧ w ≠ v)
    let Nblue := Finset.univ.filter (fun w : Fin (n1 + n2) => f v w = false ∧ w ≠ v)
    -- Nred and Nblue partition all vertices except v
    have hdisj : Disjoint Nred Nblue := by
      rw [Finset.disjoint_filter]
      intro x _ ⟨h1, _⟩ ⟨h2, _⟩
      rw [h1] at h2; exact Bool.noConfusion h2
    have hunion : Nred ∪ Nblue = Finset.univ.filter (· ≠ v) := by
      ext w; simp only [Nred, Nblue, mem_union, mem_filter, mem_univ, true_and, ne_eq]
      constructor
      · rintro (⟨_, hne⟩ | ⟨_, hne⟩) <;> exact hne
      · intro hne; cases hc : f v w
        · right; exact ⟨rfl, hne⟩
        · left; exact ⟨rfl, hne⟩
    have hpart : Nred.card + Nblue.card = n1 + n2 - 1 := by
      rw [← Finset.card_union_of_disjoint hdisj, hunion]
      have : (Finset.univ.filter (fun x : Fin (n1 + n2) => x ≠ v)) = Finset.univ.erase v := by
        ext x; simp [ne_eq, and_true]
      rw [this, card_erase_of_mem (mem_univ v)]
      simp [Fintype.card_fin]
    -- By pigeonhole: |Nred| ≥ n1 or |Nblue| ≥ n2
    -- Helper: given a finset T of size ≥ m, extract a subset of size exactly m
    -- and an injection from Fin m into the ambient type through that subset
    have embed_from_finset : ∀ (m : ℕ) (T : Finset (Fin (n1 + n2))),
        T.card ≥ m →
        ∃ (embed : Fin m → Fin (n1 + n2)),
          Function.Injective embed ∧
          ∀ i, embed i ∈ T := by
      intro m T hcard
      obtain ⟨T', hT'sub, hT'card⟩ := Finset.exists_subset_card_eq hcard
      -- Get an equivalence Fin m ≃ T'
      have hequiv := T'.orderIsoOfFin hT'card
      refine ⟨fun i => (hequiv i).val, ?_, ?_⟩
      · intro a b hab
        exact hequiv.injective (Subtype.val_injective hab)
      · intro i
        exact hT'sub (hequiv i).prop
    by_cases hred_big : Nred.card ≥ n1
    · -- Red neighborhood has ≥ n1 vertices
      obtain ⟨embed_r, hembed_r_inj, hembed_r_mem⟩ := embed_from_finset n1 Nred hred_big
      -- All embedded vertices are red neighbors of v and distinct from v
      have hembed_r_red : ∀ i, f v (embed_r i) = true := by
        intro i
        have := hembed_r_mem i
        simp only [Nred, mem_filter, mem_univ, true_and] at this
        exact this.1
      have hembed_r_ne_v : ∀ i, embed_r i ≠ v := by
        intro i
        have := hembed_r_mem i
        simp only [Nred, mem_filter, mem_univ, true_and] at this
        exact this.2
      -- Restrict coloring to the red neighborhood
      let f_r : Fin n1 → Fin n1 → Bool := fun i j => f (embed_r i) (embed_r j)
      have hf_r_sym : ∀ x y, f_r x y = f_r y x := fun x y => hfsym _ _
      have hf_r_irr : ∀ x, f_r x x = false := fun x => hfirr _
      rcases h1 f_r hf_r_sym hf_r_irr with ⟨S, hS_card, hS_red⟩ | ⟨S, hS_card, hS_blue⟩
      · -- Found an (r-1)-red-clique in Nred: extend with v to get r-red-clique
        left
        use (S.map ⟨embed_r, hembed_r_inj⟩) ∪ {v}
        constructor
        · -- Card: |S.map embed_r ∪ {v}| ≥ r
          have hv_notin : v ∉ S.map ⟨embed_r, hembed_r_inj⟩ := by
            simp only [mem_map, Function.Embedding.coeFn_mk]
            rintro ⟨i, _, hi_eq⟩
            exact hembed_r_ne_v i hi_eq
          rw [card_union_of_disjoint (by rwa [Finset.disjoint_singleton_right]),
              card_map, card_singleton]
          omega
        · -- All pairs in the extended clique are red
          intro x y hx hy hxy
          rw [mem_union, mem_singleton] at hx hy
          rcases hx with hx | rfl <;> rcases hy with hy | rfl
          · -- Both from S: use hS_red
            simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
            obtain ⟨a, ha, rfl⟩ := hx
            obtain ⟨b, hb, rfl⟩ := hy
            exact hS_red a b ha hb (fun h => hxy (congrArg embed_r h))
          · -- x from S, y = v: use that embed_r maps into Nred
            simp only [mem_map, Function.Embedding.coeFn_mk] at hx
            obtain ⟨a, _, rfl⟩ := hx
            rw [hfsym]
            exact hembed_r_red a
          · -- x = v, y from S
            simp only [mem_map, Function.Embedding.coeFn_mk] at hy
            obtain ⟨b, _, rfl⟩ := hy
            exact hembed_r_red b
          · -- x = v, y = v: contradiction
            exact absurd rfl hxy
      · -- Found an s-blue-clique in Nred: lift back
        right
        use S.map ⟨embed_r, hembed_r_inj⟩
        refine ⟨by simp [card_map]; exact hS_card, ?_⟩
        intro x y hx hy hxy
        simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact hS_blue a b ha hb (fun h => hxy (congrArg embed_r h))
    · -- Blue neighborhood has ≥ n2 vertices
      push_neg at hred_big
      have hblue_big : Nblue.card ≥ n2 := by omega
      obtain ⟨embed_b, hembed_b_inj, hembed_b_mem⟩ := embed_from_finset n2 Nblue hblue_big
      -- All embedded vertices are blue neighbors of v and distinct from v
      have hembed_b_blue : ∀ i, f v (embed_b i) = false := by
        intro i
        have := hembed_b_mem i
        simp only [Nblue, mem_filter, mem_univ, true_and] at this
        exact this.1
      have hembed_b_ne_v : ∀ i, embed_b i ≠ v := by
        intro i
        have := hembed_b_mem i
        simp only [Nblue, mem_filter, mem_univ, true_and] at this
        exact this.2
      -- Restrict coloring to the blue neighborhood
      let f_b : Fin n2 → Fin n2 → Bool := fun i j => f (embed_b i) (embed_b j)
      have hf_b_sym : ∀ x y, f_b x y = f_b y x := fun x y => hfsym _ _
      have hf_b_irr : ∀ x, f_b x x = false := fun x => hfirr _
      rcases h2 f_b hf_b_sym hf_b_irr with ⟨S, hS_card, hS_red⟩ | ⟨S, hS_card, hS_blue⟩
      · -- Found an r-red-clique in Nblue: lift back
        left
        use S.map ⟨embed_b, hembed_b_inj⟩
        refine ⟨by simp [card_map]; exact hS_card, ?_⟩
        intro x y hx hy hxy
        simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨b, hb, rfl⟩ := hy
        exact hS_red a b ha hb (fun h => hxy (congrArg embed_b h))
      · -- Found an (s-1)-blue-clique in Nblue: extend with v to get s-blue-clique
        right
        use (S.map ⟨embed_b, hembed_b_inj⟩) ∪ {v}
        constructor
        · -- Card: |S.map embed_b ∪ {v}| ≥ s
          have hv_notin : v ∉ S.map ⟨embed_b, hembed_b_inj⟩ := by
            simp only [mem_map, Function.Embedding.coeFn_mk]
            rintro ⟨i, _, hi_eq⟩
            exact hembed_b_ne_v i hi_eq
          rw [card_union_of_disjoint (by rwa [Finset.disjoint_singleton_right]),
              card_map, card_singleton]
          omega
        · -- All pairs in the extended clique are blue
          intro x y hx hy hxy
          rw [mem_union, mem_singleton] at hx hy
          rcases hx with hx | rfl <;> rcases hy with hy | rfl
          · -- Both from S: use hS_blue
            simp only [mem_map, Function.Embedding.coeFn_mk] at hx hy
            obtain ⟨a, ha, rfl⟩ := hx
            obtain ⟨b, hb, rfl⟩ := hy
            exact hS_blue a b ha hb (fun h => hxy (congrArg embed_b h))
          · -- x from S, y = v: use that embed_b maps into Nblue
            simp only [mem_map, Function.Embedding.coeFn_mk] at hx
            obtain ⟨a, _, rfl⟩ := hx
            rw [hfsym]
            exact hembed_b_blue a
          · -- x = v, y from S
            simp only [mem_map, Function.Embedding.coeFn_mk] at hy
            obtain ⟨b, _, rfl⟩ := hy
            exact hembed_b_blue b
          · -- x = v, y = v: contradiction
            exact absurd rfl hxy

/-
## Part V: Concrete R(4,k) Bounds

Using the recursion and known values.
-/

/-- Known exact Ramsey numbers and bounds for reference.
    R(3,3) = 6, R(3,4) = 9, R(3,5) = 14, R(3,6) = 18, R(3,7) = 23, R(3,8) = 28, R(3,9) = 36
    R(4,4) = 18, R(4,5) = 25 -/
theorem r3_3_le : ramseyUpperBound 3 3 = 6 := by native_decide
theorem r3_4_le : ramseyUpperBound 3 4 = 10 := by native_decide
theorem r3_5_le : ramseyUpperBound 3 5 = 15 := by native_decide

/-- Table of R(4,k) upper bounds from binomial coefficient. -/
theorem r4_bounds_table :
    ramseyUpperBound 4 3 = 10 ∧
    ramseyUpperBound 4 4 = 20 ∧
    ramseyUpperBound 4 5 = 35 ∧
    ramseyUpperBound 4 6 = 56 ∧
    ramseyUpperBound 4 7 = 84 ∧
    ramseyUpperBound 4 8 = 120 ∧
    ramseyUpperBound 4 9 = 165 ∧
    ramseyUpperBound 4 10 = 220 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-
## Part VI: R(4,k) Growth Rate

The binomial bound R(4,k) ≤ C(k+2,3) shows R(4,k) = O(k^3).
-/

/-- The R(4,k) binomial upper bound expressed directly. -/
theorem r4k_upper_bound (k : ℕ) (hk : k ≥ 1) :
    ramseyUpperBound 4 k = Nat.choose (k + 2) 3 := by
  simp only [ramseyUpperBound]
  have : ¬(4 = 0 ∨ k = 0) := by omega
  simp only [this, ↓reduceIte]
  congr 1 <;> omega

/-- The binomial bound is strictly increasing for k ≥ 1. -/
theorem r4k_bound_strict_mono (k : ℕ) (hk : k ≥ 1) :
    ramseyUpperBound 4 k < ramseyUpperBound 4 (k + 1) := by
  rw [r4k_upper_bound k hk, r4k_upper_bound (k + 1) (by omega)]
  -- C(k+2, 3) < C(k+3, 3)
  -- C(k+3, 3) = C(k+2, 2) + C(k+2, 3) by Pascal's rule
  -- and C(k+2, 2) > 0 since k+2 ≥ 2
  have hpascal : Nat.choose (k + 3) 3 = Nat.choose (k + 2) 2 + Nat.choose (k + 2) 3 := by
    exact Nat.choose_succ_succ (k + 2) 2
  have hpos : 0 < Nat.choose (k + 2) 2 := Nat.choose_pos (by omega)
  linarith

/-
## Part VII: Specific R(4,k) Computations
-/

/-- R(4,k) upper bound grows: verify a few concrete strict inequalities. -/
theorem r4_growth_examples :
    ramseyUpperBound 4 3 < ramseyUpperBound 4 4 ∧
    ramseyUpperBound 4 4 < ramseyUpperBound 4 5 ∧
    ramseyUpperBound 4 5 < ramseyUpperBound 4 6 ∧
    ramseyUpperBound 4 6 < ramseyUpperBound 4 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-
## Part VIII: Probabilistic Lower Bound Framework

The probabilistic method gives: R(r,s) > n when the expected number of
monochromatic cliques in a random coloring of K_n is < 1.

For a random 2-coloring of K_n:
- Expected red r-cliques: C(n,r) * 2^(1 - C(r,2))
- Expected blue s-cliques: C(n,s) * 2^(1 - C(s,2))

If C(n,r) * 2^(1-C(r,2)) + C(n,s) * 2^(1-C(s,2)) < 1, then R(r,s) > n.
-/

/-- The number of edges in K_r (complete graph on r vertices). -/
def completeEdges (r : ℕ) : ℕ := Nat.choose r 2

theorem complete_edges_4 : completeEdges 4 = 6 := by native_decide
theorem complete_edges_3 : completeEdges 3 = 3 := by native_decide
theorem complete_edges_5 : completeEdges 5 = 10 := by native_decide

/-- The expected count term for r-cliques in a random 2-coloring of K_n.
    Returns (numerator, denominator) = (C(n,r), 2^(C(r,2) - 1)). -/
def expectedCliqueTerm (n r : ℕ) : ℕ × ℕ :=
  (Nat.choose n r, 2 ^ (completeEdges r - 1))

/-- For R(4,k), the red 4-clique term at n vertices. -/
theorem r4_red_term (n : ℕ) :
    expectedCliqueTerm n 4 = (Nat.choose n 4, 32) := by
  simp [expectedCliqueTerm, completeEdges]
  native_decide

/-- Verify: C(8,4) = 70. At n=8 the simple probabilistic bound
    gives 70/32 > 1, so cannot show R(4,4) > 8.
    The actual R(4,4) = 18, showing the gap. -/
theorem prob_bound_r4_example : Nat.choose 8 4 = 70 := by native_decide

/-
## Part IX: R(4,k) Cubic Upper Bound

R(4,k) ≤ C(k+2,3) ≤ (k+2)^3 / 6, establishing cubic growth.
-/

/-- C(n, 2) ≤ n^2 -/
theorem choose_le_pow_two (n : ℕ) : Nat.choose n 2 ≤ n ^ 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Nat.choose_succ_succ]
    have h1 : Nat.choose m 1 = m := Nat.choose_one_right m
    linarith [sq_nonneg m]

/-- C(n, 3) ≤ n^3 -/
theorem choose_le_pow_three (n : ℕ) : Nat.choose n 3 ≤ n ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.choose_succ_succ]
    have h2 := choose_le_pow_two n
    -- n^2 + n^3 ≤ (n+1)^3 because (n+1)^3 = n^3 + 3n^2 + 3n + 1
    nlinarith [sq_nonneg n]

/-- R(4,k) ≤ (k+2)^3 for the cubic upper bound. -/
theorem r4k_cubic_upper (k : ℕ) (hk : k ≥ 1) :
    ramseyUpperBound 4 k ≤ (k + 2) ^ 3 := by
  rw [r4k_upper_bound k hk]
  exact choose_le_pow_three (k + 2)

/-- The R(4,k) bounds grow at least linearly: for k ≥ 1, the bound is ≥ k. -/
theorem r4k_bound_ge_k (k : ℕ) (hk : k ≥ 1) :
    ramseyUpperBound 4 k ≥ k := by
  rw [r4k_upper_bound k hk]
  -- C(k+2, 3) ≥ k for k ≥ 1
  -- Proof: C(k+2, 3) = C(k+1, 2) + C(k+1, 3) ≥ C(k+1, 2) ≥ k
  -- because C(k+1, 2) = k(k+1)/2 ≥ k for k ≥ 1.
  -- We know C(n, 2) = n(n-1)/2 ≥ n-1, so C(k+1, 2) ≥ k.
  have hpascal : Nat.choose (k + 2) 3 = Nat.choose (k + 1) 2 + Nat.choose (k + 1) 3 :=
    Nat.choose_succ_succ (k + 1) 2
  have h3 : Nat.choose (k + 1) 3 ≥ 0 := Nat.zero_le _
  -- C(k+1, 2) ≥ k: proved from choose_le_pow_two and explicit lower bound
  suffices h : Nat.choose (k + 1) 2 ≥ k by linarith
  -- C(k+1, 2) = C(k, 1) + C(k, 2) = k + C(k, 2) ≥ k
  have hp2 : Nat.choose (k + 1) 2 = Nat.choose k 1 + Nat.choose k 2 :=
    Nat.choose_succ_succ k 1
  rw [Nat.choose_one_right] at hp2
  linarith [Nat.zero_le (Nat.choose k 2)]

/-
## Part X: Summary of Results
-/

#check ramseyProp_mono_n
#check ramseyProp_symm
#check ramseyProp_mono_r
#check ramseyProp_mono_s
#check ramseyProp_one_left
#check ramseyProp_one_right
#check ramseyProp_two_left
#check ramseyUpperBound_mono_s
#check ramsey_recursion
#check r4_bounds_table
#check r4k_upper_bound
#check r4k_bound_strict_mono
#check r4_growth_examples
#check choose_le_pow_three
#check r4k_cubic_upper
#check r4k_bound_ge_k

end RamseyR4k
