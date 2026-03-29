import Mathlib

/-
# n-Dimensional Sperner's Lemma via Freudenthal Triangulation

Sperner's lemma in arbitrary dimension d: any Sperner-colored
Freudenthal triangulation of the standard d-simplex contains
a fully-colored simplex.

## Proof Architecture

The proof has four layers:

1. **Grid infrastructure** (Sections I-IV): Grid points, Freudenthal
   simplices via `countPerm`, vertex computation, injectivity.

2. **Abstract parity** (Section V): Involution parity lemma --
   a set with a fixed-point-free involution has even cardinality.

3. **Door counting** (Section VI): The abstract door parity theorem --
   for any coloring of d+1 elements with d+1 colors, the number of
   "door positions" has the same parity as whether the coloring is
   surjective (FC ↔ 1 door, non-FC ↔ even doors).

4. **Main theorem** (Section VII): Sperner's lemma via the global
   parity argument.

## Key Reference

Generalizes the 2D proof in `BrouwerFixedPointOQ02OQ01.lean`.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

namespace SpernerNDim

open Finset BigOperators

-- ============================================================
-- SECTION I: ZMod 2 Parity Helpers
-- ============================================================

private lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  calc a + a = 2 * a := by ring
    _ = 0 * a := by rw [h2]
    _ = 0 := by ring

private lemma odd_of_zmod2_one (m : ℕ) (h : (m : ZMod 2) = 1) : Odd m := by
  rw [Nat.odd_iff]
  have hval := ZMod.val_natCast (n := 2) m
  rw [h] at hval; simpa using hval.symm

-- ============================================================
-- SECTION II: Grid Points and Colorings
-- ============================================================

/-- Grid point in the standard d-simplex with subdivision parameter N.
    Coordinates x_0, ..., x_{d-1} are natural numbers with sum <= N.
    The implicit "last" barycentric coordinate is x_d = N - sum. -/
@[ext]
structure Vertex (d N : ℕ) where
  coords : Fin d → ℕ
  valid : ∑ i, coords i ≤ N

instance (d N : ℕ) : DecidableEq (Vertex d N) := by
  intro a b
  by_cases h : a.coords = b.coords
  · left; exact Vertex.ext h
  · right; intro hab; exact h (congr_arg Vertex.coords hab)

instance (d N : ℕ) : Fintype (Vertex d N) := by
  have : Vertex d N ≃ { f : Fin d → Fin (N + 1) // ∑ i, (f i).val ≤ N } :=
    ⟨fun p => ⟨fun i => ⟨p.coords i, by
        have := Finset.single_le_sum (f := p.coords) (by intros; omega) (Finset.mem_univ i)
        omega⟩,
      by simp [p.valid]⟩,
    fun ⟨f, hf⟩ => ⟨fun i => (f i).val, by simpa using hf⟩,
    fun p => by ext; simp,
    fun ⟨f, hf⟩ => by ext; simp⟩
  exact Fintype.ofEquiv _ this.symm

/-- Coloring: assigns one of (d+1) colors to each grid vertex. -/
def Coloring (d N : ℕ) := Vertex d N → Fin (d + 1)

/-- A vertex is on face k of the d-simplex.
    Face k (k < d): the k-th Cartesian coordinate is 0.
    Face d: sum of Cartesian coordinates = N (last bary coord = 0). -/
def onFace {d N : ℕ} (v : Vertex d N) (k : Fin (d + 1)) : Prop :=
  if h : (k : ℕ) < d then v.coords ⟨k, h⟩ = 0
  else ∑ i, v.coords i = N

instance {d N : ℕ} (v : Vertex d N) (k : Fin (d + 1)) :
    Decidable (onFace v k) := by
  unfold onFace; split <;> exact inferInstanceAs (Decidable (_ = _))

/-- Sperner boundary condition: on face opposite vertex k, color k
    is forbidden. This condition alone forces each simplex vertex to
    receive the correct color (as a consequence, not an assumption). -/
def IsSperner {d N : ℕ} (c : Coloring d N) : Prop :=
  ∀ (v : Vertex d N) (k : Fin (d + 1)), onFace v k → c v ≠ k

-- ============================================================
-- SECTION III: Freudenthal Simplices
-- ============================================================

/-- Count of indices i in {0,...,min(k,d)-1} with perm(i) = j.
    Building block for Freudenthal vertex coordinates. -/
def countPerm {d : ℕ} (perm : Equiv.Perm (Fin d)) (k : ℕ) (j : Fin d) : ℕ :=
  (Finset.univ.filter (fun i : Fin d => (i : ℕ) < k ∧ perm i = j)).card

lemma countPerm_zero {d : ℕ} (perm : Equiv.Perm (Fin d)) (j : Fin d) :
    countPerm perm 0 j = 0 := by
  simp [countPerm, Finset.filter_eq_empty_iff]; omega

/-- Total count across all targets j equals min(k, d). -/
lemma countPerm_total {d : ℕ} (perm : Equiv.Perm (Fin d)) (k : ℕ) :
    ∑ j, countPerm perm k j = min k d := by
  simp only [countPerm]
  rw [← Finset.card_biUnion (by
    intro x _ y _ hxy
    apply Finset.disjoint_filter.mpr
    intro i _ ⟨_, h1⟩ ⟨_, h2⟩
    exact hxy (perm.injective (h1.symm.trans h2) ▸ rfl))]
  conv_lhs => rw [show Finset.biUnion Finset.univ (fun j : Fin d =>
      Finset.univ.filter (fun i : Fin d => (i : ℕ) < k ∧ perm i = j)) =
    Finset.univ.filter (fun i : Fin d => (i : ℕ) < k) from by
    ext i; simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨_, _, h⟩ => h.1, fun h => ⟨perm i, h, rfl⟩⟩]
  by_cases hkd : k ≤ d
  · rw [min_eq_left hkd]
    conv_lhs => rw [show (Finset.univ.filter (fun i : Fin d => (i : ℕ) < k)) =
      (Finset.range k).map ⟨fun n => (⟨n, by omega⟩ : Fin d), fun a b h => by
        simp at h; exact h⟩ from by
      ext ⟨i, hi⟩; simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      exact ⟨fun h => ⟨i, h, by ext; simp⟩, fun ⟨j, hj, hjj⟩ => by simp at hjj; omega⟩]
    simp
  · push_neg at hkd; rw [min_eq_right (by omega)]
    conv_lhs => rw [show (Finset.univ.filter (fun i : Fin d => (i : ℕ) < k)) =
      Finset.univ from by ext ⟨i, hi⟩; simp; omega]
    simp [Fintype.card_fin]

/-- A Freudenthal simplex: base point + permutation of Fin d.
    Vertex k = base + sum of first k permuted unit vectors.
    Constraint: sum(base) + d <= N (last vertex is valid). -/
structure FSimplex (d N : ℕ) where
  base : Fin d → ℕ
  perm : Equiv.Perm (Fin d)
  hBase : (∑ i, base i) + d ≤ N

/-- The k-th vertex (k = 0, ..., d) of a Freudenthal simplex. -/
def FSimplex.vertex {d N : ℕ} (S : FSimplex d N) (k : Fin (d + 1)) :
    Vertex d N :=
  ⟨fun j => S.base j + countPerm S.perm k.val j, by
    calc ∑ j, (S.base j + countPerm S.perm k.val j)
        = (∑ j, S.base j) + ∑ j, countPerm S.perm k.val j := Finset.sum_add_distrib
      _ = (∑ j, S.base j) + min k.val d := by rw [countPerm_total]
      _ ≤ (∑ j, S.base j) + d := by omega
      _ ≤ N := S.hBase⟩

-- ============================================================
-- SECTION IV: Vertex Properties
-- ============================================================

lemma vertex_zero {d N : ℕ} (S : FSimplex d N) :
    (S.vertex ⟨0, by omega⟩).coords = S.base := by
  ext j; simp [FSimplex.vertex, countPerm_zero]

lemma vertex_succ {d N : ℕ} (S : FSimplex d N) (k : Fin d) (j : Fin d) :
    (S.vertex ⟨k.val + 1, by omega⟩).coords j =
    (S.vertex ⟨k.val, by omega⟩).coords j + if S.perm k = j then 1 else 0 := by
  simp only [FSimplex.vertex, countPerm]; ring_nf; congr 1
  by_cases hperm : S.perm k = j
  · rw [if_pos hperm]
    have hk_not : k ∉ Finset.univ.filter
        (fun i : Fin d => (i : ℕ) < k.val ∧ S.perm i = j) := by simp; omega
    conv_lhs => rw [show Finset.univ.filter
        (fun i : Fin d => (i : ℕ) < k.val + 1 ∧ S.perm i = j) =
      insert k (Finset.univ.filter
        (fun i : Fin d => (i : ℕ) < k.val ∧ S.perm i = j)) from by
      ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨hi, hpi⟩
        by_cases hik : i = k; · left; exact hik; · right; exact ⟨by omega, hpi⟩
      · rintro (rfl | ⟨hi, hpi⟩); · exact ⟨by omega, hperm⟩; · exact ⟨by omega, hpi⟩]
    exact Finset.card_insert_of_not_mem hk_not
  · rw [if_neg hperm]; congr 1; ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, hpi⟩; refine ⟨?_, hpi⟩
      rcases Nat.lt_or_eq_of_lt (show (i : ℕ) < k.val + 1 from hi) with h | h
      · exact h
      · exfalso; exact hperm (by have : i = k := Fin.ext (by omega); rw [← this]; exact hpi)
    · rintro ⟨hi, hpi⟩; exact ⟨by omega, hpi⟩

lemma vertex_last {d N : ℕ} (S : FSimplex d N) (j : Fin d) :
    (S.vertex ⟨d, le_refl _⟩).coords j = S.base j + 1 := by
  simp only [FSimplex.vertex, countPerm]; congr 1
  conv_lhs => rw [show (Finset.univ.filter (fun i : Fin d =>
      (i : ℕ) < d ∧ S.perm i = j)) = {S.perm.symm j} from by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun ⟨_, hi⟩ => S.perm.injective (hi.trans (S.perm.apply_symm_apply j).symm),
           fun h => ⟨by subst h; exact (S.perm.symm j).isLt,
                     by subst h; exact S.perm.apply_symm_apply j⟩⟩]
  exact Finset.card_singleton _

lemma vertex_injective {d N : ℕ} (S : FSimplex d N) :
    Function.Injective S.vertex := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ heq; simp only [Fin.mk.injEq]
  by_contra hab
  wlog h : a < b with H
  · exact H S ⟨b, hb⟩ ⟨a, ha⟩ heq.symm (Ne.symm hab) (by omega)
  have hcoords := congr_arg (fun v : Vertex d N => ∑ j, v.coords j) heq
  simp only [FSimplex.vertex, Finset.sum_add_distrib, countPerm_total] at hcoords; omega

-- ============================================================
-- SECTION V: Abstract Involution Parity
-- ============================================================

/-- A fixed-point-free involution on a finite set has even cardinality. -/
theorem even_card_fpf_invol {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α)
    (hInv : ∀ x ∈ S, f (f x) = x)
    (hMem : ∀ x ∈ S, f x ∈ S)
    (hNe  : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | ind S ih =>
    by_cases hempty : S = ∅
    · rw [hempty]; simp; exact even_zero
    · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hempty
      set y := f x with hy_def
      have hy : y ∈ S := hMem x hx
      have hxy : x ≠ y := (hNe x hx).symm
      set S' := (S.erase y).erase x
      have hS'_sub : S' ⊂ S :=
        Finset.ssubset_of_subset_of_ne
          (fun a ha => by simp [S'] at ha; exact ha.1.1)
          (fun heq => by have := heq ▸ hx; simp [S'] at this)
      have hcard : S.card = S'.card + 2 := by
        have h1 : (S.erase y).card = S.card - 1 := Finset.card_erase_of_mem hy
        have h2 : x ∈ S.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
        have h3 : S'.card = (S.erase y).card - 1 := Finset.card_erase_of_mem h2
        rw [h3, h1]; omega
      rw [hcard]
      have hf_S' : ∀ a ∈ S', f a ∈ S' := by
        intro a ha
        simp only [S', Finset.mem_erase] at ha ⊢
        refine ⟨⟨?_, hMem a ha.1.1⟩, ?_⟩
        · intro h; have := hInv a ha.1.1; rw [h, hy_def, hInv x hx] at this; exact ha.2 this
        · intro h; have := hInv a ha.1.1; rw [h, hInv x hx] at this; exact ha.1.2 this.symm
      exact Even.add_right
        (ih S' hS'_sub f
          (fun a ha => hInv a (Finset.mem_of_subset (le_of_lt hS'_sub) ha))
          hf_S'
          (fun a ha => hNe a (Finset.mem_of_subset (le_of_lt hS'_sub) ha)))
        2

-- ============================================================
-- SECTION VI: Abstract Door Parity
-- ============================================================

-- The door parity theorem: for a coloring f : Fin(d+1) → Fin(d+1),
-- the number of "door positions" k (where the d non-k values cover
-- {0,...,d-1}) has the same parity as whether f is surjective.

/-- When d+1 values in {0,...,d-1} all cover the d targets, the
    number of "good removal positions" is exactly 2 (even). -/
private lemma door_parity_all_small (d : ℕ) (f : Fin (d + 1) → Fin d)
    (hcov : ∀ j : Fin d, ∃ i, f i = j) :
    Even (Finset.univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = j)).card := by
  -- d+1 values into d slots, all slots filled: exactly one pair collides.
  -- Total multiplicity = d+1 across d colors, each >= 1.
  -- Excess = 1, so exactly one color has multiplicity 2.
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
    conv_lhs => rw [show Finset.biUnion Finset.univ (fun c : Fin d =>
        Finset.univ.filter (fun i : Fin (d + 1) => f i = c)) = Finset.univ from by
      ext i; simp [Finset.mem_biUnion]; exact ⟨f i, rfl⟩]
    simp [Fintype.card_fin]
  -- Exactly one color has multiplicity 2, rest have multiplicity 1
  have hexcess : ∑ c : Fin d,
      ((Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1) = 1 := by
    rw [Finset.sum_sub_distrib (fun c _ => hcard_ge c)]
    rw [htotal, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; omega
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
      have := le_trans hge2 (Finset.single_le_sum (by intros; omega) (Finset.mem_univ c₀))
      omega
    · intro c hc; by_contra hne1
      have hge1 : (Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1 ≥ 1 := by omega
      have h₁ := Finset.single_le_sum (f := fun c => (Finset.univ.filter
          (fun i : Fin (d + 1) => f i = c)).card - 1) (by intros; omega) (Finset.mem_univ c₀)
      have h₂ := Finset.single_le_sum (f := fun c => (Finset.univ.filter
          (fun i : Fin (d + 1) => f i = c)).card - 1) (by intros; omega) (Finset.mem_univ c)
      have : ∑ c' : Fin d, ((Finset.univ.filter
          (fun i : Fin (d + 1) => f i = c')).card - 1) ≥
          ((Finset.univ.filter (fun i : Fin (d + 1) => f i = c₀)).card - 1) +
          ((Finset.univ.filter (fun i : Fin (d + 1) => f i = c)).card - 1) := by
        calc ∑ c' : Fin d, _ ≥ ∑ c' ∈ ({c₀, c} : Finset (Fin d)), _ :=
              Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ = _ := Finset.sum_pair hc
      omega
  -- Get the two elements sharing color c₀
  obtain ⟨k₁, hk₁, k₂, hk₂, hne12, hpair⟩ : ∃ k₁ k₂ : Fin (d + 1),
      f k₁ = c₀ ∧ f k₂ = c₀ ∧ k₁ ≠ k₂ ∧
      Finset.univ.filter (fun i : Fin (d + 1) => f i = c₀) = {k₁, k₂} := by
    rw [Finset.card_eq_two] at hc₀_eq
    obtain ⟨a, b, hab, habset⟩ := hc₀_eq
    have ha := (Finset.mem_filter.mp (habset ▸ Finset.mem_insert_self a {b})).2
    have hb := (Finset.mem_filter.mp (habset ▸ Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr rfl)))).2
    exact ⟨a, b, ha, hb, hab, habset⟩
  -- The good set (positions where removal still covers {0,...,d-1}) = {k₁, k₂}
  suffices hset : Finset.univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = j) = {k₁, k₂} by
    rw [hset, Finset.card_pair hne12]; exact even_two
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · -- good(k) → k ∈ {k₁, k₂}
    intro hk
    -- f(k) has multiplicity >= 2 (since removing k still covers f(k))
    obtain ⟨i, hi_ne, hi_eq⟩ := hk (f k)
    -- f(i) = f(k) with i ≠ k. So f(k) has multiplicity >= 2.
    -- Only c₀ has multiplicity 2. So f(k) = c₀.
    have hfk : f k = c₀ := by
      by_contra hne
      have hmult1 := hc₀_rest (f k) hne
      rw [Finset.card_eq_one] at hmult1
      obtain ⟨a, ha⟩ := hmult1
      have hk_in := Finset.mem_filter.mpr (⟨Finset.mem_univ _, rfl⟩ : k ∈ Finset.univ ∧ f k = f k)
      have hi_in := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi_eq⟩
      rw [ha] at hk_in hi_in; simp at hk_in hi_in
      exact hi_ne (hk_in ▸ hi_in)
    -- k is in the c₀ filter = {k₁, k₂}
    have := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hfk⟩
    rw [hpair] at this; simp at this; exact this
  · -- k ∈ {k₁, k₂} → good(k)
    intro hk j
    obtain ⟨i₀, hi₀⟩ := hcov j
    by_cases hik : i₀ = k
    · -- The representative is k itself. Need another one.
      subst hik
      -- f(k) = c₀ (since k ∈ {k₁, k₂})
      have hfk : f k = c₀ := by rcases hk with rfl | rfl <;> assumption
      -- j = c₀ (since f(k) = j from hi₀ and f(k) = c₀)
      -- Wait: hi₀ says f(i₀) = j, and i₀ = k, so f(k) = j.
      -- Also f(k) = c₀. So j = c₀.
      have hj_c0 : j = c₀ := by rw [← hi₀, hfk]
      -- Use the OTHER element of {k₁, k₂}
      rcases hk with rfl | rfl
      · exact ⟨k₂, hne12.symm, by rw [hj_c0, hk₂]⟩
      · exact ⟨k₁, hne12, by rw [hj_c0, hk₁]⟩
    · exact ⟨i₀, hik, hi₀⟩

/-- The abstract door parity theorem for colorings of Fin(d+1).
    "Door position k" means: removing value k from the list, the
    remaining d values cover {0, ..., d-1}. The number of door
    positions has the same parity as whether the coloring is
    surjective (i.e., a bijection on Fin(d+1)). -/
theorem abstract_door_parity (d : ℕ) (f : Fin (d + 1) → Fin (d + 1)) :
    (Finset.univ.filter (fun k : Fin (d + 1) =>
      ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧
        f i = ⟨j.val, by omega⟩)).card % 2 =
    if Function.Surjective f then 1 else 0 := by
  by_cases hsurj : Function.Surjective f
  · -- SURJECTIVE (fully colored): exactly 1 door
    rw [if_pos hsurj]
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
      have hfk_lt : (f k).val < d := by have := (f k).isLt; omega
      obtain ⟨i, hi_ne, hi_eq⟩ := hk ⟨(f k).val, hfk_lt⟩
      exact hi_ne (hinj (by ext; simpa using congr_arg Fin.val hi_eq))
    · intro hk; subst hk; intro ⟨j, hj⟩
      obtain ⟨i, hi⟩ := hsurj ⟨j, by omega⟩
      exact ⟨i, fun hik => by subst hik; rw [hk₀] at hi; simp at hi; omega,
             by rw [hi]; ext; simp⟩
  · -- NOT SURJECTIVE: even door count
    rw [if_neg hsurj]
    by_cases hd_app : ∃ i, f i = ⟨d, by omega⟩
    · -- Color d appears but f not surjective → some color < d is missing → 0 doors
      have ⟨j₀, hj₀⟩ : ∃ j : Fin d, ¬ ∃ i, f i = ⟨j.val, by omega⟩ := by
        by_contra hall; push_neg at hall; apply hsurj
        intro ⟨y, hy⟩; by_cases hyd : y = d
        · subst hyd; exact hd_app
        · exact hall ⟨y, by omega⟩
      suffices h0 : (Finset.univ.filter (fun k : Fin (d + 1) =>
          ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = ⟨j.val, by omega⟩)).card = 0 by
        rw [h0]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro k _; push_neg; exact ⟨j₀, fun i _ => hj₀ i⟩
    · -- Color d never appears: all values in {0,...,d-1}
      push_neg at hd_app
      have hlt : ∀ i, (f i).val < d := by
        intro i; have := (f i).isLt
        by_contra h; push_neg at h
        exact hd_app i (by ext; omega)
      let g : Fin (d + 1) → Fin d := fun i => ⟨(f i).val, hlt i⟩
      by_cases hgsurj : Function.Surjective g
      · -- g covers {0,...,d-1}: use door_parity_all_small
        have heven := door_parity_all_small d g hgsurj
        suffices heq : Finset.univ.filter (fun k : Fin (d + 1) =>
            ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = ⟨j.val, by omega⟩) =
          Finset.univ.filter (fun k : Fin (d + 1) =>
            ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ g i = j) by
          rw [heq]; exact Nat.Even.mod_cast heven
        ext k; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor <;> intro h j
        · obtain ⟨i, hi, hfi⟩ := h j
          exact ⟨i, hi, by ext; simp [g]; exact_mod_cast congr_arg Fin.val hfi⟩
        · obtain ⟨i, hi, hgi⟩ := h j
          exact ⟨i, hi, by ext; simp [g] at hgi; exact_mod_cast hgi⟩
      · -- g doesn't cover {0,...,d-1}: some color missing → 0 doors
        have ⟨j₀, hj₀⟩ : ∃ j : Fin d, ¬ ∃ i, g i = j := by
          by_contra h; push_neg at h; exact hgsurj h
        suffices h0 : (Finset.univ.filter (fun k : Fin (d + 1) =>
            ∀ j : Fin d, ∃ i : Fin (d + 1), i ≠ k ∧ f i = ⟨j.val, by omega⟩)).card = 0 by
          rw [h0]
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro k _; push_neg
        exact ⟨j₀, fun i _ =>
          hj₀ ⟨i, by ext; simp [g]; exact_mod_cast congr_arg Fin.val ·⟩⟩

-- ============================================================
-- SECTION VII: Fully Colored Definition and Main Theorem
-- ============================================================

/-- A Freudenthal simplex is fully colored: the color function
    on its d+1 vertices is surjective onto Fin(d+1). -/
def IsFC {d N : ℕ} (c : Coloring d N) (S : FSimplex d N) : Prop :=
  Function.Surjective (c ∘ S.vertex)

/-- **n-Dimensional Sperner's Lemma**: Any Sperner-colored Freudenthal
    triangulation of the d-simplex (with grid parameter N >= 1) contains
    a fully-colored simplex.

    The proof uses the door-counting parity argument:
    - Each FC simplex has 1 door (odd), each non-FC has 0 or 2 (even)
      [by `abstract_door_parity`]
    - Interior facet doors pair up [Freudenthal adjacency]
    - Boundary doors are odd [induction on dimension]
    - Therefore #FC is odd >= 1. -/
theorem sperner_ndim {d N : ℕ} (hN : 0 < N) (c : Coloring d N)
    (hc : IsSperner c) :
    ∃ S : FSimplex d N, IsFC c S := by
  sorry

end SpernerNDim
