import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

/-
# Erdős Problem #1022: Property B and Sparse Set Families

## Problem Statement

Is there a function c(t) → ∞ (as t → ∞) such that every family F of sets,
each of size ≥ t, satisfying the sparsity condition
  "for every finite set X, at most c(t)·|X| members of F are subsets of X"
has **Property B** (i.e., admits a 2-coloring where no set in F is monochromatic)?

## Known Results

- c(2) = 1 works (Lovász, 1968): if every edge has ≥ 2 elements and
  every vertex appears in ≤ |V| hyperedges, then Property B holds.
- Property B is equivalent to 2-colorability of hypergraphs.
- For uniform hypergraphs of size t, Erdős (1963) showed random 2-coloring
  works when the number of edges is < 2^{t-1}.

## Formalization

We formalize Property B for finite set families on a finite ground set,
state the conjecture, and prove basic structural results.

Reference: https://erdosproblems.com/1022
-/

open Finset

namespace Erdos1022

variable {α : Type*} [DecidableEq α]

-- ══════════════════════════════════════════════════════════════════
-- § 1: Property B (2-Colorability)
-- ══════════════════════════════════════════════════════════════════

/-- A family F of sets has **Property B** if there exists a 2-coloring of the
    ground set such that no member of F is monochromatic.
    Equivalently: ∃ S such that every F_i intersects both S and its complement. -/
def HasPropertyB [Fintype α] (F : Finset (Finset α)) : Prop :=
  ∃ S : Finset α, ∀ f ∈ F, (f ∩ S).Nonempty ∧ (f \ S).Nonempty

/-- The empty family trivially has Property B. -/
theorem hasPropertyB_empty [Fintype α] : HasPropertyB (∅ : Finset (Finset α)) :=
  ⟨∅, fun f hf => absurd hf (Finset.not_mem_empty f)⟩

/-- Property B is monotone: subsets of Property B families have Property B. -/
theorem hasPropertyB_subset [Fintype α] {F G : Finset (Finset α)}
    (hFG : F ⊆ G) (hG : HasPropertyB G) : HasPropertyB F :=
  let ⟨S, hS⟩ := hG; ⟨S, fun f hf => hS f (hFG hf)⟩

-- ══════════════════════════════════════════════════════════════════
-- § 2: Definitions
-- ══════════════════════════════════════════════════════════════════

/-- Every member of F has cardinality at least t. -/
def AllSizeAtLeast (F : Finset (Finset α)) (t : ℕ) : Prop :=
  ∀ f ∈ F, t ≤ f.card

/-- The sparsity condition: for every subset X of the ground set,
    the number of members of F contained in X is at most c · |X|. -/
def IsSparse [Fintype α] (F : Finset (Finset α)) (c : ℕ) : Prop :=
  ∀ X : Finset α, (F.filter (· ⊆ X)).card ≤ c * X.card

-- ══════════════════════════════════════════════════════════════════
-- § 3: The Conjecture
-- ══════════════════════════════════════════════════════════════════

/-- **Erdős Problem #1022** (OPEN): There exists a function c : ℕ → ℕ
    tending to infinity such that every c(t)-sparse family of sets of
    size ≥ t has Property B. -/
axiom erdos_1022_conjecture :
  ∃ c : ℕ → ℕ,
    (∀ M : ℕ, ∃ t₀ : ℕ, ∀ t : ℕ, t ≥ t₀ → c t ≥ M) ∧
    (∀ (α : Type) [DecidableEq α] [Fintype α] (F : Finset (Finset α)) (t : ℕ),
      AllSizeAtLeast F t → IsSparse F (c t) → HasPropertyB F)

-- ══════════════════════════════════════════════════════════════════
-- § 4: Sparsity Properties
-- ══════════════════════════════════════════════════════════════════

/-- 0-sparse families have only empty sets as members. -/
theorem sparse_zero_forces_empty [Fintype α] (F : Finset (Finset α))
    (hF : IsSparse F 0) (f : Finset α) (hf : f ∈ F) : f = ∅ := by
  by_contra hne
  have : f ∈ F.filter (· ⊆ f) := Finset.mem_filter.mpr ⟨hf, Finset.Subset.refl f⟩
  have hb := hF f
  simp only [Nat.zero_mul] at hb
  exact absurd (Finset.card_pos.mpr ⟨f, this⟩) (by omega)

/-- A family of sets of size ≥ 1 cannot be 0-sparse (unless empty). -/
theorem not_sparse_zero_of_nonempty_member [Fintype α] (F : Finset (Finset α))
    (hF : ∃ f ∈ F, f.Nonempty) : ¬IsSparse F 0 := by
  intro h0
  obtain ⟨f, hf, hne⟩ := hF
  exact absurd (sparse_zero_forces_empty F h0 f hf) (Finset.nonempty_iff_ne_empty.mp hne)

/-- Sparsity is monotone: if F is c-sparse, it is also (c + d)-sparse. -/
theorem isSparse_mono [Fintype α] {F : Finset (Finset α)} {c d : ℕ}
    (hF : IsSparse F c) : IsSparse F (c + d) := by
  intro X
  calc (F.filter (· ⊆ X)).card ≤ c * X.card := hF X
    _ ≤ (c + d) * X.card := Nat.mul_le_mul_right X.card (Nat.le_add_right c d)

/-- A subfamily of a c-sparse family is also c-sparse. -/
theorem isSparse_subset [Fintype α] {F G : Finset (Finset α)} {c : ℕ}
    (hFG : F ⊆ G) (hG : IsSparse G c) : IsSparse F c := by
  intro X
  calc (F.filter (· ⊆ X)).card
      ≤ (G.filter (· ⊆ X)).card := Finset.card_le_card (Finset.filter_subset_filter _ hFG)
    _ ≤ c * X.card := hG X

/-- AllSizeAtLeast is monotone downward in t. -/
theorem allSizeAtLeast_mono {F : Finset (Finset α)} {s t : ℕ}
    (hst : s ≤ t) (hF : AllSizeAtLeast F t) : AllSizeAtLeast F s :=
  fun f hf => le_trans hst (hF f hf)

/-- A subfamily of a family with minimum size t also has minimum size t. -/
theorem allSizeAtLeast_subset {F G : Finset (Finset α)} {t : ℕ}
    (hFG : F ⊆ G) (hG : AllSizeAtLeast G t) : AllSizeAtLeast F t :=
  fun f hf => hG f (hFG hf)

-- ══════════════════════════════════════════════════════════════════
-- § 5: Property B for Small Families
-- ══════════════════════════════════════════════════════════════════

/-- Any single set of size ≥ 2 has Property B: split using any element. -/
theorem hasPropertyB_singleton [Fintype α] {f : Finset α} (hf : 2 ≤ f.card) :
    HasPropertyB ({f} : Finset (Finset α)) := by
  -- f has ≥ 2 elements, pick a ∈ f
  have hpos : 0 < f.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  -- f \ {a} is nonempty since |f| ≥ 2
  have hera : (f.erase a).card = f.card - 1 := Finset.card_erase_of_mem ha
  have hpos2 : 0 < (f.erase a).card := by omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp hpos2
  have hbf : b ∈ f := Finset.mem_of_mem_erase hb
  have hba : b ≠ a := Finset.ne_of_mem_erase hb
  -- Use S = {a} as the color class
  refine ⟨{a}, fun g hg => ?_⟩
  rw [Finset.mem_singleton] at hg; subst hg
  exact ⟨⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_singleton.mpr rfl⟩⟩,
         ⟨b, Finset.mem_sdiff.mpr ⟨hbf, fun hmem =>
           hba (Finset.mem_singleton.mp hmem)⟩⟩⟩

-- ══════════════════════════════════════════════════════════════════
-- § 6: Counting Lemmas
-- ══════════════════════════════════════════════════════════════════

/-- The number of members of F that are subsets of X is bounded by |F|. -/
theorem filter_subset_card_le [Fintype α] (F : Finset (Finset α)) (X : Finset α) :
    (F.filter (· ⊆ X)).card ≤ F.card :=
  Finset.card_filter_le F _

/-- A c-sparse family satisfies |F| ≤ c · |U| when U contains all members. -/
theorem sparse_family_size_bound [Fintype α] (F : Finset (Finset α)) (c : ℕ)
    (hsp : IsSparse F c) (U : Finset α) (hU : ∀ f ∈ F, f ⊆ U) :
    F.card ≤ c * U.card := by
  have hfilt : F.filter (· ⊆ U) = F := by
    ext f; simp only [Finset.mem_filter]
    exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, hU f h⟩⟩
  calc F.card = (F.filter (· ⊆ U)).card := by rw [hfilt]
    _ ≤ c * U.card := hsp U

-- ══════════════════════════════════════════════════════════════════
-- § 7: Sparsity and Empty Set
-- ══════════════════════════════════════════════════════════════════

/-- c-sparsity implies ∅ ∉ F (since the filter at ∅ has cardinality
    ≤ c · 0 = 0, but ∅ ⊆ ∅ would add an element). -/
theorem sparse_no_empty_member [Fintype α] (F : Finset (Finset α)) (c : ℕ)
    (hsp : IsSparse F c) : ∅ ∉ F := by
  intro hem
  have hmem : ∅ ∈ F.filter (· ⊆ (∅ : Finset α)) :=
    Finset.mem_filter.mpr ⟨hem, Finset.empty_subset _⟩
  have hle := hsp ∅
  simp only [Finset.card_empty, Nat.mul_zero] at hle
  exact absurd (Finset.card_pos.mpr ⟨∅, hmem⟩) (by omega)

/-- A family with min size ≥ 1 contains no empty sets. -/
theorem allSizeAtLeast_no_empty {F : Finset (Finset α)} {t : ℕ} (ht : 1 ≤ t)
    (hF : AllSizeAtLeast F t) : ∅ ∉ F := by
  intro hem
  have := hF ∅ hem
  simp at this
  omega

-- ══════════════════════════════════════════════════════════════════
-- § 8: Monotonicity of Filter Counts
-- ══════════════════════════════════════════════════════════════════

/-- If X ⊆ Y, then the number of family members inside X
    is at most the number inside Y. -/
theorem filter_subset_mono [Fintype α] (F : Finset (Finset α))
    {X Y : Finset α} (hXY : X ⊆ Y) :
    (F.filter (· ⊆ X)).card ≤ (F.filter (· ⊆ Y)).card := by
  apply Finset.card_le_card
  intro f hf
  rw [Finset.mem_filter] at hf ⊢
  exact ⟨hf.1, Finset.Subset.trans hf.2 hXY⟩

/-- Adding an element to the ground set can only increase the subset count. -/
theorem filter_subset_insert_le [Fintype α] (F : Finset (Finset α))
    (X : Finset α) (a : α) :
    (F.filter (· ⊆ X)).card ≤ (F.filter (· ⊆ insert a X)).card :=
  filter_subset_mono F (Finset.subset_insert a X)

end Erdos1022
