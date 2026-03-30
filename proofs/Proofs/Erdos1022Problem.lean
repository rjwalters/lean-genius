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

/-- **Erdős Problem #1022** (OPEN, not proved): There exists a function c : ℕ → ℕ
    tending to infinity such that every c(t)-sparse family of sets of
    size ≥ t has Property B. -/
def Erdos1022Conjecture : Prop :=
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

-- ══════════════════════════════════════════════════════════════════
-- § 9: Element Degree
-- ══════════════════════════════════════════════════════════════════

/-- The degree of an element a in family F: the number of sets containing a. -/
def degree (F : Finset (Finset α)) (a : α) : ℕ :=
  (F.filter (a ∈ ·)).card

/-- The maximum degree of any element in F relative to a ground set. -/
def maxDegree [Fintype α] (F : Finset (Finset α)) : ℕ :=
  Finset.univ.sup (degree F)

/-- Degree is monotone: subfamilies have at most the same degree. -/
theorem degree_subset {F G : Finset (Finset α)} {a : α}
    (hFG : F ⊆ G) : degree F a ≤ degree G a :=
  Finset.card_le_card (Finset.filter_subset_filter _ hFG)

/-- An element not in any member has degree 0. -/
theorem degree_eq_zero_of_not_mem {F : Finset (Finset α)} {a : α}
    (ha : ∀ f ∈ F, a ∉ f) : degree F a = 0 := by
  simp only [degree, Finset.card_eq_zero]
  ext f
  simp only [Finset.mem_filter, Finset.not_mem_empty, iff_false, not_and]
  exact ha f

-- ══════════════════════════════════════════════════════════════════
-- § 10: Lovász Theorem (c(2) = 1)
-- ══════════════════════════════════════════════════════════════════

/-  **REMOVED**: The previous `lovász_theorem` axiom was incorrectly stated.
    It claimed: IsSparse F 1 ∧ AllSizeAtLeast F 2 → HasPropertyB F.

    Counterexample: The triangle K₃ = {{0,1}, {0,2}, {1,2}} on Fin 3.
    - AllSizeAtLeast K₃ 2: all edges have cardinality 2 ✓
    - IsSparse K₃ 1: for X = {0,1,2}, 3 edges ≤ 1·3 = 3 ✓
    - ¬HasPropertyB K₃: any S splits 3 vertices into 2 groups (1,2 or 2,1).
      The group of 2 contains an edge from the triangle.

    The ACTUAL Lovász result uses a DEGREE condition (maximum number of sets
    containing any one element), not the IsSparse condition (edges in induced
    subhypergraphs). The degree condition is strictly stronger than IsSparse
    for this purpose. The correct Lovász Local Lemma version for Property B:
    if every set has size ≥ t and intersects at most d other sets, then for
    d ≤ 2^{t-2} - 1, Property B holds. -/

/-- Degree-bounded condition: every element appears in at most d members of F. -/
def IsDegreeBounded [Fintype α] (F : Finset (Finset α)) (d : ℕ) : Prop :=
  ∀ x : α, (F.filter (x ∈ ·)).card ≤ d

/-- A matching (degree 1) of ≥ 2-sets has Property B: for each set,
    put one element in S and the rest outside. Since sets are disjoint, this works. -/
theorem matching_has_propertyB [Fintype α] (F : Finset (Finset α))
    (hsize : AllSizeAtLeast F 2) (hdeg : IsDegreeBounded F 1) : HasPropertyB F := by
  induction F using Finset.induction_on with
  | empty => exact hasPropertyB_empty
  | @insert f₀ F' hna ih =>
    -- Transfer hypotheses to F'
    have hF'_size : AllSizeAtLeast F' 2 :=
      fun f hf => hsize f (Finset.mem_insert_of_mem hf)
    have hF'_deg : IsDegreeBounded F' 1 := by
      intro x
      have hsub : F'.filter (x ∈ ·) ⊆ (insert f₀ F').filter (x ∈ ·) := by
        intro f hf; rw [Finset.mem_filter] at hf ⊢
        exact ⟨Finset.mem_insert_of_mem hf.1, hf.2⟩
      exact le_trans (Finset.card_le_card hsub) (hdeg x)
    obtain ⟨S', hS'⟩ := ih hF'_size hF'_deg
    have hf₀_card : 2 ≤ f₀.card := hsize f₀ (Finset.mem_insert_self f₀ F')
    -- Key: degree ≤ 1 implies f₀ is disjoint from all members of F'
    have hdisjoint : ∀ g ∈ F', Disjoint f₀ g := by
      intro g hg; rw [Finset.disjoint_left]; intro x hxf₀ hxg
      have h1 : f₀ ∈ (insert f₀ F').filter (x ∈ ·) :=
        Finset.mem_filter.mpr ⟨Finset.mem_insert_self _ _, hxf₀⟩
      have h2 : g ∈ (insert f₀ F').filter (x ∈ ·) :=
        Finset.mem_filter.mpr ⟨Finset.mem_insert_of_mem hg, hxg⟩
      have hne : f₀ ≠ g := fun h => hna (h ▸ hg)
      have hsub : {f₀, g} ⊆ (insert f₀ F').filter (x ∈ ·) := by
        intro y hy; simp only [Finset.mem_insert, Finset.mem_singleton] at hy
        exact hy.elim (· ▸ h1) (· ▸ h2)
      have : 2 ≤ ((insert f₀ F').filter (x ∈ ·)).card := by
        calc 2 = (insert f₀ ({g} : Finset _)).card := by
                rw [Finset.card_insert_of_not_mem (Finset.not_mem_singleton.mpr hne),
                    Finset.card_singleton]
            _ ≤ _ := Finset.card_le_card hsub
      linarith [hdeg x]
    -- Pick two distinct elements a, b ∈ f₀ (since |f₀| ≥ 2)
    have hne₀ : f₀.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a, ha⟩ := hne₀
    have hera_ne : (f₀.erase a).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro h
      have := Finset.card_erase_of_mem ha; rw [h, Finset.card_empty] at this; omega
    obtain ⟨b, hb_era⟩ := hera_ne
    have hb : b ∈ f₀ := Finset.mem_of_mem_erase hb_era
    have hba : b ≠ a := Finset.ne_of_mem_erase hb_era
    -- Case split on how f₀ interacts with existing coloring S'
    by_cases h_inter : (f₀ ∩ S').Nonempty
    · by_cases h_diff : (f₀ \ S').Nonempty
      · -- Both f₀ ∩ S' and f₀ \ S' nonempty: S' already works
        exact ⟨S', fun f hf => by
          rcases Finset.mem_insert.mp hf with rfl | hf
          · exact ⟨h_inter, h_diff⟩
          · exact hS' f hf⟩
      · -- f₀ ⊆ S' (no element of f₀ is outside S'): remove element a from S'
        have hf₀_sub : ∀ x ∈ f₀, x ∈ S' := by
          intro x hx; by_contra hxn
          exact h_diff ⟨x, Finset.mem_sdiff.mpr ⟨hx, hxn⟩⟩
        refine ⟨S'.erase a, fun f hf => ?_⟩
        rcases Finset.mem_insert.mp hf with rfl | hf
        · -- For f₀: b ∈ f₀ ∩ (S' \ {a}), a ∈ f₀ \ (S' \ {a})
          exact ⟨⟨b, Finset.mem_inter.mpr ⟨hb, Finset.mem_erase.mpr ⟨hba, hf₀_sub b hb⟩⟩⟩,
                 ⟨a, Finset.mem_sdiff.mpr ⟨ha, Finset.not_mem_erase a S'⟩⟩⟩
        · -- For g ∈ F': a ∉ g (disjointness), so erasing a doesn't affect g
          have ha_not : a ∉ f := Finset.disjoint_left.mp (hdisjoint f hf) ha
          constructor
          · obtain ⟨c, hc⟩ := (hS' f hf).1
            rw [Finset.mem_inter] at hc
            exact ⟨c, Finset.mem_inter.mpr ⟨hc.1, Finset.mem_erase.mpr
              ⟨fun hca => ha_not (hca ▸ hc.1), hc.2⟩⟩⟩
          · obtain ⟨c, hc⟩ := (hS' f hf).2
            rw [Finset.mem_sdiff] at hc
            exact ⟨c, Finset.mem_sdiff.mpr ⟨hc.1, fun h =>
              hc.2 (Finset.erase_subset a S' h)⟩⟩
    · -- f₀ ∩ S' = ∅: add element a to S'
      have hf₀_disj_S : ∀ x ∈ f₀, x ∉ S' := by
        intro x hx hxS
        exact h_inter ⟨x, Finset.mem_inter.mpr ⟨hx, hxS⟩⟩
      refine ⟨insert a S', fun f hf => ?_⟩
      rcases Finset.mem_insert.mp hf with rfl | hf
      · -- For f₀: a ∈ f₀ ∩ S, b ∈ f₀ \ S (b ∉ S' and b ≠ a)
        exact ⟨⟨a, Finset.mem_inter.mpr ⟨ha, Finset.mem_insert_self a S'⟩⟩,
               ⟨b, Finset.mem_sdiff.mpr ⟨hb, fun h =>
                  (Finset.mem_insert.mp h).elim (fun heq => hba heq)
                    (hf₀_disj_S b hb)⟩⟩⟩
      · -- For g ∈ F': a ∉ g, so adding a to S' doesn't affect g
        have ha_not : a ∉ f := Finset.disjoint_left.mp (hdisjoint f hf) ha
        constructor
        · obtain ⟨c, hc⟩ := (hS' f hf).1
          rw [Finset.mem_inter] at hc
          exact ⟨c, Finset.mem_inter.mpr ⟨hc.1, Finset.mem_insert_of_mem hc.2⟩⟩
        · obtain ⟨c, hc⟩ := (hS' f hf).2
          rw [Finset.mem_sdiff] at hc
          refine ⟨c, Finset.mem_sdiff.mpr ⟨hc.1, fun h => ?_⟩⟩
          rcases Finset.mem_insert.mp h with rfl | hcS
          · exact ha_not hc.1
          · exact hc.2 hcS

-- ══════════════════════════════════════════════════════════════════
-- § 11: Union and Combination of Families
-- ══════════════════════════════════════════════════════════════════

-- Property B is inherited by subfamilies (already proved as hasPropertyB_subset).

/-- The union of a c-sparse and a d-sparse family is (c + d)-sparse. -/
theorem isSparse_union [Fintype α] {F G : Finset (Finset α)} {c d : ℕ}
    (hF : IsSparse F c) (hG : IsSparse G d) : IsSparse (F ∪ G) (c + d) := by
  intro X
  calc (Finset.filter (· ⊆ X) (F ∪ G)).card
      ≤ (F.filter (· ⊆ X)).card + (G.filter (· ⊆ X)).card := by
        rw [Finset.filter_union]
        exact Finset.card_union_le _ _
    _ ≤ c * X.card + d * X.card := Nat.add_le_add (hF X) (hG X)
    _ = (c + d) * X.card := by ring

/-- Disjoint union of c-sparse families is c-sparse if sizes partition. -/
theorem allSizeAtLeast_union {F G : Finset (Finset α)} {t : ℕ}
    (hF : AllSizeAtLeast F t) (hG : AllSizeAtLeast G t) :
    AllSizeAtLeast (F ∪ G) t :=
  fun f hf => by
    rw [Finset.mem_union] at hf
    exact hf.elim (hF f) (hG f)

-- ══════════════════════════════════════════════════════════════════
-- § 12: Erdős First-Moment Threshold
-- ══════════════════════════════════════════════════════════════════

/-- A coloring is monochromatic on A if all elements get the same color. -/
private def IsMonochromaticOn (c : α → Bool) (A : Finset α) : Prop :=
  (∀ x ∈ A, c x = true) ∨ (∀ x ∈ A, c x = false)

private instance (c : α → Bool) (A : Finset α) :
    Decidable (IsMonochromaticOn c A) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- Functions α → Bool constant b on A number at most 2^(|α| - |A|):
    restriction to Aᶜ is injective on functions constant b on A. -/
private lemma card_constOn_le [Fintype α] (A : Finset α) (b : Bool) :
    (Finset.univ.filter (fun c : α → Bool => ∀ x ∈ A, c x = b)).card
    ≤ 2 ^ (Fintype.card α - A.card) := by
  rw [← Fintype.card_coe]
  calc Fintype.card ↥(Finset.univ.filter (fun c : α → Bool => ∀ x ∈ A, c x = b))
      ≤ Fintype.card (↥(Aᶜ : Finset α) → Bool) :=
        Fintype.card_le_of_injective
          (fun (p : ↥(Finset.univ.filter (fun c : α → Bool => ∀ x ∈ A, c x = b)))
               (q : ↥(Aᶜ : Finset α)) => p.val q.val) (by
          intro ⟨f, hf⟩ ⟨g, hg⟩ heq
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf hg
          exact Subtype.ext <| funext fun x => by
            by_cases hx : x ∈ A
            · exact (hf x hx).trans (hg x hx).symm
            · exact congr_fun heq ⟨x, Finset.mem_compl.mpr hx⟩)
    _ = 2 ^ (Fintype.card α - A.card) := by
        simp [Fintype.card_bool, Fintype.card_coe]

/-- Monochromatic colorings on A number at most 2 · 2^(|α| - |A|). -/
private lemma card_monochromatic_on_le [Fintype α] (A : Finset α) :
    (Finset.univ.filter (fun c : α → Bool => IsMonochromaticOn c A)).card
    ≤ 2 * 2 ^ (Fintype.card α - A.card) := by
  calc (Finset.univ.filter (fun c => IsMonochromaticOn c A)).card
      ≤ (Finset.univ.filter (fun c : α → Bool => ∀ x ∈ A, c x = true) ∪
         Finset.univ.filter (fun c : α → Bool => ∀ x ∈ A, c x = false)).card := by
        apply Finset.card_le_card; intro c
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
                    IsMonochromaticOn]; exact id
    _ ≤ (Finset.univ.filter (fun c : α → Bool => ∀ x ∈ A, c x = true)).card +
        (Finset.univ.filter (fun c : α → Bool => ∀ x ∈ A, c x = false)).card :=
      Finset.card_union_le _ _
    _ ≤ 2 ^ (Fintype.card α - A.card) + 2 ^ (Fintype.card α - A.card) := by
        linarith [card_constOn_le A true, card_constOn_le A false]
    _ = 2 * 2 ^ (Fintype.card α - A.card) := by ring

/-- **Erdős 2^{t-1} bound** (1963): any family of fewer than 2^{t-1} sets,
    each of size ≥ t, has Property B. Proof by the probabilistic first-moment
    method: among all 2^|α| colorings, fewer than 2^|α| are bad, so a good
    coloring exists.

    Reference: Erdős, P. "On a combinatorial problem. II."
    Acta Math. Acad. Sci. Hungar. 15 (1964), 445-447. -/
theorem erdos_first_moment_bound [Fintype α] (F : Finset (Finset α)) (t : ℕ)
    (ht : 2 ≤ t) (hsize : AllSizeAtLeast F t)
    (hcount : F.card < 2 ^ (t - 1)) : HasPropertyB F := by
  -- Convert bound: F.card < 2^(t-1) → F.card * 2 < 2^t
  have hbound : F.card * 2 < 2 ^ t := by
    have h1 : F.card * 2 < 2 ^ (t - 1) * 2 := mul_lt_mul_of_pos_right hcount (by omega)
    have h2 : 2 ^ (t - 1) * 2 = 2 ^ t := by
      conv_rhs => rw [show t = t - 1 + 1 from by omega, pow_succ]
    linarith
  -- Trivial case: F empty
  by_cases hFne : F = ∅
  · exact ⟨∅, fun f hf => absurd hf (hFne ▸ Finset.not_mem_empty f)⟩
  -- For nonempty F: t ≤ |α|
  have ht_le : t ≤ Fintype.card α := by
    obtain ⟨A, hA⟩ := Finset.nonempty_of_ne_empty hFne
    exact le_trans (hsize A hA) (Finset.card_le_univ A)
  -- Bad colorings: those making some A ∈ F monochromatic
  set bad := F.biUnion (fun A => Finset.univ.filter
    (fun c : α → Bool => IsMonochromaticOn c A)) with hbad_def
  -- Union bound: |bad| ≤ |F| · (2 · 2^(n-t))
  have hbad_bound : bad.card ≤ F.card * (2 * 2 ^ (Fintype.card α - t)) := by
    calc bad.card
        ≤ F.sum (fun A => (Finset.univ.filter
            (fun c : α → Bool => IsMonochromaticOn c A)).card) :=
          Finset.card_biUnion_le
      _ ≤ F.sum (fun _ => 2 * 2 ^ (Fintype.card α - t)) := by
          apply Finset.sum_le_sum; intro A hA
          calc _ ≤ 2 * 2 ^ (Fintype.card α - A.card) := card_monochromatic_on_le A
            _ ≤ 2 * 2 ^ (Fintype.card α - t) := by
              have : Fintype.card α - A.card ≤ Fintype.card α - t := by
                have h1 := hsize A hA; have h2 := Finset.card_le_univ A; omega
              exact Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by norm_num) this)
      _ = F.card * (2 * 2 ^ (Fintype.card α - t)) := by
          simp [Finset.sum_const, smul_eq_mul]
  -- |bad| < 2^n = |total colorings|
  have hbad_lt : bad.card < 2 ^ Fintype.card α := by
    have hpos : 0 < 2 ^ (Fintype.card α - t) := pow_pos (by norm_num) _
    calc bad.card
        ≤ F.card * (2 * 2 ^ (Fintype.card α - t)) := hbad_bound
      _ = F.card * 2 * 2 ^ (Fintype.card α - t) := by ring
      _ < 2 ^ t * 2 ^ (Fintype.card α - t) :=
          mul_lt_mul_of_pos_right hbound hpos
      _ = 2 ^ Fintype.card α := by rw [← pow_add]; congr 1; omega
  -- Since |bad| < |total|, there exists a non-bad coloring
  have hgood : ∃ c : α → Bool, c ∉ bad := by
    by_contra h; push_neg at h
    have : bad = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    rw [this, Finset.card_univ, Fintype.card_fun, Fintype.card_bool] at hbad_lt
    exact lt_irrefl _ hbad_lt
  obtain ⟨c, hc⟩ := hgood
  -- Convert the good coloring to HasPropertyB: S = {x | c x = true}
  refine ⟨Finset.univ.filter (c · = true), fun f hf => ?_⟩
  have hcf : ¬ IsMonochromaticOn c f := fun h =>
    hc (Finset.mem_biUnion.mpr ⟨f, hf, Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩⟩)
  simp only [IsMonochromaticOn, not_or] at hcf
  push_neg at hcf
  obtain ⟨⟨y, hyf, hyc⟩, ⟨x, hxf, hxc⟩⟩ := hcf
  constructor
  · exact ⟨x, Finset.mem_inter.mpr ⟨hxf,
      Finset.mem_filter.mpr ⟨Finset.mem_univ x, by cases h : c x <;> simp_all⟩⟩⟩
  · exact ⟨y, Finset.mem_sdiff.mpr ⟨hyf, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      cases h : c y <;> simp_all⟩⟩

/-- A family with at most one member of size ≥ 2 has Property B. -/
theorem hasPropertyB_card_le_one [Fintype α] (F : Finset (Finset α))
    (hsize : AllSizeAtLeast F 2) (hF : F.card ≤ 1) : HasPropertyB F := by
  by_cases h : F.card = 0
  · -- F is empty
    rw [Finset.card_eq_zero.mp h]
    exact hasPropertyB_empty
  · -- F has exactly one element
    have hone : F.card = 1 := by omega
    obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hone
    have hmem : f ∈ F := by rw [hf]; exact Finset.mem_singleton_self f
    rw [hf]
    exact hasPropertyB_singleton (hsize f hmem)

/-- The Erdős bound applies at t = 2: any family of one set of size ≥ 2 has Property B. -/
theorem first_moment_at_2 [Fintype α] (F : Finset (Finset α))
    (hsize : AllSizeAtLeast F 2) (hF : F.card < 2) : HasPropertyB F :=
  hasPropertyB_card_le_one F hsize (by omega)

end Erdos1022
