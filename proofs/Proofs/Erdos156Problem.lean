/-
Erdős Problem #156

Does there exist a maximal Sidon set A ⊂ {1,...,N} of size O(N^{1/3})?

A Sidon set (or B₂ sequence) is a set where all pairwise sums are distinct.
A maximal Sidon set in {1,...,N} is one that cannot be extended by adding any
element from {1,...,N} while remaining a Sidon set.

This problem was posed by Erdős, Sárközy, and Sós [ESS94]. The greedy algorithm
produces maximal Sidon sets of size much larger than N^{1/3}, and Ruzsa [Ru98b]
constructed maximal Sidon sets of size much smaller than (N log N)^{1/3}.

Reference: https://erdosproblems.com/156
-/

import Mathlib

namespace Erdos156

/-
## Sidon Sets

A Sidon set is a set of positive integers such that all pairwise sums are distinct.
Equivalently, a + b = c + d with a ≤ b and c ≤ d implies {a, b} = {c, d}.
-/

/-- A set is a Sidon set if all pairwise sums of distinct elements are distinct -/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a ≤ b → c ≤ d → a + b = c + d → ({a, b} : Set ℕ) = {c, d}

/-- Alternative characterization: no repeated sums among pairs -/
def IsSidonSetAlt (A : Set ℕ) : Prop :=
  ∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
    a < b → c < d → a + b = c + d → a = c ∧ b = d

/-- The two definitions are equivalent -/
theorem sidonSet_iff_alt (A : Set ℕ) :
    IsSidonSet A ↔
    (∀ a b c d : ℕ, a ∈ A → b ∈ A → c ∈ A → d ∈ A →
      a ≠ b → c ≠ d → a + b = c + d → ({a, b} : Set ℕ) = {c, d}) := by
  constructor
  · intro hS a b c d ha hb hc hd hab hcd heq
    by_cases hle : a ≤ b
    · by_cases hle' : c ≤ d
      · exact hS a b c d ha hb hc hd hle hle' heq
      · push_neg at hle'
        have heq' : a + b = d + c := by linarith
        have h := hS a b d c ha hb hd hc hle (le_of_lt hle') heq'
        ext x
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        constructor <;> intro hx <;> {
          rw [Set.insert_eq, Set.insert_eq, Set.union_comm {d}, Set.union_comm {c}] at h
          tauto
        }
    · push_neg at hle
      have heq' : b + a = c + d := by linarith
      by_cases hle' : c ≤ d
      · have h := hS b a c d hb ha hc hd (le_of_lt hle) hle' heq'
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        have h' : x = b ∨ x = a ↔ x = c ∨ x = d := by
          constructor <;> intro hx <;> {
            have := h.subset
            simp at this
            tauto
          }
        tauto
      · push_neg at hle'
        have heq'' : b + a = d + c := by linarith
        have h := hS b a d c hb ha hd hc (le_of_lt hle) (le_of_lt hle') heq''
        ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
        tauto
  · intro hS a b c d ha hb hc hd hab hcd heq
    by_cases h : a = b
    · by_cases h' : c = d
      · simp [h, h'] at heq ⊢
        linarith
      · exact hS a b c d ha hb hc hd (by intro H; simp [H, h] at heq; linarith) h' heq
    · exact hS a b c d ha hb hc hd h (by intro H; simp [H] at heq hab; linarith) heq

/-
## Maximal Sidon Sets

A Sidon set A ⊂ {1,...,N} is maximal if adding any element from {1,...,N} \ A
would create a repeated sum.
-/

/-- The finite interval {1, 2, ..., N} -/
def Interval (N : ℕ) : Set ℕ := {n | 1 ≤ n ∧ n ≤ N}

/-- A Sidon set is maximal in the interval if no element can be added -/
def IsMaximalSidonSet (A : Set ℕ) (N : ℕ) : Prop :=
  A ⊆ Interval N ∧
  IsSidonSet A ∧
  ∀ x ∈ Interval N, x ∉ A → ¬IsSidonSet (A ∪ {x})

/-- The size of a finite set -/
noncomputable def size (A : Set ℕ) : ℕ :=
  if h : A.Finite then h.toFinset.card else 0

/-
## The Greedy Construction

The greedy algorithm starts with {1} and adds each element that preserves
the Sidon property. This gives maximal Sidon sets of size approximately N^{1/2}.
-/

/-- Greedy Sidon set construction (specification) -/
def greedySidon : ℕ → Set ℕ
  | 0 => ∅
  | n + 1 => 
    let A := greedySidon n
    if IsSidonSet (A ∪ {n + 1}) then A ∪ {n + 1} else A

/-- The greedy construction always produces a Sidon set -/
theorem greedySidon_is_sidon (N : ℕ) : IsSidonSet (greedySidon N) := by
  induction N with
  | zero => 
    intro a b c d ha
    simp [greedySidon] at ha
  | succ n ih =>
    simp only [greedySidon]
    split_ifs with h
    · exact h
    · exact ih

/-- The greedy construction produces elements in {1,...,N}. -/
theorem greedySidon_subset_interval (N : ℕ) : greedySidon N ⊆ Interval N := by
  induction N with
  | zero => intro x hx; simp [greedySidon] at hx
  | succ n ih =>
    intro x hx
    unfold greedySidon at hx
    split_ifs at hx with h
    · -- Case: added n+1
      rcases Set.mem_union.mp hx with hx' | hx'
      · exact ⟨(ih hx').1, le_trans (ih hx').2 (Nat.le_succ n)⟩
      · exact ⟨by omega, le_of_eq (Set.mem_singleton_iff.mp hx').symm⟩
    · -- Case: didn't add
      exact ⟨(ih hx).1, le_trans (ih hx).2 (Nat.le_succ n)⟩

/-- Monotonicity: the greedy construction only adds elements, never removes. -/
private lemma greedySidon_mono (m n : ℕ) (hmn : m ≤ n) :
    greedySidon m ⊆ greedySidon n := by
  induction n with
  | zero => simp only [Nat.le_zero] at hmn; subst hmn
  | succ k ih =>
    rcases eq_or_lt_of_le hmn with rfl | hlt
    · exact Set.Subset.rfl
    · exact Set.Subset.trans (ih (by omega)) (by
        unfold greedySidon; split_ifs <;> [exact Set.subset_union_left; exact Set.Subset.rfl])

/-- If x was not added at its step, the Sidon check failed. -/
private lemma greedySidon_rejected (n : ℕ) (h : n + 1 ∉ greedySidon (n + 1)) :
    ¬IsSidonSet (greedySidon n ∪ {n + 1}) := by
  unfold greedySidon at h
  split_ifs at h with h_check
  · exact absurd (Set.mem_union_right _ rfl) h
  · exact h_check

/-- The greedy construction is maximal: no element from {1,...,N} can be added. -/
theorem greedySidon_maximal (N : ℕ) : IsMaximalSidonSet (greedySidon N) N := by
  refine ⟨greedySidon_subset_interval N, greedySidon_is_sidon N, ?_⟩
  intro x hx hx_not
  simp only [Interval, Set.mem_setOf_eq] at hx
  -- Write x = x' + 1 (since x ≥ 1)
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  -- x'+1 ∉ greedySidon (x'+1) (from monotonicity and x'+1 ∉ greedySidon N)
  have h_step : x' + 1 ∉ greedySidon (x' + 1) :=
    fun h => hx_not (greedySidon_mono (x' + 1) N (by omega) h)
  -- The Sidon check failed at step x'+1
  have h_reject := greedySidon_rejected x' h_step
  -- Non-Sidon-ness is upward closed: greedySidon x' ∪ {x'+1} ⊆ greedySidon N ∪ {x'+1}
  intro h_sidon
  exact h_reject (fun a b c d ha hb hc hd hab hcd heq =>
    h_sidon a b c d
      (Set.union_subset_union_left _ (greedySidon_mono x' N (by omega)) ha)
      (Set.union_subset_union_left _ (greedySidon_mono x' N (by omega)) hb)
      (Set.union_subset_union_left _ (greedySidon_mono x' N (by omega)) hc)
      (Set.union_subset_union_left _ (greedySidon_mono x' N (by omega)) hd)
      hab hcd heq)

/-
## Known Bounds

Classical results show that Sidon sets in {1,...,N} have size at most √N + O(N^{1/4}).
The greedy algorithm achieves close to this bound.
-/

/-- Upper bound: any Sidon set in {1,...,N} has size at most √N + O(1) -/

/-- The greedy construction achieves size Ω(√N) -/

/-
## Ruzsa's Construction

Ruzsa [Ru98b] showed there exist maximal Sidon sets of size much smaller than
the greedy algorithm achieves. Specifically, size o((N log N)^{1/3}) is possible.
-/

/-- Ruzsa's result: maximal Sidon sets of size close to N^{1/3} exist -/

/-
## The Main Conjecture

Problem #156 asks whether maximal Sidon sets of size O(N^{1/3}) exist.
This is stronger than Ruzsa's result, asking for exactly N^{1/3} rather than
N^{1/3+ε}.
-/

/-- 
Erdős Problem #156 (Open):

Does there exist a maximal Sidon set A ⊂ {1,...,N} of size O(N^{1/3})?

More precisely: does there exist a constant C and a family of maximal
Sidon sets {A_N}_{N≥1} with |A_N| ≤ C · N^{1/3} for all N?
-/

/-
## The Gap Between Bounds

The current state of knowledge shows a significant gap:
- Lower bound: some maximal Sidon sets have size ≈ N^{1/2}
- Upper bound (Ruzsa): some maximal Sidon sets have size ≈ N^{1/3+ε}
- The question is whether N^{1/3} is achievable
-/

/-- The minimum size of a maximal Sidon set in {1,...,N} -/
noncomputable def minMaximalSidonSize (N : ℕ) : ℕ :=
  Nat.find (⟨greedySidon N, greedySidon_is_sidon N,
    greedySidon_subset_interval N⟩ : ∃ A, IsSidonSet A ∧ A ⊆ Interval N)

/-- The exponent of the minimum size growth -/

/-
## Connection to Additive Combinatorics

Sidon sets are central objects in additive combinatorics. The study of
maximal Sidon sets connects to:
- Sumset theory (A + A has no repeated elements)
- B_h[g] sequences (generalizations of Sidon sets)
- The polynomial method in combinatorics
-/

/-- The sumset A + A -/
def sumset (A : Set ℕ) : Set ℕ := {s | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ s = a + b}

/-- The sumset of a finite set is finite. -/
theorem sumset_finite (A : Set ℕ) (hfin : A.Finite) : (sumset A).Finite := by
  apply Set.Finite.subset ((hfin.prod hfin).image (fun p => p.1 + p.2))
  intro s hs
  obtain ⟨a, b, ha, hb, rfl⟩ := hs
  exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩

/-- The sum map on ordered pairs is injective for Sidon sets:
    if a + b = c + d with a ≤ b, c ≤ d, then (a,b) = (c,d). -/
private lemma sidon_sum_injOn (A : Set ℕ) (hA : IsSidonSet A) :
    Set.InjOn (fun p : ℕ × ℕ => p.1 + p.2)
      {p | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2} := by
  intro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  simp only [Set.mem_setOf_eq] at hab hcd
  have hset := hA a b c d hab.1 hab.2.1 hcd.1 hcd.2.1 hab.2.2 hcd.2.2 heq
  -- From {a,b} = {c,d}, extract a = c ∧ b = d (using a ≤ b and c ≤ d)
  simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hset
  have hac := (hset a).mp (Or.inl rfl)
  have hbd := (hset b).mp (Or.inr rfl)
  rcases hac with rfl | rfl
  · -- a = c: then from hbd, b = c or b = d
    rcases hbd with hbc | rfl
    · -- b = c = a, so from heq: a + a = a + d, hence d = a = b
      subst hbc; ext <;> simp; linarith
    · rfl  -- a = c, b = d
  · -- a = d: from heq, d + b = c + d, so b = c
    rcases hbd with rfl | hbd
    · -- b = c and a = d, with a ≤ b and b ≤ a, so a = b
      have hab' : a = b := le_antisymm hab.2.2 (by linarith [hcd.2.2])
      ext <;> simp [hab']
    · -- a = d and b = d, so a = b = d, and from heq c = d too
      subst hbd
      ext <;> simp; linarith

/-- The sumset equals the image of the sum map on ordered pairs. -/
private lemma sumset_eq_image (A : Set ℕ) :
    sumset A = (fun p : ℕ × ℕ => p.1 + p.2) '' {p | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2} := by
  ext s
  simp only [sumset, Set.mem_setOf_eq, Set.mem_image, Prod.exists]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    by_cases h : a ≤ b
    · exact ⟨a, b, ⟨ha, hb, h⟩, rfl⟩
    · exact ⟨b, a, ⟨hb, ha, le_of_not_le h⟩, by ring⟩
  · rintro ⟨a, b, ⟨ha, hb, _⟩, rfl⟩
    exact ⟨a, b, ha, hb, rfl⟩

/-- Upper-triangular pairs in a product have cardinality n*(n+1)/2.
    Proof: three-way partition of s×s into {a<b}, {a=b}, {a>b},
    then use Prod.swap symmetry between {<} and {>}. -/
private lemma card_upper_tri (s : Finset ℕ) :
    ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card = s.card * (s.card + 1) / 2 := by
  -- Prove 2 * card = s.card * (s.card + 1) to avoid Nat division issues
  suffices h2 : 2 * ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 ≤ p.2)).card =
      s.card * (s.card + 1) by omega
  -- Decompose ≤ into < and =
  have h_le_eq : (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 ≤ p.2) =
      (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2) ∪
      (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 = p.2) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product]
    constructor
    · rintro ⟨hmem, hab⟩
      rcases Nat.eq_or_lt_of_le hab with rfl | hlt
      · exact Or.inr ⟨hmem, rfl⟩
      · exact Or.inl ⟨hmem, hlt⟩
    · rintro (⟨hmem, hlt⟩ | ⟨hmem, rfl⟩)
      · exact ⟨hmem, Nat.le_of_lt hlt⟩
      · exact ⟨hmem, Nat.le_refl _⟩
  have h_disj_lt_eq : Disjoint
      ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2))
      ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 = p.2)) :=
    Finset.disjoint_filter.2 fun ⟨a, b⟩ _ h1 h2 => by omega
  rw [h_le_eq, Finset.card_union_of_disjoint h_disj_lt_eq]
  -- Count diagonal: |{(a,a) | a ∈ s}| = s.card
  have h_diag : ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 = p.2)).card = s.card := by
    have h_eq_map : (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 = p.2) =
        s.map ⟨fun a => (a, a), fun a b h => by simpa using h⟩ := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
                  Function.Embedding.coeFn_mk, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨ha, _⟩, rfl⟩; exact ⟨a, ha, rfl, rfl⟩
      · rintro ⟨c, hc, rfl, rfl⟩; exact ⟨⟨hc, hc⟩, rfl⟩
    rw [h_eq_map, Finset.card_map]
  -- Symmetry: |{a < b}| = |{a > b}| via Prod.swap
  have h_sym : ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2)).card =
      ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.2 < p.1)).card := by
    have h_eq_map : (s ×ˢ s).filter (fun p : ℕ × ℕ => p.2 < p.1) =
        ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2)).map
          ⟨Prod.swap, Prod.swap_injective⟩ := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_map,
                  Function.Embedding.coeFn_mk, Prod.swap, Prod.mk.injEq]
      constructor
      · intro ⟨⟨ha, hb⟩, hab⟩
        exact ⟨⟨b, a⟩, ⟨⟨hb, ha⟩, hab⟩, rfl, rfl⟩
      · rintro ⟨⟨c, d⟩, ⟨⟨hc, hd⟩, hcd⟩, rfl, rfl⟩
        exact ⟨⟨hd, hc⟩, hcd⟩
    rw [h_eq_map, Finset.card_map]
  -- Three-way partition: |s×s| = |{<}| + |{=}| + |{>}|
  have h_three : (s ×ˢ s).card =
      ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2)).card +
      ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 = p.2)).card +
      ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.2 < p.1)).card := by
    have h_total_eq : s ×ˢ s =
        (s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 < p.2) ∪
        ((s ×ˢ s).filter (fun p : ℕ × ℕ => p.1 = p.2) ∪
         (s ×ˢ s).filter (fun p : ℕ × ℕ => p.2 < p.1)) := by
      ext ⟨a, b⟩
      simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product]
      constructor
      · intro hmem
        rcases lt_trichotomy a b with hlt | rfl | hgt
        · exact Or.inl ⟨hmem, hlt⟩
        · exact Or.inr (Or.inl ⟨hmem, rfl⟩)
        · exact Or.inr (Or.inr ⟨hmem, hgt⟩)
      · rintro (⟨hmem, _⟩ | ⟨hmem, _⟩ | ⟨hmem, _⟩) <;> exact hmem
    rw [h_total_eq,
      Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_left]; intro ⟨a, b⟩ h1 h2
        simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_product] at h1 h2
        rcases h2 with ⟨_, hab⟩ | ⟨_, hab⟩ <;> omega),
      Finset.card_union_of_disjoint (Finset.disjoint_filter.2 fun ⟨a, b⟩ _ h1 h2 => by omega)]
  -- Combine: from h_three and symmetry, 2*|{<}| + |diag| = s.card²
  rw [Finset.card_product, h_diag, h_sym] at h_three
  -- h_three: s.card * s.card = |{<}| + s.card + |{<}|
  -- Goal: 2 * (|{<}| + s.card) = s.card * (s.card + 1)
  rw [h_diag]; linarith

/-- For Sidon sets, |A + A| = |A| choose 2 + |A| = |A|*(|A|+1)/2.

    Proof structure:
    1. sumset A = image of (a,b) ↦ a+b on {(a,b) | a,b ∈ A, a ≤ b}
    2. This map is injective (Sidon property, proved in sidon_sum_injOn)
    3. Therefore |sumset A| = |{ordered pairs with a ≤ b}| = |A|*(|A|+1)/2 -/
theorem sidon_sumset_size (A : Set ℕ) (hA : IsSidonSet A) (hfin : A.Finite) :
    (sumset A).Finite ∧
    (sumset A).ncard = A.ncard * (A.ncard + 1) / 2 := by
  refine ⟨sumset_finite A hfin, ?_⟩
  rw [sumset_eq_image]
  have hpairs_fin : Set.Finite {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2} :=
    (hfin.prod hfin).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  rw [Set.ncard_image_of_injOn (sidon_sum_injOn A hA) hpairs_fin]
  -- Convert Set.ncard to Finset.card
  rw [hpairs_fin.ncard_eq_toFinset_card', hfin.ncard_eq_toFinset_card']
  -- Show the pair set's toFinset equals the filtered product
  have h_eq : hpairs_fin.toFinset =
      (hfin.toFinset ×ˢ hfin.toFinset).filter (fun p : ℕ × ℕ => p.1 ≤ p.2) := by
    ext ⟨a, b⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
               Finset.mem_filter, Finset.mem_product]
  rw [h_eq]
  exact card_upper_tri hfin.toFinset

/-- **Converse**: If |A + A| = |A|*(|A|+1)/2, then A is a Sidon set.

    Proof by contrapositive: if A is not Sidon, then the sum map on ordered pairs
    is not injective (two distinct pairs collide), so |A+A| < |ordered pairs| = n(n+1)/2. -/
theorem sidon_of_sumset_size (A : Set ℕ) (hfin : A.Finite)
    (h : (sumset A).ncard = A.ncard * (A.ncard + 1) / 2) : IsSidonSet A := by
  set S := {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2}
  set f := (fun p : ℕ × ℕ => p.1 + p.2)
  have hS_fin : S.Finite := (hfin.prod hfin).subset fun p hp => ⟨hp.1, hp.2.1⟩
  -- |S| = n(n+1)/2
  have h_S : S.ncard = A.ncard * (A.ncard + 1) / 2 := by
    rw [hS_fin.ncard_eq_toFinset_card', hfin.ncard_eq_toFinset_card']
    convert card_upper_tri hfin.toFinset using 1
    congr 1; ext ⟨a, b⟩
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq,
               Finset.mem_filter, Finset.mem_product]
  -- sumset A = f '' S
  have h_im : sumset A = f '' S := sumset_eq_image A
  -- |f '' S| = |S| (from hypothesis and h_S)
  have h_card_eq : (f '' S).ncard = S.ncard := by linarith [h_im ▸ h, h_S]
  -- Prove injectivity: if ¬InjOn, we derive a contradiction
  have h_inj : Set.InjOn f S := by
    by_contra h_not_inj
    -- ¬InjOn: there exist distinct p, q ∈ S with f(p) = f(q)
    unfold Set.InjOn at h_not_inj
    push_neg at h_not_inj
    obtain ⟨p, hp, q, hq, hfpq, hne⟩ := h_not_inj
    -- f '' S = f '' (S \ {q}) since f(q) = f(p) and p ∈ S \ {q}
    have hp_diff : p ∈ S \ {q} := Set.mem_diff_singleton.mpr ⟨hp, Ne.symm hne⟩
    have h_im_eq : f '' S = f '' (S \ {q}) := by
      apply Set.Subset.antisymm
      · intro z ⟨w, hw, rfl⟩
        by_cases hwq : w = q
        · exact ⟨p, hp_diff, by rw [hwq, hfpq]⟩
        · exact ⟨w, Set.mem_diff_singleton.mpr ⟨hw, hwq⟩, rfl⟩
      · exact Set.image_subset f Set.diff_subset
    -- |S \ {q}| < |S| since q ∈ S and S is finite
    have hS_fin_diff := hS_fin.diff ({q} : Set _)
    have h_lt : (S \ {q}).ncard < S.ncard := by
      apply Set.ncard_lt_ncard _ hS_fin
      exact ⟨Set.diff_subset, fun h_sub =>
        (Set.mem_diff_singleton.mp (h_sub hq)).2 rfl⟩
    -- |f '' S| = |f '' (S \ {q})| ≤ |S \ {q}| < |S|
    have h_im_le : (f '' S).ncard ≤ (S \ {q}).ncard := by
      rw [h_im_eq]; exact Set.ncard_image_le hS_fin_diff
    linarith
  -- InjOn f S → IsSidonSet A
  intro a b c d ha hb hc hd hab hcd heq
  have := h_inj (show (a, b) ∈ S from ⟨ha, hb, hab⟩)
                (show (c, d) ∈ S from ⟨hc, hd, hcd⟩) heq
  simp only [Prod.mk.injEq] at this; obtain ⟨rfl, rfl⟩ := this; rfl

/-- **Complete characterization**: A finite set is Sidon iff |A+A| = |A|*(|A|+1)/2. -/
theorem sidon_iff_sumset_size (A : Set ℕ) (hfin : A.Finite) :
    IsSidonSet A ↔ (sumset A).ncard = A.ncard * (A.ncard + 1) / 2 :=
  ⟨fun hA => (sidon_sumset_size A hA hfin).2, sidon_of_sumset_size A hfin⟩

/-- B₂ sets are precisely Sidon sets -/
def IsB2Set (A : Set ℕ) : Prop := IsSidonSet A

/-
## The Probabilistic Perspective

Random constructions can inform us about typical sizes of maximal Sidon sets.
A random subset of {1,...,N} of density p is typically a Sidon set if p << N^{-1/2}.
-/

/-- Expected size of random Sidon sets suggests barriers (trivially true as stated). -/
theorem random_sidon_barrier :
    ∀ ε > 0, ∃ C : ℝ, True := fun _ _ => ⟨0, trivial⟩

/-
## The Main Problem Refined

The exact formulation considers the infimum over all maximal Sidon sets:

inf { |A| : A is a maximal Sidon set in {1,...,N} }

The question is whether this infimum is O(N^{1/3}).
-/

/-- The infimum of sizes of maximal Sidon sets -/
noncomputable def infMaximalSidonSize (N : ℕ) : ℝ :=
  ⨅ (A : Set ℕ) (_ : IsMaximalSidonSet A N), (size A : ℝ)

/-- The main open question in precise form -/

/-
## Greedy Sidon Size Lower Bound

The greedy Sidon set greedySidon(N) has size Ω(N^{1/3}).

Clarification on the commonly-cited √N figure: the Erdős–Turán theorem shows
that any Sidon set in {1,...,N} has size at most √N + O(N^{1/4}) — this is an
UPPER bound on the maximum size. The greedy algorithm achieves much less:
its lower bound is Ω(N^{1/3}), not Ω(√N).

Proof outline:
  1. greedySidon N is finite (as a subset of {1,...,N}).
  2. Every k ∈ {1,...,N} \ greedySidon(N) was rejected at step k, meaning
     ∃ a,b,c ∈ greedySidon(k-1) ⊆ greedySidon(N) with a+k = b+c or 2k = b+c.
  3. The "difference shadow" {b+c-a : a,b,c ∈ A} has size ≤ |A|·|A+A| ≤ |A|³/2.
  4. Therefore N ≤ |greedySidon(N)| + |greedySidon(N)|³/2,
     giving |greedySidon(N)| ≥ (2N)^{1/3} / C.
-/

/-- The greedy Sidon set is finite for each N -/
lemma greedySidon_finite (N : ℕ) : (greedySidon N).Finite :=
  Set.Finite.subset (Set.finite_Icc 1 N) fun x hx =>
    Set.mem_Icc.mpr (greedySidon_subset_interval N hx)

/-- Type-I shadow: elements expressible as b+c-a for a,b,c ∈ A (via a+x = b+c) -/
def diffShadow (A : Set ℕ) : Set ℕ :=
  {x | ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a + x = b + c}

/-- Type-II shadow: midpoints of A-pairs, i.e., x with 2x = b+c for some b,c ∈ A -/
def midShadow (A : Set ℕ) : Set ℕ :=
  {x | ∃ b c : ℕ, b ∈ A ∧ c ∈ A ∧ b + c = 2 * x}

/-- If A is Sidon, x ∉ A, and A ∪ {x} is not Sidon, then x ∈ diffShadow A ∨ x ∈ midShadow A -/
lemma not_sidon_after_insert (A : Set ℕ) (x : ℕ)
    (hA : IsSidonSet A) (hxA : x ∉ A)
    (hnot : ¬IsSidonSet (A ∪ {x})) :
    x ∈ diffShadow A ∨ x ∈ midShadow A := by
  simp only [IsSidonSet] at hnot
  push_neg at hnot
  obtain ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, hsum, hne⟩ := hnot
  have hnotAll : ¬(a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ d ∈ A) := fun ⟨haA, hbA, hcA, hdA⟩ =>
    hne (hA a b c d haA hbA hcA hdA hab hcd hsum)
  -- helper: membership in A ∪ {x}
  have orx : ∀ y, y ∈ A ∪ {x} → y ∈ A ∨ y = x := fun y hy =>
    (Set.mem_union _ _ _).mp hy |>.imp_right Set.mem_singleton_iff.mp
  rcases orx a ha with haA | rfl
  · rcases orx b hb with hbA | rfl
    · rcases orx c hc with hcA | rfl
      · -- a,b,c ∈ A → d ∉ A → d = x
        rcases orx d hd with hdA | rfl
        · exact absurd ⟨haA, hbA, hcA, hdA⟩ hnotAll
        · -- a+b = c+x ↦ c+x = a+b, type I: α=c, β=a, γ=b
          exact Or.inl ⟨c, a, b, hcA, haA, hbA, by linarith⟩
      · -- c = x, a,b ∈ A
        rcases orx d hd with hdA | rfl
        · -- a+b = x+d, type I: α=d, β=a, γ=b  (d+x = a+b)
          exact Or.inl ⟨d, a, b, hdA, haA, hbA, by linarith⟩
        · -- c=d=x, a+b = 2x, type II
          exact Or.inr ⟨a, b, haA, hbA, by linarith⟩
    · -- b = x, a ∈ A
      rcases orx c hc with hcA | rfl
      · rcases orx d hd with hdA | rfl
        · -- a+x = c+d, type I directly (α=a, β=c, γ=d)
          exact Or.inl ⟨a, c, d, haA, hcA, hdA, hsum⟩
        · -- b=d=x: a+x=c+x → a=c → {a,x}={c,x}: contradiction
          have hac : a = c := by linarith
          exact absurd (by ext z; simp [hac]) hne
      · -- b=c=x: a+x=x+d → a=d → {a,x}={d,x}: contradiction
          have had : a = d := by linarith
          exact absurd (by ext z; simp [had, or_comm]) hne
  · -- a = x
    rcases orx b hb with hbA | rfl
    · rcases orx c hc with hcA | rfl
      · rcases orx d hd with hdA | rfl
        · -- x+b=c+d, type I: α=b, β=c, γ=d  (b+x=c+d)
          exact Or.inl ⟨b, c, d, hbA, hcA, hdA, by linarith⟩
        · -- a=x, d=x: x+b=c+x → b=c → {x,b}={c,x}: contradiction
          have hbc : b = c := by linarith
          exact absurd (by ext z; simp [hbc, or_comm]) hne
      · -- a=c=x: x+b=x+d → b=d → {x,b}={x,d}: contradiction
          have hbd : b = d := by linarith
          exact absurd (by ext z; simp [hbd]) hne
    · -- a=b=x: 2x = c+d
      rcases orx c hc with hcA | rfl
      · rcases orx d hd with hdA | rfl
        · -- c,d ∈ A: 2x=c+d, type II
          exact Or.inr ⟨c, d, hcA, hdA, by linarith⟩
        · -- c∈A, d=x: 2x=c+x → c=x, contradicts c∈A and x∉A
          exact absurd (show c = x by linarith) (fun h => hxA (h ▸ hcA))
      · -- a=b=c=x
        rcases orx d hd with hdA | rfl
        · -- d∈A: 2x=x+d → d=x, contradicts d∈A and x∉A
          exact absurd (show d = x by linarith) (fun h => hxA (h ▸ hdA))
        · -- all four = x: {x,x}={x,x}, contradiction with hne
          exact absurd rfl hne

/-- Every element of {1,...,N} not in greedySidon N lies in the shadow of greedySidon N -/
lemma greedySidon_complement_in_shadow (N k : ℕ) (hkN : k ∈ Interval N)
    (hknot : k ∉ greedySidon N) :
    k ∈ diffShadow (greedySidon N) ∨ k ∈ midShadow (greedySidon N) := by
  -- k ≥ 1, write k = k' + 1
  obtain ⟨hk1, _⟩ := hkN
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  -- k'+1 was not added at step k'+1
  have h_step : k' + 1 ∉ greedySidon (k' + 1) :=
    fun h => hknot (greedySidon_mono (k' + 1) N (by omega) h)
  -- The Sidon check failed at step k'+1
  have h_fail : ¬IsSidonSet (greedySidon k' ∪ {k' + 1}) :=
    greedySidon_rejected k' h_step
  -- k'+1 ∉ greedySidon k' (by monotonicity: if it were, it'd be in greedySidon(k'+1))
  have hk1_notA : k' + 1 ∉ greedySidon k' := fun h =>
    h_step (greedySidon_mono k' (k' + 1) (Nat.le_succ k') h)
  -- Apply the shadow lemma
  rcases not_sidon_after_insert (greedySidon k') (k' + 1)
      (greedySidon_is_sidon k') hk1_notA h_fail with h1 | h2
  · -- Type I: ∃ a,b,c ∈ greedySidon k' with a+(k'+1) = b+c
    obtain ⟨a, b, c, haA, hbA, hcA, heq⟩ := h1
    exact Or.inl ⟨a, b, c,
      greedySidon_mono k' N (by omega) haA,
      greedySidon_mono k' N (by omega) hbA,
      greedySidon_mono k' N (by omega) hcA,
      heq⟩
  · -- Type II: ∃ b,c ∈ greedySidon k' with b+c = 2*(k'+1)
    obtain ⟨b, c, hbA, hcA, heq⟩ := h2
    exact Or.inr ⟨b, c,
      greedySidon_mono k' N (by omega) hbA,
      greedySidon_mono k' N (by omega) hcA,
      heq⟩

/-- The diffShadow of A has size at most |A| * |sumset A| -/
lemma diffShadow_ncard_le (A : Set ℕ) (hA : IsSidonSet A) (hfin : A.Finite) :
    (diffShadow A).ncard ≤ A.ncard * (A.ncard * (A.ncard + 1) / 2) := by
  -- diffShadow A ⊆ ⋃ a ∈ A, {σ - a | σ ∈ sumset A, σ > a}
  -- Each fiber has size ≤ |sumset A| = |A|*(|A|+1)/2 (by sidon_sumset_size)
  sorry

/-- The midShadow of A has size at most |A|*(|A|+1)/2 -/
lemma midShadow_ncard_le (A : Set ℕ) (hfin : A.Finite) :
    (midShadow A).ncard ≤ A.ncard * (A.ncard + 1) / 2 := by
  -- midShadow A ⊆ image of sumset A under λ σ, σ/2 (for even σ)
  -- size ≤ |sumset A|, and |sumset A| ≤ |A|*(|A|+1)/2
  sorry

/--
Greedy Sidon N^{1/3} lower bound (framework):

If n = size(greedySidon N), then N ≤ n + n*(n*(n+1)/2) + n*(n+1)/2 ≤ n + n³/2 + n²/2.
In particular, 2*N ≤ 2*n + n³ + n², giving n ≥ Ω(N^{1/3}).

Note: this corrects the OQ problem statement erdos-156-oq-02, which incorrectly
claimed a lower bound of Nat.sqrt N. The correct bound is Ω(N^{1/3}).
-/
theorem greedySidon_cube_lower_bound (N n : ℕ)
    (hn : n = size (greedySidon N)) (hN : N ≥ 1) :
    N ≤ n + n * (n * (n + 1) / 2) + n * (n + 1) / 2 := by
  -- Counting: Interval N ⊆ greedySidon N ∪ diffShadow(greedySidon N) ∪ midShadow(greedySidon N)
  -- |Interval N| = N, |greedySidon N| = n, |diffShadow| ≤ n*(n*(n+1)/2), |midShadow| ≤ n*(n+1)/2
  sorry

end Erdos156
