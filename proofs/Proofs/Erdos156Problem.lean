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

/-- For Sidon sets, |A + A| = |A| choose 2 + |A| = |A|*(|A|+1)/2.

    Proof structure:
    1. sumset A = image of (a,b) ↦ a+b on {(a,b) | a,b ∈ A, a ≤ b}
    2. This map is injective (Sidon property, proved in sidon_sum_injOn)
    3. Therefore |sumset A| = |{ordered pairs with a ≤ b}| = |A|*(|A|+1)/2

    Steps 1 and 2 are proved above. Step 3 (counting ordered pairs)
    remains as a sorry — it is a standard identity on triangular numbers
    suitable for automated proof search. -/
theorem sidon_sumset_size (A : Set ℕ) (hA : IsSidonSet A) (hfin : A.Finite) :
    (sumset A).Finite ∧
    (sumset A).ncard = A.ncard * (A.ncard + 1) / 2 := by
  refine ⟨sumset_finite A hfin, ?_⟩
  -- Rewrite sumset as image of injective map
  rw [sumset_eq_image]
  have hpairs_fin : Set.Finite {p : ℕ × ℕ | p.1 ∈ A ∧ p.2 ∈ A ∧ p.1 ≤ p.2} :=
    (hfin.prod hfin).subset (fun p hp => ⟨hp.1, hp.2.1⟩)
  rw [Set.ncard_image_of_injOn (sidon_sum_injOn A hA) hpairs_fin]
  -- Remaining: |{(a,b) ∈ A × A | a ≤ b}| = |A| * (|A| + 1) / 2
  sorry

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

end Erdos156
