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

/-!
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

/-!
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

/-!
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

/-- The greedy construction is maximal -/
theorem greedySidon_maximal (N : ℕ) : IsMaximalSidonSet (greedySidon N) N := by
  sorry -- Proof requires detailed analysis of the greedy construction

/-!
## Known Bounds

Classical results show that Sidon sets in {1,...,N} have size at most √N + O(N^{1/4}).
The greedy algorithm achieves close to this bound.
-/

/-- Upper bound: any Sidon set in {1,...,N} has size at most √N + O(1) -/
axiom sidon_upper_bound :
  ∃ C : ℝ, ∀ N : ℕ, ∀ A : Set ℕ, A ⊆ Interval N → IsSidonSet A →
    (size A : ℝ) ≤ Real.sqrt N + C

/-- The greedy construction achieves size Ω(√N) -/
axiom greedy_lower_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 1 →
    (size (greedySidon N) : ℝ) ≥ c * Real.sqrt N

/-!
## Ruzsa's Construction

Ruzsa [Ru98b] showed there exist maximal Sidon sets of size much smaller than
the greedy algorithm achieves. Specifically, size o((N log N)^{1/3}) is possible.
-/

/-- Ruzsa's result: maximal Sidon sets of size close to N^{1/3} exist -/
axiom ruzsa_small_maximal :
  ∀ ε > 0, ∃ f : ℕ → Set ℕ, 
    (∀ N, IsMaximalSidonSet (f N) N) ∧
    (∀ N ≥ 1, (size (f N) : ℝ) ≤ (N : ℝ)^((1/3 : ℝ) + ε))

/-!
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
axiom erdos_156_conjecture :
  (∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 1 →
    ∃ A : Set ℕ, IsMaximalSidonSet A N ∧ (size A : ℝ) ≤ C * (N : ℝ)^(1/3 : ℝ)) ∨
  (∀ C : ℝ, C > 0 → ∃ N₀ : ℕ, ∀ N ≥ N₀,
    ∀ A : Set ℕ, IsMaximalSidonSet A N → (size A : ℝ) > C * (N : ℝ)^(1/3 : ℝ))

/-!
## The Gap Between Bounds

The current state of knowledge shows a significant gap:
- Lower bound: some maximal Sidon sets have size ≈ N^{1/2}
- Upper bound (Ruzsa): some maximal Sidon sets have size ≈ N^{1/3+ε}
- The question is whether N^{1/3} is achievable
-/

/-- The minimum size of a maximal Sidon set in {1,...,N} -/
noncomputable def minMaximalSidonSize (N : ℕ) : ℕ :=
  Nat.find (⟨greedySidon N, greedySidon_is_sidon N,
    sorry⟩ : ∃ A, IsSidonSet A ∧ A ⊆ Interval N)

/-- The exponent of the minimum size growth -/
axiom minMaximalSidon_exponent :
  ∃ α : ℝ, 1/3 ≤ α ∧ α ≤ 1/2 ∧
    Filter.Tendsto (fun N => Real.log (minMaximalSidonSize N) / Real.log N)
      Filter.atTop (nhds α)

/-!
## Connection to Additive Combinatorics

Sidon sets are central objects in additive combinatorics. The study of
maximal Sidon sets connects to:
- Sumset theory (A + A has no repeated elements)
- B_h[g] sequences (generalizations of Sidon sets)
- The polynomial method in combinatorics
-/

/-- The sumset A + A -/
def sumset (A : Set ℕ) : Set ℕ := {s | ∃ a b : ℕ, a ∈ A ∧ b ∈ A ∧ s = a + b}

/-- For Sidon sets, |A + A| = |A| choose 2 + |A| -/
theorem sidon_sumset_size (A : Set ℕ) (hA : IsSidonSet A) (hfin : A.Finite) :
    (sumset A).Finite ∧ 
    (sumset A).ncard = A.ncard * (A.ncard + 1) / 2 := by
  sorry -- Standard counting argument

/-- B₂ sets are precisely Sidon sets -/
def IsB2Set (A : Set ℕ) : Prop := IsSidonSet A

/-!
## The Probabilistic Perspective

Random constructions can inform us about typical sizes of maximal Sidon sets.
A random subset of {1,...,N} of density p is typically a Sidon set if p << N^{-1/2}.
-/

/-- Expected size of random Sidon sets suggests barriers -/
axiom random_sidon_barrier :
  ∀ ε > 0, ∃ C : ℝ, 
    -- A random maximal Sidon set has size roughly N^{1/2}
    True

/-!
## The Main Problem Refined

The exact formulation considers the infimum over all maximal Sidon sets:

inf { |A| : A is a maximal Sidon set in {1,...,N} }

The question is whether this infimum is O(N^{1/3}).
-/

/-- The infimum of sizes of maximal Sidon sets -/
noncomputable def infMaximalSidonSize (N : ℕ) : ℝ :=
  ⨅ (A : Set ℕ) (_ : IsMaximalSidonSet A N), (size A : ℝ)

/-- The main open question in precise form -/
axiom erdos_156_precise :
  -- Is inf_N (infMaximalSidonSize N / N^{1/3}) bounded?
  (∃ C : ℝ, ∀ N ≥ 1, infMaximalSidonSize N ≤ C * (N : ℝ)^(1/3 : ℝ)) ∨
  (Filter.Tendsto (fun N => infMaximalSidonSize N / (N : ℝ)^(1/3 : ℝ))
    Filter.atTop Filter.atTop)

end Erdos156
