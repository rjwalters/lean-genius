/-
# Erdős Problem #949: Sum-Free Sets and Continuum-Sized Sumset Avoidance

Let S ⊆ ℝ be a set containing no solution to a + b = c (i.e., S is
sum-free). Must there exist A ⊆ ℝ \ S with |A| = 𝔠 (continuum)
such that A + A ⊆ ℝ \ S?

## Status: OPEN (general); SOLVED for Sidon sets

## References
- Erdős (original problem)
- Dillies–AlphaProof: proved the Sidon variant
-/

import Mathlib

open Set

-- ## Definitions

/-- A set S ⊆ ℝ is sum-free: no a, b, c ∈ S satisfy a + b = c.
Equivalently, (S + S) ∩ S = ∅. -/
def IsSumFreeSet (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a + b ∉ S

/-- A Sidon set in ℝ: all pairwise sums a + b with a ≤ b are distinct.
Equivalently, a + b = c + d with a ≤ b, c ≤ d implies (a,b) = (c,d). -/
def IsSidonReal (S : Set ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- The sumset A + A = {a + b : a, b ∈ A}. -/
def realSumset (A : Set ℝ) : Set ℝ :=
  {x | ∃ a ∈ A, ∃ b ∈ A, x = a + b}

-- ## The Main Problem

/-- **Erdős Problem #949**: If S ⊆ ℝ is sum-free, must there exist
A ⊆ ℝ \ S with |A| = 𝔠 such that A + A ⊆ ℝ \ S? -/
def ErdosProblem949 : Prop :=
  ∀ S : Set ℝ, IsSumFreeSet S →
    ∃ A : Set ℝ, A ⊆ Sᶜ ∧
      Cardinal.mk A = Cardinal.continuum ∧
      realSumset A ⊆ Sᶜ

-- ## The general problem is undecided (trivially by LEM)

theorem sum_free_decidable : ErdosProblem949 ∨ ¬ ErdosProblem949 :=
  em ErdosProblem949

-- ## Concrete examples of sum-free sets

/-- The set of odd numbers {1, 3, 5, ...} ∩ [1,∞) is sum-free
since odd + odd = even. -/
theorem odd_is_sum_free : IsSumFreeSet {x : ℝ | ∃ n : ℕ, x = 2 * n + 1} := by
  intro a ⟨m, hm⟩ b ⟨n, hn⟩ ⟨k, hk⟩
  subst hm; subst hn
  -- LHS = 2(m+n) + 2 (even), RHS = 2k + 1 (odd). Contradiction in ℕ.
  have h1 : (2 : ℝ) * ↑m + 1 + (2 * ↑n + 1) = 2 * (↑m + ↑n + 1) := by ring
  have h2 : (2 : ℝ) * (↑m + ↑n + 1) = 2 * ↑k + 1 := by linarith
  have h3 : (↑(2 * (m + n + 1)) : ℝ) = ↑(2 * k + 1) := by push_cast; linarith
  have h4 : 2 * (m + n + 1) = 2 * k + 1 := by exact_mod_cast h3
  omega

-- ## Sidon set examples and properties

/-- The empty set is trivially Sidon. -/
theorem sidon_empty : IsSidonReal ∅ := by
  intro a ha; exact absurd ha (Set.notMem_empty a)

/-- A singleton set is Sidon. -/
theorem sidon_singleton (x : ℝ) : IsSidonReal {x} := by
  intro a ha b hb c hc d hd _ _  _
  rw [mem_singleton_iff] at ha hb hc hd
  exact ⟨by rw [ha, hc], by rw [hb, hd]⟩

/-- Sidon sets are NOT necessarily sum-free. Counterexample:
{1, 2, 4} is Sidon (all pairwise sums 2,3,5,4,6,8 are distinct)
but 1 + 1 = 2 ∈ S, so it is not sum-free.

This corrects the previous axiom `sidon_is_sum_free` which was UNSOUND. -/
theorem sidon_not_implies_sum_free :
    ¬ (∀ S : Set ℝ, IsSidonReal S → (0 : ℝ) ∉ S → IsSumFreeSet S) := by
  intro h
  have hS : IsSidonReal ({1, 2, 4} : Set ℝ) := by
    intro a ha b hb c hc d hd hab hcd heq
    simp only [mem_insert_iff, mem_singleton_iff] at ha hb hc hd
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
      refine ⟨?_, ?_⟩ <;> linarith
  have h0 : (0 : ℝ) ∉ ({1, 2, 4} : Set ℝ) := by
    simp only [mem_insert_iff, mem_singleton_iff]; norm_num
  have hsf := h _ hS h0
  have : (1 : ℝ) + 1 ∉ ({1, 2, 4} : Set ℝ) := hsf 1 (by simp) 1 (by simp)
  simp only [mem_insert_iff, mem_singleton_iff] at this; norm_num at this

-- ## Structural Properties

/-- The empty set is sum-free. -/
theorem sum_free_empty : IsSumFreeSet ∅ :=
  fun _ ha => absurd ha (Set.notMem_empty _)

/-- {x} is sum-free for x ≠ 0. (0 + 0 = 0 means {0} is not sum-free.) -/
theorem sum_free_singleton {x : ℝ} (hx : x ≠ 0) : IsSumFreeSet {x} := by
  intro a ha b hb hab
  rw [Set.mem_singleton_iff] at ha hb hab
  subst ha; subst hb; exact hx (by linarith)

/-- A subset of a sum-free set is sum-free. -/
theorem sum_free_subset {S T : Set ℝ} (hT : IsSumFreeSet T) (hST : S ⊆ T) :
    IsSumFreeSet S :=
  fun a ha b hb hab => hT a (hST ha) b (hST hb) (hST hab)

/-- realSumset is monotone: A ⊆ B → A + A ⊆ B + B. -/
theorem realSumset_mono {A B : Set ℝ} (h : A ⊆ B) : realSumset A ⊆ realSumset B :=
  fun _ ⟨a, ha, b, hb, hx⟩ => ⟨a, h ha, b, h hb, hx⟩

/-- The open interval (1/3, 2/3) is sum-free.
    Classic result: if a, b ∈ (1/3, 2/3) then a + b > 2/3, so a + b ∉ (1/3, 2/3). -/
theorem open_interval_sum_free : IsSumFreeSet (Set.Ioo (1/3 : ℝ) (2/3)) := by
  intro a ⟨_, ha2⟩ b ⟨hb1, _⟩ ⟨_, hc2⟩
  linarith

/-- The sumset of the empty set is empty. -/
theorem realSumset_empty : realSumset ∅ = ∅ := by
  ext x; simp [realSumset]

/-- The sumset of a singleton {x} is {2x}. -/
theorem realSumset_singleton (x : ℝ) : realSumset {x} = {x + x} := by
  ext y; simp [realSumset]
  constructor
  · rintro ⟨a, rfl, b, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨x, rfl, x, rfl, rfl⟩

/-- The sumset contains all doubles: if a ∈ A then 2a ∈ A + A. -/
theorem mem_realSumset_of_mem {A : Set ℝ} {a : ℝ} (ha : a ∈ A) :
    a + a ∈ realSumset A :=
  ⟨a, ha, a, ha, rfl⟩

/-- {0} is NOT sum-free: 0 + 0 = 0. -/
theorem zero_not_sum_free : ¬IsSumFreeSet {(0 : ℝ)} := by
  intro h; exact h 0 rfl 0 rfl rfl

-- ## The Sidon Variant (Solved by Dillies/AlphaProof)

/-- The Sidon variant: if S is Sidon, then a continuum-sized
sumset-avoiding subset of the complement exists.
Note: this does NOT require S to be sum-free. -/
axiom sidon_variant_solved :
    ∀ S : Set ℝ, IsSidonReal S →
      ∃ A : Set ℝ, A ⊆ Sᶜ ∧
        Cardinal.mk A = Cardinal.continuum ∧
        realSumset A ⊆ Sᶜ

-- ## The general sum-free problem remains open
-- The key difficulty is that sum-free sets can be much denser than
-- Sidon sets, and the Sidon proof technique (exploiting injectivity
-- of the sum map) does not generalize. The general problem is OPEN.
