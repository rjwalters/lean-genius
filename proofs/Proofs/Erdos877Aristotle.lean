/-
  Aristotle targets for Erdős Problem #877
  Routine supporting lemmas for automated proof search.
  See Erdos877Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Łuczak-Schoen bound, BLST sharp asymptotics)
  - NOT the open counting asymptotics (f_m(n) ~ 2^{n/4})
  - Routine sum-free set arithmetic: parity, filter bounds
  - No axioms, no definition sorries, no open conjectures
  - No /-! docstring sections
-/
import Mathlib

namespace Erdos877Aristotle

open Nat Finset

def isSumFree (A : Finset ℕ) : Prop :=
  ∀ a b c : ℕ, a ∈ A → b ∈ A → c ∈ A → a ≠ b + c

/-
  ## Section 1: Parity Arithmetic

  The odd numbers in {0,...,n} are sum-free: odd + odd = even ≠ odd.
  These basic parity facts support odds_construction in the main file.
-/

-- Aristotle target: sum of two odd naturals is even (norm_num / omega)
theorem odd_add_odd_even (b c : ℕ) (hb : b % 2 = 1) (hc : c % 2 = 1) :
    (b + c) % 2 = 0 := by sorry

-- Aristotle target: odd ≠ sum of two odds (follows from parity)
theorem odd_ne_sum_of_two_odds (a b c : ℕ)
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1) :
    a ≠ b + c := by sorry

-- Aristotle target: 0 is not odd (trivial)
theorem zero_not_odd : (0 : ℕ) % 2 ≠ 1 := by sorry

/-
  ## Section 2: The Odd Filter is Sum-Free

  odds_construction witnesses A = filter (fun x => x % 2 = 1) (range(n+1)).
  The sum-freeness of this set follows from Section 1 parity facts.
-/

-- Aristotle target: the filter of odd numbers in range(n+1) is sum-free
theorem isSumFree_odd_filter (n : ℕ) :
    isSumFree (Finset.filter (fun x => x % 2 = 1) (Finset.range (n + 1))) := by sorry

-- Aristotle target: odd filter is a subset of range(n+1)
theorem odd_filter_subset_range (n : ℕ) :
    Finset.filter (fun x => x % 2 = 1) (Finset.range (n + 1)) ⊆ Finset.range (n + 1) := by sorry

-- Aristotle target: odd filter has cardinality ≥ n / 2
-- Proof sketch: odds in {0,...,n} number ⌈(n+1)/2⌉ = (n+1)/2 ≥ n/2
theorem odd_filter_card_ge_half (n : ℕ) :
    (Finset.filter (fun x => x % 2 = 1) (Finset.range (n + 1))).card ≥ n / 2 := by sorry

/-
  ## Section 3: Existence of a Large Sum-Free Subset

  This is the direct content of odds_construction in Erdos877Problem.lean.
  Combined from Sections 1-2: the odd filter witnesses the existence claim.
-/

-- Aristotle target: exists A ⊆ range(n+1) that is sum-free and has card ≥ n/2
-- Witness: A = filter (fun x => x % 2 = 1) (range(n+1))
theorem odds_construction_goal (n : ℕ) : ∃ A : Finset ℕ,
    A ⊆ Finset.range (n + 1) ∧
    isSumFree A ∧
    A.card ≥ n / 2 := by sorry

/-
  ## Section 4: Sum-Free Maximality Helpers

  Supporting the maximal_criterion theorem: if A is sum-free and
  inserting x breaks sum-freeness, then x appears in the violating triple.
-/

-- Aristotle target: ¬isSumFree A implies existence of a violating triple
theorem not_isSumFree_triple (A : Finset ℕ) (h : ¬isSumFree A) :
    ∃ a b c : ℕ, a ∈ A ∧ b ∈ A ∧ c ∈ A ∧ a = b + c := by sorry

-- Aristotle target: if A is sum-free and insert x A is not, then x is in the triple
-- (since A itself has no sum triple, the new element x must appear)
theorem insert_breaks_sum_free_via_x (A : Finset ℕ) (x : ℕ)
    (hx : x ∉ A)
    (hA : isSumFree A)
    (hAx : ¬isSumFree (insert x A)) :
    ∃ a b c : ℕ,
      a ∈ insert x A ∧ b ∈ insert x A ∧ c ∈ insert x A ∧ a = b + c ∧
      (a = x ∨ b = x ∨ c = x) := by sorry

end Erdos877Aristotle
