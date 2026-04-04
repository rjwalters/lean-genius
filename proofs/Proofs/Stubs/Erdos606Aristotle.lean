/-
  Aristotle targets for Erdos606 (Distinct Lines from n Points)
  Routine supporting lemmas for automated proof search.
  See Erdos606Problem.lean for the main formalization.

  These lemmas provide building blocks for point-line incidence counting:
  - Counting distinct pairs from n elements: C(n,2) = n*(n-1)/2
  - Finset.univ structure for Fin n × Fin n
  - Basic properties of the distinctPairs construction
-/
import Mathlib

namespace Erdos606.Aristotle

open Finset

/-
  ## Section 1: Counting Ordered Pairs
-/

/-- The number of ordered pairs (i, j) with i < j from Fin n is n*(n-1)/2 -/
theorem fin_strict_pairs_card (n : ℕ) :
    (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ).card =
    n * (n - 1) / 2 := by
  sorry

/-- The set of pairs (i,j) with i < j from Fin n is the same as
    the image of {(i,j) : i < j} -/
lemma strict_pairs_eq_filter (n : ℕ) :
    (Finset.filter (fun p : Fin n × Fin n => p.1 < p.2) Finset.univ) =
    (Finset.univ.product Finset.univ).filter (fun p => p.1 < p.2) := by
  sorry

/-
  ## Section 2: Basic Combinatorics
-/

/-- n*(n-1)/2 for small values -/
lemma pairs_card_zero : 0 * (0 - 1) / 2 = 0 := by
  sorry

lemma pairs_card_one : 1 * (1 - 1) / 2 = 0 := by
  sorry

lemma pairs_card_two : 2 * (2 - 1) / 2 = 1 := by
  sorry

lemma pairs_card_three : 3 * (3 - 1) / 2 = 3 := by
  sorry

lemma pairs_card_four : 4 * (4 - 1) / 2 = 6 := by
  sorry

/-- C(n,2) = n*(n-1)/2 is always a natural number -/
lemma choose_two_eq (n : ℕ) : n.choose 2 = n * (n - 1) / 2 := by
  sorry

/-
  ## Section 3: Finset Properties
-/

/-- Finset.univ for Fin n × Fin n has card n² -/
lemma univ_fin_prod_card (n : ℕ) :
    (Finset.univ : Finset (Fin n × Fin n)).card = n * n := by
  sorry

/-- For n ≥ 1, Finset.univ : Finset (Fin n) is Nonempty -/
lemma fin_univ_nonempty (n : ℕ) (hn : n ≥ 1) :
    (Finset.univ : Finset (Fin n)).Nonempty := by
  sorry

/-- Strict order on Fin n: i < j implies i ≠ j -/
lemma fin_lt_ne {n : ℕ} (i j : Fin n) (h : i < j) : i ≠ j := by
  sorry

end Erdos606.Aristotle
