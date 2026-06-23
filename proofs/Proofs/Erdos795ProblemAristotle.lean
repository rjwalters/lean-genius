/-
  Aristotle targets for Erdős Problem #795: Distinct Subset Products
  Routine supporting lemmas for automated proof search.
  See Erdos795Problem.lean for the main formalization.

  This companion imports Proofs.Erdos795Problem and operates in the
  Erdos795 namespace so that proofs here directly close sorries in
  the main file.

  Criteria for inclusion:
  - Routine supporting lemmas (NOT the main Erdős/Raghavan bounds)
  - No def sorries, no axiom declarations, no open conjectures
  - No references to noncomputable g (elaboration issues in Aristotle context)
-/
import Mathlib
import Proofs.Erdos795Problem

namespace Erdos795

open Finset Nat

-- Routine: primePi is monotone.
-- More primes can be ≤ m than ≤ n when n ≤ m.
theorem primePi_mono {n m : ℕ} (h : n ≤ m) : primePi n ≤ primePi m := by
  sorry

-- Routine: primePi n ≤ n.
-- There are at most n primes ≤ n (filter of range n+1 has card ≤ n+1).
theorem primePi_le_self (n : ℕ) : primePi n ≤ n := by
  sorry

-- Routine: The empty set has distinct subset products.
-- Vacuously true: no two distinct subsets exist.
theorem empty_has_distinct_products : HasDistinctSubsetProducts ∅ := by
  sorry

-- Routine: Any singleton {a} has distinct subset products.
-- The only subsets are ∅ and {a}, and ∅.prod id = 1, {a}.prod id = a.
theorem singleton_has_distinct_products (a : ℕ) :
    HasDistinctSubsetProducts {a} := by
  sorry

-- Routine: If A has distinct subset products, so does any subset B ⊆ A.
-- Subsets of B are also subsets of A, so injectivity transfers.
theorem subset_has_distinct_products {A B : Finset ℕ}
    (hA : HasDistinctSubsetProducts A) (hB : B ⊆ A) :
    HasDistinctSubsetProducts B := by
  sorry

-- Routine: primePi 2 = 1 (only prime ≤ 2 is 2).
theorem primePi_two : primePi 2 = 1 := by
  sorry

-- Routine: If n ≥ 2 then primePi n ≥ 1 (2 is always a prime ≤ n).
theorem primePi_ge_one {n : ℕ} (hn : n ≥ 2) : primePi n ≥ 1 := by
  sorry

-- Routine: {2, 3, 5} has distinct subset products.
-- Subset products: 1, 2, 3, 5, 6, 10, 15, 30 — all distinct.
theorem primes_235_distinct : HasDistinctSubsetProducts {2, 3, 5} := by
  sorry

-- Routine: {2, 3, 6} does NOT have distinct subset products.
-- {2, 3} and {6} both give product 6.
theorem not_distinct_236 : ¬HasDistinctSubsetProducts {2, 3, 6} := by
  sorry

-- Routine: {2, 6, 18} has distinct subset products but is not multiplicative Sidon.
-- Witness: 6 * 6 = 2 * 18 = 36, but {6} ≠ {2, 18}.
theorem distinct_products_not_sidon :
    ∃ A : Finset ℕ, HasDistinctSubsetProducts A ∧ ¬IsMultiplicativeSidon A := by
  sorry

end Erdos795
