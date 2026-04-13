/-
  Aristotle targets for Erdős Problem #795
  Routine supporting lemmas for automated proof search.
  See Erdos795Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (Erdős/Raghavan bounds — deep analytic number theory)
  - Routine supporting facts: prime counting monotonicity, basic set product properties
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos795Aristotle

open Finset Nat

/-- π(n) counts primes ≤ n -/
def primePi (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter Nat.Prime |>.card

/-- A set A ⊆ ℕ has distinct subset products if every subset gives a different product -/
def HasDistinctSubsetProducts (A : Finset ℕ) : Prop :=
  ∀ S T : Finset ℕ, S ⊆ A → T ⊆ A → S ≠ T → S.prod id ≠ T.prod id

/-- A multiplicative Sidon set: no equation a*b = c*d with {a,b} ≠ {c,d} -/
def IsMultiplicativeSidon (A : Finset ℕ) : Prop :=
  ∀ a b c d ∈ A, a * b = c * d → ({a, b} : Finset ℕ) = {c, d}

-- Routine: primePi is monotone.
-- More primes can be ≤ m than ≤ n when n ≤ m.
theorem primePi_mono {n m : ℕ} (h : n ≤ m) : primePi n ≤ primePi m := by
  sorry

-- Routine: primePi n ≤ n.
-- There are at most n primes ≤ n.
theorem primePi_le_self (n : ℕ) : primePi n ≤ n := by
  sorry

-- Routine: The empty set has distinct subset products.
-- Vacuously true: there are no two distinct subsets.
theorem empty_has_distinct_products : HasDistinctSubsetProducts ∅ := by
  sorry

-- Routine: Any singleton {a} has distinct subset products.
-- The only subsets are ∅ and {a}, which have products 1 and a.
-- These are equal only if a = 1; but even then, ∅ ≠ {1}.
theorem singleton_has_distinct_products (a : ℕ) :
    HasDistinctSubsetProducts {a} := by
  sorry

-- Routine: If A has distinct subset products, so does any subset B ⊆ A.
theorem subset_has_distinct_products {A B : Finset ℕ}
    (hA : HasDistinctSubsetProducts A) (hB : B ⊆ A) :
    HasDistinctSubsetProducts B := by
  sorry

-- Routine: primePi 2 = 1 (only prime ≤ 2 is 2).
theorem primePi_two : primePi 2 = 1 := by
  sorry

-- Routine: If n ≥ 2, then primePi n ≥ 1 (2 is always a prime ≤ n).
theorem primePi_ge_one {n : ℕ} (hn : n ≥ 2) : primePi n ≥ 1 := by
  sorry

end Erdos795Aristotle
