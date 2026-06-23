/-
  Aristotle targets for Erdos Problem #771 (Erdos-Graham Conjecture)
  Routine supporting lemmas for automated proof search.
  See Erdos771Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjectures or deep analytic results (Erdos-Graham, Alon-Freiman)
  - Known results likely provable from Mathlib (finset counting, divisibility)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos771Aristotle

open Finset Nat

/-- {1, ..., n} as a Finset -/
def Icc_n (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- The set of all nonempty subset sums of S -/
noncomputable def subsetSums (S : Finset ℕ) : Finset ℕ :=
  (S.powerset.image (fun A => ∑ a ∈ A, a)).filter (· > 0)

/-- A set S avoids sum m if no nonempty subset of S sums to m -/
def AvoidSum (S : Finset ℕ) (m : ℕ) : Prop :=
  m ∉ subsetSums S

/-- Multiples of p in {1, ..., n} -/
def primeMutliples (p n : ℕ) : Finset ℕ :=
  (Icc_n n).filter (fun k => p ∣ k)

-- ===================================================================
-- Section 1: Size of prime multiples
-- ===================================================================

/-- The number of multiples of p in {1, ..., n} equals floor(n/p).
    This is a standard counting result: multiples of p in [1,n] are p, 2p, ..., floor(n/p)*p. -/
theorem prime_multiples_size (p n : ℕ) (hp : p > 0) :
    (primeMutliples p n).card = n / p := by
  sorry

-- ===================================================================
-- Section 2: Prime multiples avoid non-multiples
-- ===================================================================

/-- Every element of primeMutliples p n is divisible by p. -/
theorem mem_primeMutliples_dvd (p n k : ℕ) (hk : k ∈ primeMutliples p n) :
    p ∣ k := by
  simp only [primeMutliples, Icc_n, Finset.mem_filter] at hk
  exact hk.2

/-- Any nonempty subset of primeMutliples p n has sum divisible by p. -/
theorem primeMutliples_subset_sum_dvd (p n : ℕ) (A : Finset ℕ)
    (hA : A ⊆ primeMutliples p n) :
    p ∣ ∑ a ∈ A, a := by
  apply Finset.dvd_sum
  intro k hk
  exact mem_primeMutliples_dvd p n k (hA hk)

/-- For prime p not dividing m, multiples of p avoid sum m.
    Any subset sum of multiples of p is a multiple of p, but m is not. -/
theorem prime_multiples_avoid (p m n : ℕ) (hp : Nat.Prime p) (hpm : ¬p ∣ m) :
    AvoidSum (primeMutliples p n) m := by
  sorry

-- ===================================================================
-- Section 3: Avoiding sum 1
-- ===================================================================

/-- The set {2, ..., n} is a 1-avoiding set of size n-1 for n >= 2. -/
theorem Icc_2_n_avoids_one (n : ℕ) (hn : n ≥ 2) :
    AvoidSum (Finset.Icc 2 n) 1 := by
  sorry

/-- The set {2, ..., n} has card n - 1. -/
theorem Icc_2_n_card (n : ℕ) (hn : n ≥ 2) :
    (Finset.Icc 2 n).card = n - 1 := by
  sorry

end Erdos771Aristotle
