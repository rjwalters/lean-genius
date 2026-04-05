/-
  Aristotle targets for Erdős Problem #1095: The Erdős-Selfridge Function
  Routine supporting lemmas for automated proof search.
  See Stubs/Erdos1095Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the open problem (growth rate of g(k))
  - NOT theorems depending on axiomatized deep results (EES74, Konyagin, etc.)
  - Routine properties of isKRough, binomIsKRough, and lcmUpTo
  - No definition sorries
  - No axioms

  Included targets (5):
  - isKRough_one: isKRough 1 k (1 has no prime factors)
  - isKRough_antitone: j ≤ k → isKRough n k → isKRough n j
  - isKRough_not_dvd: isKRough n k → p.Prime → p ≤ k → ¬(p ∣ n)
  - binomIsKRough_zero: binomIsKRough n 0 (C(n,0) = 1 is trivially 0-rough)
  - lcmUpTo_pos: 0 < lcmUpTo k
-/
import Mathlib

open Nat Finset BigOperators

namespace Erdos1095Aristotle

/-- An integer is k-rough if all its prime factors exceed k -/
def isKRough (n k : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p > k

/-- C(n,k) is k-rough: all prime factors exceed k -/
def binomIsKRough (n k : ℕ) : Prop :=
  isKRough (Nat.choose n k) k

/-- L_k = lcm(1, 2, ..., k). -/
def lcmUpTo (k : ℕ) : ℕ :=
  (Finset.Icc 1 k).lcm id

-- Routine: 1 is k-rough for any k.
-- 1 has no prime factors, so the condition is vacuously true.
theorem isKRough_one (k : ℕ) : isKRough 1 k := by
  sorry

-- Routine: isKRough is antitone in the roughness threshold.
-- If n is k-rough and j ≤ k, then n is j-rough.
theorem isKRough_antitone (n j k : ℕ) (hjk : j ≤ k) (h : isKRough n k) : isKRough n j := by
  sorry

-- Routine: k-rough means primes ≤ k do not divide n.
-- Contrapositive of the isKRough definition.
theorem isKRough_not_dvd (n k : ℕ) (p : ℕ) (hp : p.Prime) (hpk : p ≤ k)
    (hrough : isKRough n k) : ¬(p ∣ n) := by
  sorry

-- Routine: C(n,0) = 1 is 0-rough.
-- Nat.choose n 0 = 1 which has no prime factors.
theorem binomIsKRough_zero (n : ℕ) : binomIsKRough n 0 := by
  sorry

-- Routine: lcmUpTo k is always positive.
-- The lcm of any set of natural numbers in Lean is ≥ 1.
theorem lcmUpTo_pos (k : ℕ) : 0 < lcmUpTo k := by
  sorry

end Erdos1095Aristotle
