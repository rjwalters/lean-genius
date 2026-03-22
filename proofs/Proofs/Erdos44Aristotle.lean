/-
  Aristotle targets for Erdős Problem #44
  Routine supporting lemmas for automated proof search.
  See Erdos44Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (monotonicity, cardinality, bounds, etc.)
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

open Finset BigOperators

namespace Erdos44Aristotle

/-
  ## Erdős-Turán Sidon Construction

  For prime p, the set A_p = {2p·i + (i²%p) + 1 : i ∈ range p} is Sidon.
  The following lemmas prove the key properties.
-/

/-- The Erdős-Turán map i ↦ 2p·i + (i²%p) + 1 is injective on {0,...,p-1}:
    values lie in disjoint intervals [2pi, 2pi+p) for distinct i. -/
theorem erdosTuran_injOn (p : ℕ) (hp : 1 ≤ p) :
    Set.InjOn (fun i => 2 * p * i + i * i % p + 1) (↑(Finset.range p)) := by
  sorry

/-- The Erdős-Turán construction has exactly p elements. -/
theorem erdosTuran_card (p : ℕ) (hp : 1 ≤ p) :
    ((Finset.range p).image (fun i => 2 * p * i + i * i % p + 1)).card = p := by
  sorry

/-- All elements of the Erdős-Turán construction are ≥ 1. -/
theorem erdosTuran_pos (p i : ℕ) : 1 ≤ 2 * p * i + i * i % p + 1 := by
  omega

/-- All elements of the Erdős-Turán construction are ≤ 2p². -/
theorem erdosTuran_le (p : ℕ) (hp : 1 ≤ p) (i : ℕ) (hi : i < p) :
    2 * p * i + i * i % p + 1 ≤ 2 * p * p := by
  sorry

/-- Key step 1: from sum equality, extract index sum equality.
    2p(a+b) + R₁ = 2p(c+d) + R₂ with R₁, R₂ < 2p implies a+b = c+d. -/
theorem sum_eq_of_sum_eq {p a b c d : ℕ}
    (hp : 1 ≤ p) (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (heq : 2 * p * a + a * a % p + 1 + (2 * p * b + b * b % p + 1) =
           2 * p * c + c * c % p + 1 + (2 * p * d + d * d % p + 1)) :
    a + b = c + d := by
  sorry

/-- Key step 2: when index sums match, remainders match. -/
theorem rem_eq_of_sum_eq {p a b c d : ℕ}
    (hp : 1 ≤ p) (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (heq : 2 * p * a + a * a % p + 1 + (2 * p * b + b * b % p + 1) =
           2 * p * c + c * c % p + 1 + (2 * p * d + d * d % p + 1))
    (hab_cd : a + b = c + d) :
    a * a % p + b * b % p = c * c % p + d * d % p := by
  sorry

/-- Key step 3: from remainder equality and index sum equality, derive divisibility.
    a² + b² ≡ c² + d² (mod p) and a+b = c+d implies p | (ab - cd). -/
theorem dvd_prod_diff {p a b c d : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 ≤ p)
    (ha : a < p) (hb : b < p) (hc : c < p) (hd : d < p)
    (hab : a + b = c + d)
    (hrem : a * a % p + b * b % p = c * c % p + d * d % p) :
    (p : ℤ) ∣ ((a : ℤ) * b - c * d) := by
  sorry

/-- Key algebraic identity: (a-c)(a-d) = cd - ab when a+b = c+d. -/
theorem factor_identity (a b c d : ℤ) (h : a + b = c + d) :
    (a - c) * (a - d) = c * d - a * b := by
  have : b = c + d - a := by linarith
  rw [this]; ring

/-- Nat.sqrt N * Nat.sqrt N ≤ N (square of integer square root). -/
theorem sqrt_sq_le (N : ℕ) : Nat.sqrt N * Nat.sqrt N ≤ N :=
  Nat.sqrt_le N

/-- Nat.sqrt N ≤ 3 for N < 16. -/
theorem sqrt_le_three (N : ℕ) (hN : N < 16) : Nat.sqrt N ≤ 3 := by
  omega

end Erdos44Aristotle
