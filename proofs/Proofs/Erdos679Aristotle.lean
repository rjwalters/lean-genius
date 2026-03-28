/-
  Aristotle targets for Erdős Problem #679
  Routine supporting lemmas for automated proof search.
  See Erdos679Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main conjecture or deep analytic results (Hardy-Ramanujan, etc.)
  - Known results likely provable from Mathlib (prime factor counting, additivity)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos679Aristotle

open Nat Finset

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Basic ω Properties (Mathlib primeFactors API)
-- ═══════════════════════════════════════════════════════════════════

/-- ω(n) = number of distinct prime divisors of n. -/
noncomputable def omega (n : ℕ) : ℕ := n.primeFactors.card

/-- ω(1) = 0. -/
theorem omega_one : omega 1 = 0 := by
  simp [omega]

/-- ω(p) = 1 for prime p. -/
theorem omega_prime (p : ℕ) (hp : p.Prime) : omega p = 1 := by
  simp [omega, Nat.primeFactors_prime hp]

/-- ω(p^k) = 1 for prime p and k ≥ 1. -/
theorem omega_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≥ 1) :
    omega (p ^ k) = 1 := by
  simp [omega, Nat.primeFactors_prime_pow hp (by omega)]

/-- ω is additive on coprime arguments. -/
theorem omega_mul_coprime (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0)
    (hmn : m.Coprime n) :
    omega (m * n) = omega m + omega n := by
  simp [omega]
  rw [Nat.Coprime.primeFactors_mul hmn hm hn]
  exact Finset.card_union_of_disjoint (Nat.Coprime.disjoint_primeFactors hmn)

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Ω vs ω Comparison
-- ═══════════════════════════════════════════════════════════════════

/-- Ω(n) = number of prime divisors counted with multiplicity. -/
noncomputable def bigOmega (n : ℕ) : ℕ := n.primeFactorsList.length

/-- Ω(n) ≥ ω(n) always. -/
theorem bigOmega_ge_omega (n : ℕ) : bigOmega n ≥ omega n := by
  simp only [bigOmega, omega, ge_iff_le]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · calc n.primeFactors.card
        ≤ n.primeFactorsList.toFinset.card := by
          apply Finset.card_le_card; intro p hp
          exact List.mem_toFinset.mpr ((Nat.mem_primeFactorsList hn).mpr
            ((Nat.mem_primeFactors hn).mp hp))
      _ ≤ n.primeFactorsList.length := List.toFinset_card_le_length

/-- Ω(1) = 0. -/
theorem bigOmega_one : bigOmega 1 = 0 := by
  simp [bigOmega]

/-- Ω(p) = 1 for prime p. -/
theorem bigOmega_prime (p : ℕ) (hp : p.Prime) : bigOmega p = 1 := by
  simp [bigOmega, Nat.primeFactorsList_prime hp]

/-- Ω(p^k) = k for prime p. -/
theorem bigOmega_prime_pow (p k : ℕ) (hp : p.Prime) :
    bigOmega (p ^ k) = k := by
  simp [bigOmega, Nat.primeFactorsList_prime_pow hp]

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: Small Computations
-- ═══════════════════════════════════════════════════════════════════

/-- ω(2) = 1. -/
theorem omega_two : omega 2 = 1 := omega_prime 2 Nat.prime_two

/-- ω(6) = 2 since 6 = 2 · 3. -/
theorem omega_six : omega 6 = 2 := by native_decide

/-- ω(30) = 3 since 30 = 2 · 3 · 5. -/
theorem omega_thirty : omega 30 = 3 := by native_decide

/-- Ω(12) = 3 since 12 = 2² · 3. -/
theorem bigOmega_twelve : bigOmega 12 = 3 := by native_decide

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Prime Factor Monotonicity
-- ═══════════════════════════════════════════════════════════════════

/-- If m | n and n ≠ 0, then ω(m) ≤ ω(n). -/
theorem omega_dvd_le (m n : ℕ) (hn : n ≠ 0) (h : m ∣ n) :
    omega m ≤ omega n := by
  simp only [omega]
  exact Finset.card_le_card (primeFactors_dvd_subset m n hn h)

/-- primeFactors of a divisor is a subset. -/
theorem primeFactors_dvd_subset (m n : ℕ) (hn : n ≠ 0) (h : m ∣ n) :
    m.primeFactors ⊆ n.primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors (show m ≠ 0 from Nat.ne_zero_of_dvd_ne_zero hn h)] at hp
  rw [Nat.mem_primeFactors hn]
  exact ⟨hp.1, hp.2.trans h⟩

end Erdos679Aristotle
