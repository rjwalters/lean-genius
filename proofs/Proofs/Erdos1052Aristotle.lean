/-
  Aristotle targets for Erdős Problem #1052 (Unitary Perfect Numbers)
  Routine supporting lemmas for automated proof search.
  See Erdos1052Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture
  - Known result likely in Mathlib (divisor sums, coprimality, etc.)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos1052Aristotle

/-- A proper unitary divisor of n is a divisor d with gcd(d, n/d) = 1 and d < n. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ d.Coprime (n / d))

/-- The unitary divisor function: sum of all unitary divisors of n (including n itself). -/
def unitaryDivisorSum (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))).sum id

/-- σ*(1) = 1: the only unitary divisor of 1 is 1 itself. -/
theorem unitaryDivisorSum_one : unitaryDivisorSum 1 = 1 := by native_decide

/-- σ*(p) = 1 + p for prime p: the unitary divisors of a prime are 1 and p. -/
theorem unitaryDivisorSum_prime {p : ℕ} (hp : p.Prime) :
    unitaryDivisorSum p = 1 + p := by
  simp only [unitaryDivisorSum]
  -- For prime p, Ico 1 (p+1) filtered by (d ∣ p ∧ d.Coprime (p/d)) = {1, p}
  have hp2 : p ≥ 2 := hp.two_le
  have : (Finset.Ico 1 (p + 1)).filter (fun d => d ∣ p ∧ d.Coprime (p / d)) = {1, p} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd1, hdp1⟩, hdvd, hcop⟩
      rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨le_refl 1, by omega⟩, one_dvd p, Nat.coprime_one_left _⟩
      · refine ⟨⟨by omega, by omega⟩, dvd_refl p, ?_⟩
        simp [Nat.div_self (by omega : 0 < p), Nat.Coprime.symm, Nat.coprime_one_right]
  rw [this]
  simp [Finset.sum_insert (by simp [Nat.Prime.ne_one hp] : p ∉ ({1} : Finset ℕ))]

/-- For a prime power p^k with k ≥ 1, σ*(p^k) = 1 + p^k.
    The only unitary divisors are 1 and p^k itself. -/
theorem unitaryDivisorSum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    unitaryDivisorSum (p ^ k) = 1 + p ^ k := by sorry

/-- The number of proper unitary divisors of a prime is 1 (just {1}). -/
theorem card_properUnitaryDivisors_prime {p : ℕ} (hp : p.Prime) :
    (properUnitaryDivisors p).card = 1 := by
  have hp1 : p ≥ 2 := hp.two_le
  simp only [properUnitaryDivisors]
  -- Ico 1 p filtered to {d | d ∣ p ∧ d.Coprime (p/d)}
  -- For prime p, divisors are 1 and p. Only d < p qualifies, so d = 1.
  -- 1 ∣ p ✓, Coprime 1 (p/1) = Coprime 1 p ✓
  convert Finset.card_singleton (1 : ℕ) using 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd1, hdp⟩, hdvd, hcop⟩
    rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl
    · rfl
    · omega
  · rintro rfl
    exact ⟨⟨le_refl 1, hp1⟩, one_dvd p, Nat.coprime_one_left _⟩

/-- If d is a unitary divisor of n, then n/d is also a unitary divisor of n. -/
theorem unitary_complement_mem {n d : ℕ} (hn : 0 < n)
    (hd : d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))) :
    n / d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d)) := by sorry

/-- The unitary divisor sum of a product of two coprime numbers equals the product
    of their unitary divisor sums. This is the multiplicativity property. -/
theorem unitaryDivisorSum_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    unitaryDivisorSum (m * n) = unitaryDivisorSum m * unitaryDivisorSum n := by sorry

end Erdos1052Aristotle
