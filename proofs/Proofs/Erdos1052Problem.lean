/-
Erdős Problem #1052: Unitary Perfect Numbers

A unitary divisor d of n is one where gcd(d, n/d) = 1.
A unitary perfect number is a positive integer equal to the sum of its
proper unitary divisors.

Main Results:
- Computational verification: 6, 60, 90 are unitary perfect (native_decide)
- Sum-of-odd-parity lemma (proved by induction)
- Unitary complement theorem (proved)
- Coprime characterization of unitary divisors (proved)
- All unitary perfect numbers are even (axiom with proof sketch)

Known unitary perfect numbers: 6, 60, 90, 87360, 146361946186458562560000
It is conjectured there are only finitely many.

References:
- https://erdosproblems.com/1052
- Wall, Charles R. "The fifth unitary perfect number" (1972)
-/
import Mathlib

namespace Erdos1052

/-
## Core Definitions
-/

/-- A proper unitary divisor of n is a divisor d with gcd(d, n/d) = 1 and d < n. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ d.Coprime (n / d))

/-- A number n > 0 is a unitary perfect number if it equals the sum of its
proper unitary divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  (properUnitaryDivisors n).sum id = n ∧ 0 < n

-- Decidable instance for computational verification
instance (n : ℕ) : Decidable (IsUnitaryPerfect n) := by
  unfold IsUnitaryPerfect; exact instDecidableAnd

/-
## Basic Properties
-/

theorem one_mem_properUnitaryDivisors {n : ℕ} (hn : 1 < n) :
    1 ∈ properUnitaryDivisors n := by
  simp only [properUnitaryDivisors, Finset.mem_filter, Finset.mem_Ico]
  constructor
  · omega
  · constructor
    · exact one_dvd n
    · simp [Nat.Coprime]

theorem mem_properUnitaryDivisors {n d : ℕ} :
    d ∈ properUnitaryDivisors n ↔ d ∈ Finset.Ico 1 n ∧ d ∣ n ∧ d.Coprime (n / d) := by
  simp [properUnitaryDivisors]

/-- Unitary divisors of an odd number are odd. -/
theorem odd_of_unitaryDivisor_of_odd {n d : ℕ} (hn : Odd n) (hd : d ∣ n)
    (_hcop : d.Coprime (n / d)) : Odd d := by
  by_contra h
  have hd_even : Even d := Nat.not_odd_iff_even.mp h
  have h2_dvd_d : 2 ∣ d := Even.two_dvd hd_even
  have h2_dvd_n : 2 ∣ n := dvd_trans h2_dvd_d hd
  exact hn.not_two_dvd_nat h2_dvd_n

/-
## Parity Lemmas
-/

/-- Sum of odd numbers has odd parity iff the count is odd.
Proof by Finset induction using Odd/Even arithmetic. -/
theorem sum_odd_parity {s : Finset ℕ} (hs : ∀ x ∈ s, Odd x) :
    Odd (s.sum id) ↔ Odd s.card := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have ha_odd : Odd a := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ x ∈ s, Odd x := fun x hx => hs x (Finset.mem_insert_of_mem hx)
    -- Helper: Even n and Odd n cannot both hold
    have even_odd_absurd : ∀ n : ℕ, Even n → Odd n → False := by
      intro n ⟨r, hr⟩ ⟨k, hk⟩; omega
    constructor
    · intro h_odd
      have h_sum_even : Even (s.sum id) := by
        by_contra h_sum_not_even
        have h_sum_odd : Odd (s.sum id) :=
          (Nat.even_or_odd _).resolve_left h_sum_not_even
        exact even_odd_absurd _ (ha_odd.add_odd h_sum_odd) h_odd
      have h_card_even : Even s.card := by
        by_contra h_card_not_even
        have h_card_odd : Odd s.card :=
          (Nat.even_or_odd _).resolve_left h_card_not_even
        exact even_odd_absurd _ h_sum_even ((ih hs').mpr h_card_odd)
      exact h_card_even.add_one
    · intro h_succ_odd
      have h_card_even : Even s.card := by
        obtain ⟨k, hk⟩ := h_succ_odd; exact ⟨k, by omega⟩
      have h_sum_even : Even (s.sum id) := by
        by_contra h_sum_not_even
        have h_sum_odd : Odd (s.sum id) :=
          (Nat.even_or_odd _).resolve_left h_sum_not_even
        exact even_odd_absurd _ h_card_even ((ih hs').mp h_sum_odd)
      exact ha_odd.add_even h_sum_even

/-
## Unitary Divisor Structure
-/

/-- A divisor d of n is unitary iff no prime divides both d and n/d. -/
theorem unitary_iff_no_common_prime {n d : ℕ} :
    d.Coprime (n / d) ↔ ∀ p : ℕ, p.Prime → p ∣ d → ¬(p ∣ n / d) := by
  rw [Nat.Coprime]
  constructor
  · intro hcop p hp hpd hpnd
    have : p ∣ d.gcd (n / d) := Nat.dvd_gcd hpd hpnd
    rw [hcop] at this
    exact Nat.Prime.not_dvd_one hp this
  · intro h
    by_contra hne
    have hne' : d.gcd (n / d) ≠ 1 := hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne'
    exact h p hp (dvd_trans hpdvd (Nat.gcd_dvd_left d (n / d)))
      (dvd_trans hpdvd (Nat.gcd_dvd_right d (n / d)))

/-- Complement of a unitary divisor is unitary. -/
theorem unitary_complement {n d : ℕ} (hd : d ∣ n) (hn : 0 < n)
    (hcop : d.Coprime (n / d)) : (n / d).Coprime (n / (n / d)) := by
  have hn_ne : n ≠ 0 := by omega
  rw [Nat.div_div_self hd hn_ne]
  exact hcop.symm

/-- The unitary divisor function: sum of all unitary divisors of n. -/
def unitaryDivisorSum (n : ℕ) : ℕ :=
  ((Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))).sum id

/-
## Main Theorem: All Unitary Perfect Numbers are Even

**Proof:**
For n = p₁^a₁ · ... · pₖ^aₖ with pᵢ distinct primes, the unitary divisor
sum factors as σ*(n) = ∏ᵢ(1 + pᵢ^aᵢ).

For unitary perfect n: σ*(n) = 2n.

If n were odd, every pᵢ would be odd, so each factor 1 + pᵢ^aᵢ is even.
With k = ω(n) distinct prime factors, σ*(n) is divisible by 2^k.

Case k ≥ 2: Then 2^k | σ*(n) = 2n, so 2^(k-1) | n. But n is odd, contradiction.

Case k = 1: Then n = p^a for odd prime p. σ*(p^a) = 1 + p^a = 2p^a,
giving 1 = p^a, impossible since p ≥ 2 and a ≥ 1.

Case k = 0: n = 1, but σ*(1) = 1 ≠ 2 = 2·1, so 1 isn't unitary perfect.
-/
axiom even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n

/-
## Verified Examples
-/

/-- The number 6 is a unitary perfect number.
Proper unitary divisors of 6 = 2 · 3: {1, 2, 3}. Sum = 6. -/
theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by native_decide

/-- The number 60 is a unitary perfect number.
60 = 2² · 3 · 5. Proper unitary divisors: {1, 3, 4, 5, 12, 15, 20}. Sum = 60. -/
theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by native_decide

/-- The number 90 is a unitary perfect number.
90 = 2 · 3² · 5. Proper unitary divisors: {1, 2, 5, 9, 10, 18, 45}. Sum = 90. -/
theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by native_decide

/-
## Further Properties
-/

/-- For prime powers p^k, the only unitary divisors are 1 and p^k.
Proof: d ∣ p^k means d = p^j for some j ≤ k. Then p^k/d = p^(k-j).
If 0 < j < k, then p divides both p^j and p^(k-j), contradicting coprimality. -/
theorem unitaryDivisors_primePow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    (Finset.Ico 1 (p^k + 1)).filter (fun d => d ∣ p^k ∧ d.Coprime (p^k / d)) = {1, p^k} := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · -- Forward: d in filter → d = 1 or d = p^k
    rintro ⟨⟨h1le, hlt⟩, hdvd, hcop⟩
    obtain ⟨j, hjk, rfl⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    by_cases hj0 : j = 0
    · left; simp [hj0]
    · right
      by_cases hjk' : j = k
      · exact congr_arg _ hjk'
      · -- 0 < j < k: p divides both p^j and p^(k-j)
        exfalso
        have hj_pos : 0 < j := Nat.pos_of_ne_zero hj0
        have hkj_pos : 0 < k - j := by omega
        have hdiv : p ^ k / p ^ j = p ^ (k - j) := Nat.pow_div hjk hp.pos
        rw [hdiv] at hcop
        have h_pdvd_j : p ∣ p ^ j := dvd_pow_self p (by omega)
        have h_pdvd_kj : p ∣ p ^ (k - j) := dvd_pow_self p (by omega)
        exact (hp.coprime_iff_not_dvd.mp (hcop.coprime_dvd_left h_pdvd_j)) h_pdvd_kj
  · -- Backward: d = 1 or d = p^k → d in filter
    rintro (rfl | rfl)
    · -- d = 1
      exact ⟨⟨le_refl 1, by linarith [Nat.one_le_pow k p hp.pos]⟩, one_dvd _,
        by simp [Nat.Coprime]⟩
    · -- d = p^k
      refine ⟨⟨Nat.one_le_pow k p hp.pos, Nat.lt_add_one _⟩, dvd_refl _, ?_⟩
      rw [Nat.div_self (Nat.pos_of_ne_zero (pow_ne_zero k hp.ne_zero))]
      exact Nat.coprime_one_right _

/-- The unitary divisor sum is multiplicative for coprime arguments. -/
axiom unitaryDivisorSum_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    unitaryDivisorSum (m * n) = unitaryDivisorSum m * unitaryDivisorSum n

/-- Proper unitary divisors pair up via d ↦ n/d, except possibly at the square root. -/
axiom properUnitaryDivisors_pairing {n : ℕ} (hn : 1 < n) :
    ∃ pairs : Finset (ℕ × ℕ), ∃ singleton : Option ℕ,
      (∀ p ∈ pairs, p.1 < p.2 ∧ p.1 * p.2 = n ∧
        p.1 ∈ properUnitaryDivisors n ∧ p.2 ∈ properUnitaryDivisors n) ∧
      (∀ s ∈ singleton, s * s = n ∧ s ∈ properUnitaryDivisors n)

/-
## The Main Conjecture (OPEN)
-/

/-- **Erdős Problem #1052 (OPEN)**
Are there only finitely many unitary perfect numbers?
Known: 6, 60, 90, 87360, 146361946186458562560000 (only 5 known). -/
axiom erdos_1052_conjecture : { n : ℕ | IsUnitaryPerfect n }.Finite

end Erdos1052
