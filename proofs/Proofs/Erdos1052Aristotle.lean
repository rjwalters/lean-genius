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
  unfold unitaryDivisorSum
  have hfilt : (Finset.Ico 1 (p + 1)).filter (fun d => d ∣ p ∧ d.Coprime (p / d)) = {1, p} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, _⟩, hdvd, _⟩
      exact hp.eq_one_or_self_of_dvd d hdvd
    · rintro (rfl | rfl)
      · exact ⟨⟨le_refl 1, by omega⟩, one_dvd p, Nat.coprime_one_left _⟩
      · exact ⟨⟨hp.one_le, by omega⟩, dvd_refl p, by rw [Nat.div_self hp.pos]; exact Nat.coprime_one_right _⟩
  rw [hfilt, Finset.sum_pair hp.one_lt.ne']

/-- If d > 1 and d ∣ p^k for prime p, then p ∣ d. -/
private theorem prime_dvd_of_dvd_prime_pow {p d k : ℕ} (hp : p.Prime) (hd : 1 < d) (hdvd : d ∣ p ^ k) :
    p ∣ d := by
  obtain ⟨q, hq_prime, hq_dvd_d⟩ := Nat.exists_prime_and_dvd hd.ne'
  have hq_dvd_pk : q ∣ p ^ k := dvd_trans hq_dvd_d hdvd
  have hqp : q = p := by
    have : q ∣ p := (hq_prime.dvd_of_dvd_pow hq_dvd_pk)
    rcases hp.eq_one_or_self_of_dvd q this with h | h
    · exact absurd h hq_prime.one_lt.ne'
    · exact h
  rw [hqp] at hq_dvd_d
  exact hq_dvd_d

/-- For a prime power p^k with k ≥ 1, σ*(p^k) = 1 + p^k.
    The only unitary divisors are 1 and p^k itself. -/
theorem unitaryDivisorSum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    unitaryDivisorSum (p ^ k) = 1 + p ^ k := by
  unfold unitaryDivisorSum
  have hpk_pos : 0 < p ^ k := Nat.pos_of_ne_zero (by positivity)
  have hfilt : (Finset.Ico 1 (p ^ k + 1)).filter (fun d => d ∣ p ^ k ∧ d.Coprime (p ^ k / d)) =
      {1, p ^ k} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd1, hd2⟩, hdvd, hcop⟩
      by_contra h
      push_neg at h
      obtain ⟨hd_ne1, hd_nepk⟩ := h
      have hd_gt1 : 1 < d := lt_of_le_of_ne hd1 (Ne.symm hd_ne1)
      have hd_lt_pk : d < p ^ k := lt_of_le_of_ne (by omega) hd_nepk
      -- p ∣ d since d > 1 and d ∣ p^k
      have hp_dvd_d : p ∣ d := prime_dvd_of_dvd_prime_pow hp hd_gt1 hdvd
      -- p ∣ (p^k/d) since p^k/d > 1 and p^k/d ∣ p^k
      have hnd_gt1 : 1 < p ^ k / d := by
        have h : p ^ k = d * (p ^ k / d) := (Nat.div_mul_cancel hdvd).symm
        have : p ^ k / d ≠ 0 := by intro h0; rw [h0, mul_zero] at h; omega
        have : p ^ k / d ≠ 1 := by intro h1; rw [h1, mul_one] at h; omega
        omega
      have hnd_dvd : p ^ k / d ∣ p ^ k := Nat.div_dvd_of_dvd hdvd
      have hp_dvd_nd : p ∣ p ^ k / d := prime_dvd_of_dvd_prime_pow hp hnd_gt1 hnd_dvd
      -- p ∣ gcd(d, p^k/d) = 1, contradiction
      have h3 : p ∣ Nat.gcd d (p ^ k / d) := Nat.dvd_gcd hp_dvd_d hp_dvd_nd
      rw [hcop] at h3
      exact absurd (Nat.le_of_dvd Nat.one_pos h3) (by omega)
    · rintro (rfl | rfl)
      · exact ⟨⟨le_refl 1, by omega⟩, one_dvd _, Nat.coprime_one_left _⟩
      · exact ⟨⟨hpk_pos, by omega⟩, dvd_refl _, by rw [Nat.div_self hpk_pos]; exact Nat.coprime_one_right _⟩
  rw [hfilt, Finset.sum_pair (Nat.one_lt_pow hk.ne' hp.one_lt |>.ne')]

/-- The number of proper unitary divisors of a prime is 1 (just {1}). -/
theorem card_properUnitaryDivisors_prime {p : ℕ} (hp : p.Prime) :
    (properUnitaryDivisors p).card = 1 := by
  unfold properUnitaryDivisors
  have hfilt : (Finset.Ico 1 p).filter (fun d => d ∣ p ∧ d.Coprime (p / d)) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, hd2⟩, hdvd, _⟩
      rcases hp.eq_one_or_self_of_dvd d hdvd with rfl | rfl
      · rfl
      · exact absurd hd2 (by omega)
    · rintro rfl
      exact ⟨⟨le_refl 1, hp.one_lt⟩, one_dvd p, Nat.coprime_one_left _⟩
  rw [hfilt, Finset.card_singleton]

/-- If d is a unitary divisor of n, then n/d is also a unitary divisor of n. -/
theorem unitary_complement_mem {n d : ℕ} (hn : 0 < n)
    (hd : d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))) :
    n / d ∈ (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d)) := by
  simp only [Finset.mem_filter, Finset.mem_Ico] at hd ⊢
  obtain ⟨⟨hd1, _⟩, hdvd, hcop⟩ := hd
  have hd_pos : 0 < d := by omega
  have hnd_dvd : n / d ∣ n := Nat.div_dvd_of_dvd hdvd
  have hnd_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdvd) hd_pos
  refine ⟨⟨hnd_pos, by omega⟩, hnd_dvd, ?_⟩
  -- Need: Coprime (n/d) (n / (n/d))
  -- Since d ∣ n, n = (n/d) * d, so n / (n/d) = d
  have hrewrite : n / (n / d) = d := by
    have h := Nat.div_mul_cancel hdvd  -- n / d * d = n
    rw [show n = n / d * d from h.symm]
    exact Nat.mul_div_cancel_left d hnd_pos
  rw [hrewrite]
  exact hcop.symm

/-- The unitary divisor sum of a product of two coprime numbers equals the product
    of their unitary divisor sums. This is the multiplicativity property. -/
theorem unitaryDivisorSum_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    unitaryDivisorSum (m * n) = unitaryDivisorSum m * unitaryDivisorSum n := by sorry

end Erdos1052Aristotle
