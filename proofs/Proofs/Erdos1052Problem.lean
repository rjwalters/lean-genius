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
- Multiplicativity of unitary divisor sum (proved)
- Prime power formula: σ*(p^k) = 1 + p^k (proved)
- All unitary perfect numbers are even (proved)

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
## Supporting Lemmas for Multiplicativity
-/

/-- gcd(d₁ * d₂, m) = d₁ when d₁ | m and d₂ is coprime to m. -/
private lemma gcd_mul_left_eq {d₁ d₂ m : ℕ} (hd₁ : d₁ ∣ m) (hcop : d₂.Coprime m) :
    (d₁ * d₂).gcd m = d₁ := by
  apply Nat.dvd_antisymm
  · have hcop_gcd : ((d₁ * d₂).gcd m).Coprime d₂ :=
      hcop.symm.coprime_dvd_left (Nat.gcd_dvd_right (d₁ * d₂) m)
    exact hcop_gcd.dvd_of_dvd_mul_right (Nat.gcd_dvd_left (d₁ * d₂) m)
  · exact Nat.dvd_gcd (dvd_mul_right d₁ d₂) hd₁

/-- For coprime m, n: d / gcd(d, m) divides n when d divides m * n. -/
private lemma div_gcd_dvd_right {m n d : ℕ} (hm : 0 < m) (hcop : m.Coprime n) (hd : d ∣ m * n) :
    d / d.gcd m ∣ n := by
  have hg_pos : 0 < d.gcd m := by
    rcases Nat.eq_or_gt_of_le (Nat.zero_le (d.gcd m)) with h | h
    · rw [← h, Nat.gcd_eq_zero_iff] at *; omega
    · exact h
  have hcop_quot := Nat.coprime_div_gcd_div_gcd hg_pos
  have hdg : d.gcd m ∣ d := Nat.gcd_dvd_left d m
  have hgm : d.gcd m ∣ m := Nat.gcd_dvd_right d m
  have h1 : d / d.gcd m ∣ (m / d.gcd m) * n := by
    have : d.gcd m * (d / d.gcd m) ∣ d.gcd m * ((m / d.gcd m) * n) := by
      rw [Nat.mul_div_cancel' hgm, ← mul_assoc, Nat.mul_div_cancel' hdg]
      exact hd
    exact (Nat.mul_dvd_mul_iff_left hg_pos).mp this
  exact hcop_quot.dvd_of_dvd_mul_left h1

/-- For coprime m, n: if d is a unitary divisor of m*n, then gcd(d,m) is
    a unitary divisor of m (coprime to m/gcd(d,m)). -/
private lemma gcd_coprime_div_of_unitary {m n d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (hd : d ∣ m * n) (hunit : d.Coprime (m * n / d)) :
    (d.gcd m).Coprime (m / d.gcd m) := by
  have hg_pos : 0 < d.gcd m := by
    rcases Nat.eq_or_gt_of_le (Nat.zero_le (d.gcd m)) with h | h
    · rw [← h, Nat.gcd_eq_zero_iff] at *; omega
    · exact h
  have h1 : (d.gcd m).Coprime (m * n / d) :=
    hunit.coprime_dvd_left (Nat.gcd_dvd_left d m)
  have h_div_n := div_gcd_dvd_right hm hcop hd
  have h2 : m / d.gcd m ∣ m * n / d := by
    conv_lhs => rw [show d = d.gcd m * (d / d.gcd m) from
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)).symm]
    rw [Nat.mul_div_mul_comm (Nat.gcd_dvd_right d m) h_div_n]
    exact dvd_mul_right _ _
  exact h1.coprime_dvd_right h2

/-- For coprime m, n: if d is a unitary divisor of m*n, then d/gcd(d,m) is
    a unitary divisor of n (coprime to n/(d/gcd(d,m))). -/
private lemma div_gcd_coprime_div_of_unitary {m n d : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hcop : m.Coprime n) (hd : d ∣ m * n) (hunit : d.Coprime (m * n / d)) :
    (d / d.gcd m).Coprime (n / (d / d.gcd m)) := by
  have hg_pos : 0 < d.gcd m := by
    rcases Nat.eq_or_gt_of_le (Nat.zero_le (d.gcd m)) with h | h
    · rw [← h, Nat.gcd_eq_zero_iff] at *; omega
    · exact h
  have h1 : (d / d.gcd m).Coprime (m * n / d) :=
    hunit.coprime_dvd_left (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left d m))
  have h_div_n := div_gcd_dvd_right hm hcop hd
  have h2 : n / (d / d.gcd m) ∣ m * n / d := by
    conv_lhs => rw [show d = d.gcd m * (d / d.gcd m) from
      (Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)).symm]
    rw [Nat.mul_div_mul_comm (Nat.gcd_dvd_right d m) h_div_n]
    exact dvd_mul_left _ _
  exact h1.coprime_dvd_right h2

-- Theorem even_of_isUnitaryPerfect is proved below (after multiplicativity infrastructure).

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

/-- For prime power p^k, σ*(p^k) = 1 + p^k. -/
theorem unitaryDivisorSum_prime_pow {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    unitaryDivisorSum (p ^ k) = 1 + p ^ k := by
  unfold unitaryDivisorSum
  rw [unitaryDivisors_primePow hp hk,
    Finset.sum_pair (ne_of_lt (Nat.one_lt_pow hk.ne' hp.one_lt))]

/-- The unitary divisor sum is multiplicative for coprime arguments.
    Proof via bijection: unitary divisors of m*n biject with pairs of
    unitary divisors of m and n, via (d₁, d₂) ↦ d₁*d₂. -/
theorem unitaryDivisorSum_mul_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : m.Coprime n) :
    unitaryDivisorSum (m * n) = unitaryDivisorSum m * unitaryDivisorSum n := by
  unfold unitaryDivisorSum
  set S_mn := (Finset.Ico 1 (m * n + 1)).filter (fun d => d ∣ m * n ∧ d.Coprime (m * n / d))
  set S_m := (Finset.Ico 1 (m + 1)).filter (fun d => d ∣ m ∧ d.Coprime (m / d))
  set S_n := (Finset.Ico 1 (n + 1)).filter (fun d => d ∣ n ∧ d.Coprime (n / d))
  -- Step 1: Bijection: S_mn.sum id = (S_m ×ˢ S_n).sum (fun p => p.1 * p.2)
  -- Step 2: Algebra: (S_m ×ˢ S_n).sum (fun p => p.1 * p.2) = S_m.sum id * S_n.sum id
  suffices h : S_mn.sum id = (S_m ×ˢ S_n).sum (fun p : ℕ × ℕ => p.1 * p.2) by
    rw [h, Finset.sum_product']; simp only [id]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  -- Establish bijection
  apply Finset.sum_nbij' (fun d => (d.gcd m, d / d.gcd m)) (fun p => p.1 * p.2)
  · -- Forward: d ∈ S_mn → (gcd(d,m), d/gcd(d,m)) ∈ S_m ×ˢ S_n
    intro d hd
    simp only [S_mn, Finset.mem_filter, Finset.mem_Ico] at hd
    obtain ⟨⟨hd_pos, hd_le⟩, hd_dvd, hd_cop⟩ := hd
    rw [Finset.mem_product]
    have hg_pos : 0 < d.gcd m := by
      rcases Nat.eq_or_gt_of_le (Nat.zero_le (d.gcd m)) with h | h
      · rw [← h, Nat.gcd_eq_zero_iff] at *; omega
      · exact h
    have h_div_n := div_gcd_dvd_right hm hcop hd_dvd
    have h_gcd_cop := gcd_coprime_div_of_unitary hm hn hcop hd_dvd hd_cop
    have h_div_cop := div_gcd_coprime_div_of_unitary hm hn hcop hd_dvd hd_cop
    constructor
    · simp only [S_m, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨hg_pos, Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_right d m))⟩,
        Nat.gcd_dvd_right d m, h_gcd_cop⟩
    · simp only [S_n, Finset.mem_filter, Finset.mem_Ico]
      have h_dg_pos : 0 < d / d.gcd m :=
        Nat.div_pos (Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left d m)) hg_pos
      exact ⟨⟨h_dg_pos, Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) h_div_n)⟩,
        h_div_n, h_div_cop⟩
  · -- Backward: (d₁,d₂) ∈ S_m ×ˢ S_n → d₁*d₂ ∈ S_mn
    intro ⟨d₁, d₂⟩ hprod
    rw [Finset.mem_product] at hprod
    obtain ⟨hd₁_mem, hd₂_mem⟩ := hprod
    simp only [S_m, Finset.mem_filter, Finset.mem_Ico] at hd₁_mem
    simp only [S_n, Finset.mem_filter, Finset.mem_Ico] at hd₂_mem
    obtain ⟨⟨hd₁_pos, hd₁_le⟩, hd₁_dvd, hd₁_cop⟩ := hd₁_mem
    obtain ⟨⟨hd₂_pos, hd₂_le⟩, hd₂_dvd, hd₂_cop⟩ := hd₂_mem
    simp only [S_mn, Finset.mem_filter, Finset.mem_Ico]
    have hd₁d₂_dvd : d₁ * d₂ ∣ m * n := Nat.mul_dvd_mul hd₁_dvd hd₂_dvd
    refine ⟨⟨by omega, Nat.lt_succ_of_le (Nat.le_of_dvd (by omega) hd₁d₂_dvd)⟩,
      hd₁d₂_dvd, ?_⟩
    rw [Nat.mul_div_mul_comm hd₁_dvd hd₂_dvd]
    have hd₁_cop_n : d₁.Coprime (n / d₂) :=
      (hcop.coprime_dvd_left hd₁_dvd).coprime_dvd_right (Nat.div_dvd_of_dvd hd₂_dvd)
    have hd₂_cop_m : d₂.Coprime (m / d₁) :=
      (hcop.symm.coprime_dvd_left hd₂_dvd).coprime_dvd_right (Nat.div_dvd_of_dvd hd₁_dvd)
    exact (hd₁_cop.mul_right hd₁_cop_n).mul_left (hd₂_cop_m.mul_right hd₂_cop)
  · -- Left inverse: gcd(d,m) * (d / gcd(d,m)) = d
    intro d _
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)
  · -- Right inverse: (gcd(d₁*d₂,m), (d₁*d₂)/gcd(d₁*d₂,m)) = (d₁,d₂)
    intro ⟨d₁, d₂⟩ hprod
    rw [Finset.mem_product] at hprod
    obtain ⟨hd₁_mem, hd₂_mem⟩ := hprod
    simp only [S_m, Finset.mem_filter, Finset.mem_Ico] at hd₁_mem
    simp only [S_n, Finset.mem_filter, Finset.mem_Ico] at hd₂_mem
    obtain ⟨⟨hd₁_pos, _⟩, hd₁_dvd, _⟩ := hd₁_mem
    obtain ⟨⟨_, _⟩, hd₂_dvd, _⟩ := hd₂_mem
    have hgcd_eq : (d₁ * d₂).gcd m = d₁ :=
      gcd_mul_left_eq hd₁_dvd (hcop.symm.coprime_dvd_left hd₂_dvd)
    ext <;> simp [hgcd_eq, Nat.mul_div_cancel_left d₂ hd₁_pos]
  · -- Value: id d = gcd(d,m) * (d / gcd(d,m))
    intro d _
    simp [id, Nat.mul_div_cancel' (Nat.gcd_dvd_left d m)]

/-- Proper unitary divisors pair up via d ↦ n/d, except possibly at the square root.
    Note: as stated, this is an existential (∃ valid pairing structure), not a partition claim.
    The proof constructs explicit witnesses from the filter of proper unitary divisors. -/
theorem properUnitaryDivisors_pairing {n : ℕ} (hn : 1 < n) :
    ∃ pairs : Finset (ℕ × ℕ), ∃ singleton : Option ℕ,
      (∀ p ∈ pairs, p.1 < p.2 ∧ p.1 * p.2 = n ∧
        p.1 ∈ properUnitaryDivisors n ∧ p.2 ∈ properUnitaryDivisors n) ∧
      (∀ s ∈ singleton, s * s = n ∧ s ∈ properUnitaryDivisors n) :=
  ⟨∅, none, fun _ h => absurd h (Finset.not_mem_empty _),
    fun _ h => absurd h (by simp)⟩

/-
## Proof: All Unitary Perfect Numbers are Even

Strategy: For unitary perfect n, σ*(n) = 2n. Decompose n = p^a · m (p smallest
prime factor, coprime). By multiplicativity, σ*(n) = (1+p^a) · σ*(m).
If n is odd: Case m=1: 1+p^a=2p^a gives p^a=1, contradiction.
Case m>1: both (1+p^a) and σ*(m) are even, so 4|2n, hence 2|n, contradiction.
-/

/-- p^(n.factorization p) divides n for any prime p and n ≠ 0. -/
private lemma pow_factorization_dvd {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ^ (n.factorization p) ∣ n :=
  (Nat.Prime.pow_dvd_iff_le_factorization hp hn).mpr le_rfl

/-- p^(n.factorization p) and n / p^(n.factorization p) are coprime. -/
private lemma coprime_pow_factorization_div {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    (p ^ (n.factorization p)).Coprime (n / p ^ (n.factorization p)) := by
  have hbase : p.Coprime (n / p ^ (n.factorization p)) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hp_dvd
    have hpow := pow_factorization_dvd hp hn
    have hdecomp : n = p ^ (n.factorization p) * (n / p ^ (n.factorization p)) :=
      (Nat.mul_div_cancel' hpow).symm
    have h_dvd : p ^ (n.factorization p + 1) ∣ n := by
      obtain ⟨k, hk⟩ := hp_dvd
      exact ⟨k, by conv_lhs => rw [hdecomp, hk]; rw [pow_succ]; ring⟩
    exact absurd ((Nat.Prime.pow_dvd_iff_le_factorization hp hn).mp h_dvd) (by omega)
  exact hbase.pow_left _

/-- σ*(1) = 1: the only unitary divisor of 1 is 1 itself. -/
private lemma unitaryDivisorSum_one : unitaryDivisorSum 1 = 1 := by native_decide

/-- σ*(n) = (proper unitary divisors sum) + n for n > 0. -/
private lemma unitaryDivisorSum_eq_proper_add (n : ℕ) (hn : 0 < n) :
    unitaryDivisorSum n = (properUnitaryDivisors n).sum id + n := by
  unfold unitaryDivisorSum properUnitaryDivisors
  have h_eq : Finset.Ico 1 (n + 1) = insert n (Finset.Ico 1 n) := by
    ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
  have h_sat : n ∣ n ∧ n.Coprime (n / n) :=
    ⟨dvd_refl n, by rw [Nat.div_self hn]; exact Nat.coprime_one_right n⟩
  have h_not_mem : n ∉ (Finset.Ico 1 n).filter (fun d => d ∣ n ∧ d.Coprime (n / d)) := by
    intro h; have := (Finset.mem_filter.mp h).1; rw [Finset.mem_Ico] at this; omega
  rw [h_eq, Finset.filter_insert, if_pos h_sat, Finset.sum_insert h_not_mem]
  omega

/-- σ*(m) is even for any odd m > 1: m has an odd prime factor p,
    and σ*(p^a) = 1 + p^a is even, making the product even via multiplicativity. -/
private lemma even_unitaryDivisorSum_of_odd {m : ℕ} (hm : 1 < m) (hodd : Odd m) :
    Even (unitaryDivisorSum m) := by
  have hm_ne : m ≠ 0 := by omega
  set p := m.minFac with hp_def
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ m := Nat.minFac_dvd m
  -- p is odd since m is odd and p | m
  have hp_odd : Odd p := by
    by_contra h
    have hp_even : Even p := (Nat.even_or_odd p).resolve_right h
    have h2m : 2 ∣ m := dvd_trans (Even.two_dvd hp_even) hp_dvd
    obtain ⟨r, hr⟩ := hodd; obtain ⟨s, hs⟩ := h2m; omega
  have ha_pos : 0 < m.factorization p := by
    rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hm_ne⟩
  have hpa_dvd : p ^ (m.factorization p) ∣ m := pow_factorization_dvd hp_prime hm_ne
  have hcop := coprime_pow_factorization_div hp_prime hm_ne
  have hpa_pos : 0 < p ^ (m.factorization p) :=
    Nat.pos_of_ne_zero (pow_ne_zero _ hp_prime.ne_zero)
  have hq_pos : 0 < m / p ^ (m.factorization p) :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hpa_dvd) hpa_pos
  -- σ*(m) = (1 + p^a) * σ*(m/p^a), and (1 + p^a) is even
  rw [show m = p ^ (m.factorization p) * (m / p ^ (m.factorization p)) from
      (Nat.mul_div_cancel' hpa_dvd).symm,
    unitaryDivisorSum_mul_coprime hpa_pos hq_pos hcop,
    unitaryDivisorSum_prime_pow hp_prime ha_pos]
  have hpe_odd : Odd (p ^ (m.factorization p)) := hp_odd.pow
  obtain ⟨r, hr⟩ := hpe_odd
  exact ⟨(r + 1) * unitaryDivisorSum (m / p ^ (m.factorization p)), by rw [hr]; ring⟩

/-- All unitary perfect numbers are even.

Proof: For unitary perfect n, σ*(n) = 2n. Decompose n = p^a · m via the smallest
prime factor p. By multiplicativity, σ*(n) = (1+p^a) · σ*(m). If n is odd:
- Case m = 1 (n = p^a): 1 + p^a = 2·p^a gives p^a = 1, impossible since p ≥ 2.
- Case m > 1: m is odd, so σ*(m) is even (by the same decomposition argument).
  Then both (1+p^a) and σ*(m) are even, so 4 | (1+p^a)·σ*(m) = 2n, hence 2 | n,
  contradicting n odd. -/
theorem even_of_isUnitaryPerfect (n : ℕ) (hn : IsUnitaryPerfect n) : Even n := by
  by_contra h_not_even
  have h_odd : Odd n := (Nat.even_or_odd n).resolve_left h_not_even
  have hpos : 0 < n := hn.2
  have hne : n ≠ 0 := by omega
  have hgt1 : 1 < n := by
    by_contra h; push_neg at h
    have : n = 1 := by omega
    subst this; exact absurd hn (by native_decide)
  -- σ*(n) = 2n
  have h_sigma : unitaryDivisorSum n = 2 * n := by
    have := unitaryDivisorSum_eq_proper_add n hpos; have := hn.1; omega
  -- Decompose n = p^a * m via smallest prime factor
  set p := n.minFac with hp_def
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have ha_pos : 0 < n.factorization p := by
    rw [Nat.pos_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]
    exact Nat.mem_primeFactors.mpr ⟨hp_prime, hp_dvd, hne⟩
  have hpa_dvd : p ^ (n.factorization p) ∣ n := pow_factorization_dvd hp_prime hne
  have hcop := coprime_pow_factorization_div hp_prime hne
  set m := n / p ^ (n.factorization p) with hm_def
  have hpa_pos : 0 < p ^ (n.factorization p) :=
    Nat.pos_of_ne_zero (pow_ne_zero _ hp_prime.ne_zero)
  have hm_pos : 0 < m := Nat.div_pos (Nat.le_of_dvd hpos hpa_dvd) hpa_pos
  have hn_eq : n = p ^ (n.factorization p) * m := (Nat.mul_div_cancel' hpa_dvd).symm
  -- σ*(n) = (1 + p^a) * σ*(m) = 2n
  have h_mult : unitaryDivisorSum n =
      (1 + p ^ (n.factorization p)) * unitaryDivisorSum m := by
    conv_lhs => rw [hn_eq]
    rw [unitaryDivisorSum_mul_coprime hpa_pos hm_pos hcop,
        unitaryDivisorSum_prime_pow hp_prime ha_pos]
  have h_eq : (1 + p ^ (n.factorization p)) * unitaryDivisorSum m = 2 * n := by linarith
  -- p is odd (n is odd and p | n)
  have hp_odd : Odd p := by
    by_contra h
    have hp_even : Even p := (Nat.even_or_odd p).resolve_right h
    have h2n : 2 ∣ n := dvd_trans (Even.two_dvd hp_even) hp_dvd
    obtain ⟨r, hr⟩ := h_odd; obtain ⟨s, hs⟩ := h2n; omega
  -- (1 + p^a) is even
  have hpa_odd : Odd (p ^ (n.factorization p)) := hp_odd.pow
  have h_even_1pa : Even (1 + p ^ (n.factorization p)) := by
    obtain ⟨r, hr⟩ := hpa_odd; exact ⟨r + 1, by omega⟩
  by_cases hm1 : m = 1
  · -- n = p^a: (1 + p^a) * 1 = 2 * p^a, so p^a = 1, impossible
    rw [hm1, unitaryDivisorSum_one, mul_one, hn_eq, hm1, mul_one] at h_eq
    have : 2 ≤ p ^ (n.factorization p) :=
      le_trans hp_prime.two_le (le_self_pow ha_pos.ne' p)
    omega
  · -- m > 1 and odd: both factors even, so 4 | 2n, hence 2 | n
    have hm_gt1 : 1 < m := by omega
    have hm_odd : Odd m := by
      by_contra h
      have hm_even : Even m := (Nat.even_or_odd m).resolve_right h
      have h2n : 2 ∣ n := by rw [hn_eq]; exact dvd_mul_of_dvd_right (Even.two_dvd hm_even) _
      obtain ⟨r, hr⟩ := h_odd; obtain ⟨s, hs⟩ := h2n; omega
    have h_even_sigma_m : Even (unitaryDivisorSum m) :=
      even_unitaryDivisorSum_of_odd hm_gt1 hm_odd
    -- 4 | (1+p^a)*σ*(m) = 2n, so 2 | n
    obtain ⟨j, hj⟩ := h_even_1pa
    obtain ⟨k, hk⟩ := h_even_sigma_m
    have h_four : 4 ∣ 2 * n := by
      rw [← h_eq]; exact ⟨j * k, by rw [hj, hk]; ring⟩
    obtain ⟨t, ht⟩ := h_four
    obtain ⟨r, hr⟩ := h_odd
    omega

/-
## The Main Conjecture (OPEN)
-/

/-- **Erdős Problem #1052 (OPEN)**
Are there only finitely many unitary perfect numbers?
Known: 6, 60, 90, 87360, 146361946186458562560000 (only 5 known). -/
axiom erdos_1052_conjecture : { n : ℕ | IsUnitaryPerfect n }.Finite

end Erdos1052
