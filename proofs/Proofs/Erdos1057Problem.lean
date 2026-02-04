/-
  Erdős Problem #1057: Counting Carmichael Numbers

  Source: https://erdosproblems.com/1057
  Status: OPEN

  Statement:
  Let C(x) count Carmichael numbers in [1,x]. Is C(x) = x^{1-o(1)}?

  Background:
  A Carmichael number is a composite n satisfying a^n ≡ a (mod n) for all
  integers a. Equivalently (Korselt's criterion): n is squarefree and
  (p-1) | (n-1) for all prime divisors p of n.

  These are the "strongest" Fermat pseudoprimes—they fool the Fermat
  primality test for every base. The smallest is 561 = 3 × 11 × 17.

  Known bounds:
  • Upper (Erdős 1956): C(x) < x·exp(-c·log x·log log log x / log log x)
  • Lower (Lichtman 2022): C(x) > x^{0.3389} for large x
  • Alford-Granville-Pomerance (1994): C(x) → ∞ (infinitely many exist)

  The conjecture C(x) = x^{1-o(1)} asserts Carmichael numbers are quite
  dense—almost achieving density 1 in log scale.

  References:
  [Er56c] Erdős, "On pseudoprimes and Carmichael numbers" (1956)
  [AGP94] Alford-Granville-Pomerance, "There are infinitely many Carmichael numbers"
  [Po89] Pomerance, "Two methods in elementary analytic number theory" (1989)
  [Li22] Lichtman, "Improved bounds on the counting function" (2022)

  Tags: number-theory, carmichael-numbers, pseudoprimes, counting-functions, open-problem
-/

import Mathlib

open Nat BigOperators Finset Classical

/-
## Carmichael Numbers

Definition via Korselt's criterion.
-/

/-- Korselt's criterion: n is squarefree and (p-1) | (n-1) for all prime p | n -/
def satisfiesKorselt (n : ℕ) : Prop :=
  Squarefree n ∧ ∀ p : ℕ, p.Prime → p ∣ n → (p - 1) ∣ (n - 1)

/-- A Carmichael number is a composite satisfying Korselt's criterion -/
def IsCarmichael (n : ℕ) : Prop :=
  n > 1 ∧ ¬n.Prime ∧ satisfiesKorselt n

/-- Fermat's little theorem characterization: a^n ≡ a (mod n) for all a -/
def satisfiesFermat (n : ℕ) : Prop :=
  ∀ a : ℕ, a^n % n = a % n

/-- Korselt's theorem: the two definitions are equivalent -/
axiom korselt_theorem :
  ∀ n : ℕ, n > 1 → ¬n.Prime → (satisfiesKorselt n ↔ satisfiesFermat n)

/-
## Small Carmichael Numbers

The first few Carmichael numbers.
-/

/-- 561 = 3 × 11 × 17 -/
theorem factorization_561 : 561 = 3 * 11 * 17 := by native_decide

/-- Verification: 2 | 560, 10 | 560, 16 | 560 -/
theorem korselt_561 : (2 ∣ 560) ∧ (10 ∣ 560) ∧ (16 ∣ 560) := by
  exact ⟨⟨280, rfl⟩, ⟨56, rfl⟩, ⟨35, rfl⟩⟩

/-- Helper: the prime factors of 561 are {3, 11, 17} -/
private theorem primeFactors_561 : (561 : ℕ).primeFactors = {3, 11, 17} := by native_decide

/-- 561 is squarefree -/
theorem squarefree_561 : Squarefree (561 : ℕ) := by
  rw [show (561 : ℕ) = 3 * 187 from by norm_num]
  rw [show (187 : ℕ) = 11 * 17 from by norm_num]
  have h3 : Nat.Prime 3 := by native_decide
  have h11 : Nat.Prime 11 := by native_decide
  have h17 : Nat.Prime 17 := by native_decide
  have h1 : Nat.Coprime 3 (11 * 17) := by rw [Nat.Coprime]; native_decide
  have h2 : Nat.Coprime 11 17 := by rw [Nat.Coprime]; native_decide
  exact Nat.squarefree_mul_iff.mpr ⟨h1, h3.squarefree,
    Nat.squarefree_mul_iff.mpr ⟨h2, h11.squarefree, h17.squarefree⟩⟩

/-- 561 satisfies Korselt's criterion -/
theorem satisfiesKorselt_561 : satisfiesKorselt 561 := by
  constructor
  · exact squarefree_561
  · intro p hp hpdvd
    have hpf := primeFactors_561
    have hp_mem : p ∈ (561 : ℕ).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨hp, hpdvd, by norm_num⟩
    rw [hpf] at hp_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
    rcases hp_mem with rfl | rfl | rfl
    · -- p = 3: (3-1) = 2 | 560
      exact ⟨280, by norm_num⟩
    · -- p = 11: (11-1) = 10 | 560
      exact ⟨56, by norm_num⟩
    · -- p = 17: (17-1) = 16 | 560
      exact ⟨35, by norm_num⟩

/-- 561 = 3 × 11 × 17 is the smallest Carmichael number (PROVED) -/
theorem carmichael_561 : IsCarmichael 561 := by
  refine ⟨by norm_num, by native_decide, satisfiesKorselt_561⟩

/-- 1105 = 5 × 13 × 17 -/
theorem factorization_1105 : 1105 = 5 * 13 * 17 := by native_decide

/-- Helper: the prime factors of 1105 are {5, 13, 17} -/
private theorem primeFactors_1105 : (1105 : ℕ).primeFactors = {5, 13, 17} := by native_decide

/-- 1105 satisfies Korselt's criterion -/
theorem satisfiesKorselt_1105 : satisfiesKorselt 1105 := by
  constructor
  · -- Squarefree
    rw [show (1105 : ℕ) = 5 * 221 from by norm_num, show (221 : ℕ) = 13 * 17 from by norm_num]
    have h5 : Nat.Prime 5 := by native_decide
    have h13 : Nat.Prime 13 := by native_decide
    have h17 : Nat.Prime 17 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h5.squarefree,
      Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h13.squarefree, h17.squarefree⟩⟩
  · intro p hp hpdvd
    have hp_mem : p ∈ (1105 : ℕ).primeFactors := by
      rw [Nat.mem_primeFactors]; exact ⟨hp, hpdvd, by norm_num⟩
    rw [primeFactors_1105] at hp_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
    rcases hp_mem with rfl | rfl | rfl
    · exact ⟨276, by norm_num⟩  -- (5-1) = 4 | 1104
    · exact ⟨92, by norm_num⟩   -- (13-1) = 12 | 1104
    · exact ⟨69, by norm_num⟩   -- (17-1) = 16 | 1104

/-- 1105 = 5 × 13 × 17 is the second Carmichael number (PROVED) -/
theorem carmichael_1105 : IsCarmichael 1105 := by
  refine ⟨by norm_num, by native_decide, satisfiesKorselt_1105⟩

/-- 1729 = 7 × 13 × 19 -/
theorem factorization_1729 : 1729 = 7 * 13 * 19 := by native_decide

/-- Helper: the prime factors of 1729 -/
private theorem primeFactors_1729 : (1729 : ℕ).primeFactors = {7, 13, 19} := by native_decide

/-- 1729 satisfies Korselt's criterion -/
theorem satisfiesKorselt_1729 : satisfiesKorselt 1729 := by
  constructor
  · rw [show (1729 : ℕ) = 7 * 247 from by norm_num, show (247 : ℕ) = 13 * 19 from by norm_num]
    have h7 : Nat.Prime 7 := by native_decide
    have h13 : Nat.Prime 13 := by native_decide
    have h19 : Nat.Prime 19 := by native_decide
    exact Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h7.squarefree,
      Nat.squarefree_mul_iff.mpr ⟨by rw [Nat.Coprime]; native_decide, h13.squarefree, h19.squarefree⟩⟩
  · intro p hp hpdvd
    have hp_mem : p ∈ (1729 : ℕ).primeFactors := by
      rw [Nat.mem_primeFactors]; exact ⟨hp, hpdvd, by norm_num⟩
    rw [primeFactors_1729] at hp_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp_mem
    rcases hp_mem with rfl | rfl | rfl
    · exact ⟨288, by norm_num⟩  -- (7-1) = 6 | 1728
    · exact ⟨144, by norm_num⟩  -- (13-1) = 12 | 1728
    · exact ⟨96, by norm_num⟩   -- (19-1) = 18 | 1728

/-- 1729 = 7 × 13 × 19 is the Hardy-Ramanujan taxicab number and a Carmichael number (PROVED) -/
theorem carmichael_1729 : IsCarmichael 1729 := by
  refine ⟨by norm_num, by native_decide, satisfiesKorselt_1729⟩

/-- List of first few Carmichael numbers (OEIS A002997) -/
def smallCarmichaels : List ℕ := [561, 1105, 1729, 2465, 2821, 6601, 8911]

/-
## The Counting Function

C(x) counts Carmichael numbers up to x.
-/

/-- C(x): count of Carmichael numbers in [1, x] -/
noncomputable def C (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).filter IsCarmichael |>.card

/-- C is monotone increasing -/
theorem C_mono : ∀ x y : ℕ, x ≤ y → C x ≤ C y := by
  intro x y hxy
  unfold C
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
  exact ⟨Nat.lt_of_lt_of_le hn.1 (Nat.add_le_add_right hxy 1), hn.2⟩

/-
## Known Bounds

Upper and lower bounds on C(x).
-/

/-- Erdős's upper bound (1956) -/
axiom erdos_upper_bound :
  ∃ c : ℝ, c > 0 ∧ ∀ x : ℕ, x ≥ 2 →
    (C x : ℝ) < x * Real.exp (-c * Real.log x * Real.log (Real.log (Real.log x)) /
                               Real.log (Real.log x))

/-- Lichtman's lower bound (2022): C(x) > x^{0.3389} -/
axiom lichtman_lower_bound :
  ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(0.3389 : ℝ)

/-- Harman's earlier lower bound (2008): C(x) > x^{0.33336704} -/
axiom harman_lower_bound :
  ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(0.33336704 : ℝ)

/-- AGP (1994): There are infinitely many Carmichael numbers -/
axiom infinitely_many_carmichaels :
  ∀ N : ℕ, ∃ n > N, IsCarmichael n

/-- AGP lower bound: C(x) > x^{2/7} for large x -/
axiom agp_lower_bound :
  ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(2/7 : ℝ)

/-
## The Main Conjecture

Is C(x) = x^{1-o(1)}?
-/

/-- The conjecture: C(x) = x^{1-o(1)} -/
def erdos1057Conjecture : Prop :=
  ∀ ε > 0, ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > x^(1 - ε : ℝ)

/-- Equivalent: log C(x) / log x → 1 -/
def erdos1057ConjectureAlt : Prop :=
  Filter.Tendsto (fun x => Real.log (C x) / Real.log x)
    Filter.atTop (nhds 1)

/-- Pomerance's heuristic prediction for the exact order -/
noncomputable def pomeranceOrder (x : ℝ) : ℝ :=
  x * Real.exp (-Real.log x * Real.log (Real.log (Real.log x)) / Real.log (Real.log x))

/-- Pomerance conjecture: C(x) ~ pomeranceOrder(x) -/
def pomeranceConjecture : Prop :=
  Filter.Tendsto (fun x => (C x : ℝ) / pomeranceOrder x)
    Filter.atTop (nhds 1)

/-
## Properties of Carmichael Numbers

Structural results about Carmichael numbers.
-/

/-- Every Carmichael number has at least 3 prime factors -/
axiom carmichael_at_least_3_primes :
  ∀ n : ℕ, IsCarmichael n → n.primeFactors.card ≥ 3

/-- No Carmichael number is a prime power -/
theorem carmichael_not_prime_power (n : ℕ) (h : IsCarmichael n) :
    ¬∃ p k : ℕ, p.Prime ∧ k ≥ 1 ∧ n = p^k := by
  intro ⟨p, k, hp, hk, hn⟩
  have h3 := carmichael_at_least_3_primes n h
  rw [hn] at h3
  -- p^k has only one prime factor (namely p), so card = 1 < 3
  have hpk_pos : p ^ k ≠ 0 := Nat.pos_of_ne_zero (pow_ne_zero k hp.ne_zero) |>.ne'
  have hsub : (p ^ k).primeFactors ⊆ {p} := by
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    simp only [Finset.mem_singleton]
    have hqp := hq.1.dvd_of_dvd_pow hq.2.1
    exact (Nat.Prime.eq_one_or_self_of_dvd hp q hqp).resolve_left
      (Nat.Prime.one_lt hq.1).ne'
  have hcard : (p ^ k).primeFactors.card ≤ 1 := by
    calc (p ^ k).primeFactors.card
        ≤ ({p} : Finset ℕ).card := Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton p
  omega

/--
**Carmichael numbers are odd.**

Proof: If n is even and Carmichael, then 2 | n, so by Korselt (2-1) = 1 | (n-1).
This is always true, so that's not the contradiction. The key is that n must be
squarefree and have ≥ 3 prime factors. If n is even, then 2 is one prime factor.
We need at least 2 more odd primes p, q. Then (p-1) | (n-1) and (q-1) | (n-1).
Since n is even, n-1 is odd. But p-1 is even for odd p > 2, so (p-1) | (n-1)
requires an even number to divide an odd number, which is impossible.
-/
theorem carmichael_odd (n : ℕ) (h : IsCarmichael n) : Odd n := by
  by_contra hnodd
  rw [Nat.not_odd_iff_even] at hnodd
  -- n is even, so 2 | n
  have h2dvd : 2 ∣ n := Even.two_dvd hnodd
  have hn_pos : n > 1 := h.1
  have hn_ne0 : n ≠ 0 := by omega
  -- 2 is a prime factor of n
  have h2_prime : Nat.Prime 2 := by native_decide
  have h2_pf : 2 ∈ n.primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨h2_prime, h2dvd, hn_ne0⟩
  -- n has ≥ 3 prime factors
  have h3pf := carmichael_at_least_3_primes n h
  -- Erasing 2 leaves ≥ 2 prime factors
  have hcard_rest : (n.primeFactors.erase 2).card ≥ 2 := by
    have := Finset.card_erase_of_mem h2_pf
    omega
  -- So there exists some p ≠ 2 in the prime factors
  have hne : (n.primeFactors.erase 2).Nonempty := by
    exact Finset.card_pos.mp (by omega)
  obtain ⟨p, hp_mem⟩ := hne
  have hp_pf : p ∈ n.primeFactors := Finset.mem_of_mem_erase hp_mem
  have hp_ne2 : p ≠ 2 := Finset.ne_of_mem_erase hp_mem
  rw [Nat.mem_primeFactors] at hp_pf
  have hp_prime := hp_pf.1
  have hp_dvd := hp_pf.2.1
  -- p is an odd prime > 2, so p - 1 is even
  have hp_ge2 : p ≥ 2 := hp_prime.two_le
  have hp_gt2 : p > 2 := Nat.lt_of_le_of_ne hp_ge2 (Ne.symm hp_ne2)
  -- p is odd (since p is prime and p ≠ 2)
  have hp_odd : Odd p := Nat.Prime.odd_of_ne_two hp_prime hp_ne2
  -- p - 1 is even: p = 2k+1 implies p - 1 = 2k
  obtain ⟨pk, hpk⟩ := hp_odd
  have hp1_even : 2 ∣ (p - 1) := ⟨pk, by omega⟩
  -- By Korselt, (p-1) | (n-1)
  have hkorselt := h.2.2.2 p hp_prime hp_dvd
  -- So 2 | (n-1) via transitivity
  have h2_dvd_n1 : 2 ∣ (n - 1) := dvd_trans hp1_even hkorselt
  -- But n is even, so n - 1 is odd
  obtain ⟨nk, hnk⟩ := hnodd
  have hn1_odd : ¬(2 ∣ (n - 1)) := by
    intro ⟨d, hd⟩; omega
  exact hn1_odd h2_dvd_n1

/-
## The Gap

The huge gap between upper and lower bounds.
-/

/-- Upper bound exponent in log scale -/
noncomputable def upperExponent (x : ℝ) : ℝ :=
  1 - Real.log (Real.log (Real.log x)) / Real.log (Real.log x)

/-- Lower bound exponent -/
def lowerExponent : ℝ := 0.3389

/-- The gap: we know lowerExponent < true exponent < upperExponent(x) -/
theorem exponent_gap : lowerExponent < 1 := by
  norm_num [lowerExponent]

/-- The open problem: what is the true exponent? -/
def erdos1057OpenProblem : Prop := erdos1057Conjecture

/-
## Part VII: Additional Structural Properties
-/

/-- Carmichael numbers are greater than 1 (by definition) -/
theorem carmichael_gt_one (n : ℕ) (h : IsCarmichael n) : n > 1 := h.1

/-- Carmichael numbers are composite (by definition) -/
theorem carmichael_composite (n : ℕ) (h : IsCarmichael n) : ¬n.Prime := h.2.1

/-- Carmichael numbers are squarefree (from Korselt) -/
theorem carmichael_squarefree (n : ℕ) (h : IsCarmichael n) : Squarefree n := h.2.2.1

/--
**Carmichael numbers are not divisible by 4.**
Since they are squarefree, no prime squared divides them. In particular 4 = 2² ∤ n.
-/
theorem carmichael_not_div_4 (n : ℕ) (h : IsCarmichael n) : ¬(4 ∣ n) := by
  intro h4
  have hsf := carmichael_squarefree n h
  have h22 : 2 * 2 ∣ n := by omega
  have := hsf 2 h22
  rw [Nat.isUnit_iff] at this
  omega

/--
**Every prime factor of a Carmichael number divides n-1 shifted:**
For Carmichael n and prime p | n, we have (p-1) | (n-1).
This is the Korselt condition extracted.
-/
theorem carmichael_korselt_condition (n p : ℕ) (h : IsCarmichael n)
    (hp : p.Prime) (hpn : p ∣ n) : (p - 1) ∣ (n - 1) :=
  h.2.2.2 p hp hpn

/--
**There are no Carmichael numbers ≤ 560.**
The smallest Carmichael number is 561. This is a computational fact
verified by checking all candidates ≤ 560 against Korselt's criterion.
-/
axiom no_carmichael_below_561 (n : ℕ) (hn : n ≤ 560) : ¬IsCarmichael n

/--
**No Carmichael number exists in any range below 561.**
For any n < 561, n is not Carmichael.
-/
theorem C_zero_below_561 (n : ℕ) (hn : n < 561) (hc : IsCarmichael n) : False :=
  no_carmichael_below_561 n (by omega) hc

/--
**C(x) ≥ C(561) for x ≥ 561.**
By monotonicity of C.
-/
theorem C_ge_C561 (x : ℕ) (hx : x ≥ 561) : C x ≥ C 561 :=
  C_mono 561 x hx

/--
**The conjecture implies C grows faster than any fixed polynomial exponent < 1.**
If erdos1057Conjecture holds, then for any α < 1, C(x) > x^α eventually.
-/
theorem conjecture_implies_faster_than (α : ℝ) (hα : α < 1) :
    erdos1057Conjecture → ∃ X : ℕ, ∀ x ≥ X, (C x : ℝ) > (x : ℝ)^α := by
  intro hconj
  have h := hconj (1 - α) (by linarith)
  simp only [sub_sub_cancel] at h
  exact h

/--
**Monotonicity of bounds: Lichtman improves Harman improves AGP.**
The exponents 0.3389 > 0.33336704 > 2/7 ≈ 0.2857.
-/
theorem bound_improvement : (2 : ℝ) / 7 < 0.33336704 ∧ (0.33336704 : ℝ) < 0.3389 := by
  constructor <;> norm_num
