/-
  Aristotle targets for Erdos695 (Prime Chain Growth)
  Routine supporting lemmas for automated proof search.
  See Erdos695Problem.lean for the main formalization.

  These lemmas provide building blocks for prime chain analysis:
  - IsPrimeChain and ChainDivisibility basic properties
  - Prime chain monotonicity and lower bounds
  - Real.rpow helpers for p_k^(1/k) → ∞
  - Dirichlet's theorem consequence (prime congruent to 1)
  - Arithmetic in prime chains
-/
import Mathlib

open Filter Finset Real

namespace Erdos695.Aristotle

/-
  ## Section 1: IsPrimeChain Properties
-/

def IsPrimeChain (p : ℕ → ℕ) : Prop :=
  StrictMono p ∧ (∀ i, (p i).Prime) ∧ (∀ i, p (i + 1) % p i = 1)

/-- Prime chains are strictly increasing -/
lemma primeChain_strictMono (p : ℕ → ℕ) (h : IsPrimeChain p) : StrictMono p := h.1

/-- All elements of a prime chain are prime -/
lemma primeChain_all_prime (p : ℕ → ℕ) (h : IsPrimeChain p) (i : ℕ) : (p i).Prime :=
  h.2.1 i

/-- All elements of a prime chain are ≥ 2 -/
lemma primeChain_ge_two (p : ℕ → ℕ) (h : IsPrimeChain p) (i : ℕ) : p i ≥ 2 :=
  (h.2.1 i).two_le

/-- p(i+1) > p(i) in a prime chain -/
lemma primeChain_next_gt (p : ℕ → ℕ) (h : IsPrimeChain p) (i : ℕ) : p (i + 1) > p i :=
  h.1 (Nat.lt_succ_self i)

/-- p(i+1) ≥ p(i) + 1 in a prime chain (StrictMono) -/
lemma primeChain_next_ge_double (p : ℕ → ℕ) (h : IsPrimeChain p) (i : ℕ) :
    p (i + 1) ≥ p i + 1 := by
  have := h.1 (show i < i + 1 by omega)
  omega

/-
  ## Section 2: ChainDivisibility
-/

def ChainDivisibility (p : ℕ → ℕ) : Prop :=
  ∀ i, p i ∣ (p (i + 1) - 1)

/-- If p(i+1) % p(i) = 1 then p(i) | p(i+1) - 1 -/
lemma mod_one_implies_dvd (p q : ℕ) (h : q % p = 1) (hq : q ≥ 1) : p ∣ q - 1 := by
  -- Keep the nonlinear product `p * (q / p)` as a single atom so `omega` stays linear.
  have hdm : p * (q / p) + q % p = q := Nat.div_add_mod q p
  rw [h] at hdm
  exact ⟨q / p, by omega⟩

/-- Chain congruence implies divisibility -/
lemma chain_cong_to_dvd (p : ℕ → ℕ) (hprime : ∀ i, (p i).Prime)
    (hcong : ∀ i, p (i + 1) % p i = 1) : ChainDivisibility p := fun i =>
  mod_one_implies_dvd _ _ (hcong i) (hprime (i + 1)).pos

/-
  ## Section 3: Real.rpow Helpers for Growth Rate
-/

/-- p^(1/k) → ∞ iff p grows super-exponentially.
    Both directions use the rpow identity ((p k)^(1/k))^k = p k for k ≥ 1. -/
lemma rpow_tendsto_atTop_iff (p : ℕ → ℕ) :
    Filter.Tendsto (fun k => (p k : ℝ) ^ (1 / (k : ℝ))) Filter.atTop Filter.atTop ↔
    ∀ c : ℝ, c > 1 → ∀ᶠ k in Filter.atTop, (p k : ℝ) > c ^ k := by
  -- Helper: ((p k)^{1/k})^k = p k for k ≥ 1 (rpow identity)
  have rpow_inv_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) (hk : k ≠ 0) :
      (x ^ ((1 : ℝ) / (k : ℝ))) ^ k = x := by
    rw [← Real.rpow_natCast (x ^ _) k, ← Real.rpow_mul hx,
        one_div, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hk), Real.rpow_one]
  constructor
  · -- (→) tendsto to ∞ implies p k > c^k eventually, for each c > 1
    intro htend c hc
    rw [Filter.tendsto_atTop_atTop] at htend
    obtain ⟨k₀, hk₀⟩ := htend (c + 1)
    rw [Filter.eventually_atTop]
    refine ⟨max k₀ 1, fun k hk => ?_⟩
    have hkne : k ≠ 0 := by omega
    have hpk_pos : (0 : ℝ) ≤ (p k : ℝ) := Nat.cast_nonneg _
    have hc0 : (0 : ℝ) ≤ c := le_of_lt (lt_trans one_pos hc)
    -- (p k)^(1/k) ≥ c + 1 > c
    have hkth : c < (p k : ℝ) ^ (1 / (k : ℝ)) := by
      have := hk₀ k (by omega : k₀ ≤ k); linarith
    calc (c : ℝ) ^ k < ((p k : ℝ) ^ (1 / (k : ℝ))) ^ k :=
          pow_lt_pow_left₀ hkth hc0 hkne
      _ = (p k : ℝ) := rpow_inv_pow _ hpk_pos k hkne
  · -- (←) p k > c^k eventually (each c > 1) implies kthRoot tends to ∞
    intro h
    rw [Filter.tendsto_atTop_atTop]
    intro b
    have hc2 : (max b 2 : ℝ) > 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    obtain ⟨k₀, hk₀⟩ := Filter.eventually_atTop.mp (h (max b 2) hc2)
    refine ⟨max k₀ 1, fun k hk => ?_⟩
    have hkne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hgt := hk₀ k (by omega)
    calc (p k : ℝ) ^ ((1 : ℝ) / (k : ℝ))
        ≥ ((max b 2 : ℝ) ^ (k : ℕ)) ^ ((1 : ℝ) / (k : ℝ)) := by
          apply Real.rpow_le_rpow (by positivity) (le_of_lt hgt)
          positivity
      _ = max b 2 := by
          rw [← Real.rpow_natCast (max b 2 : ℝ) k,
              ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ max b 2),
              show (↑k : ℝ) * ((1 : ℝ) / (k : ℝ)) = 1 from mul_one_div_cancel hkne,
              Real.rpow_one]
      _ ≥ b := le_max_left _ _

/-- For c > 1, c^k → ∞ -/
lemma pow_tendsto_atTop (c : ℝ) (hc : c > 1) :
    Filter.Tendsto (fun k : ℕ => c ^ k) Filter.atTop Filter.atTop :=
  tendsto_pow_atTop_atTop_of_one_lt hc

/-- rpow is monotone: if a ≤ b and r ≥ 0 then a^r ≤ b^r -/
lemma rpow_mono (a b : ℝ) (r : ℝ) (ha : 0 ≤ a) (hr : 0 ≤ r) (h : a ≤ b) :
    a ^ r ≤ b ^ r := Real.rpow_le_rpow ha h hr

/-- (p k : ℝ)^(1/k) ≥ 2 for k ≥ 1 when p k ≥ 2^k -/
lemma rpow_ge_two_of_exp_bound (p : ℕ → ℕ) (k : ℕ) (hk : k ≥ 1)
    (h : p k ≥ 2 ^ k) : (p k : ℝ) ^ (1 / (k : ℝ)) ≥ 2 := by
  have hpk : (2 : ℝ) ^ k ≤ (p k : ℝ) := by exact_mod_cast h
  have h2k_rpow : ((2 : ℝ) ^ k) ^ (1 / (k : ℝ)) = 2 := by
    rw [← Real.rpow_natCast 2 k, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
    have hk_pos : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [mul_one_div_cancel hk_pos]
    simp [Real.rpow_one]
  calc (2 : ℝ) = ((2 : ℝ) ^ k) ^ (1 / (k : ℝ)) := h2k_rpow.symm
    _ ≤ (p k : ℝ) ^ (1 / (k : ℝ)) :=
        rpow_mono _ _ _ (by positivity) (by positivity) hpk

/-
  ## Section 4: Dirichlet Consequence
-/

/-- For any prime p, there exists a prime q with q ≡ 1 (mod p).
    This is a consequence of Dirichlet's theorem: since gcd(1, p) = 1, there are
    infinitely many primes q ≡ 1 (mod p). We extract one via
    `Nat.forall_exists_prime_gt_and_modEq`. -/
lemma prime_cong_one_exists (p : ℕ) (hp : p.Prime) : ∃ q : ℕ, q.Prime ∧ q % p = 1 := by
  have hcop : Nat.Coprime 1 p := Nat.coprime_one_left p
  -- `forall_exists_prime_gt_and_modEq 0 hp.ne_zero hcop : ∃ q > 0, q.Prime ∧ q ≡ 1 [MOD p]`
  obtain ⟨q, -, hq_prime, hq_mod⟩ := Nat.forall_exists_prime_gt_and_modEq 0 hp.ne_zero hcop
  refine ⟨q, hq_prime, ?_⟩
  -- `Nat.ModEq p q 1` is defeq to `q % p = 1 % p`; reduce `1 % p` using `p > 1`
  have hmod : q % p = 1 % p := hq_mod
  rwa [Nat.mod_eq_of_lt hp.one_lt] at hmod

/-- Any prime q ≡ 1 (mod p) satisfies q > p -/
lemma smallest_cong_prime_gt (p : ℕ) (hp : p.Prime) (q : ℕ) (hq : q.Prime)
    (hmod : q % p = 1) : q > p := by
  rcases Nat.lt_or_ge q p with hlt | hge
  · -- q < p → q % p = q → q = 1, not prime
    rw [Nat.mod_eq_of_lt hlt] at hmod
    exact absurd hmod hq.one_lt.ne'
  · -- q ≥ p: rule out q = p, so q > p
    rcases eq_or_lt_of_le hge with heq | hgt
    · -- heq : p = q, then q % p = p % p = 0 ≠ 1
      rw [← heq, Nat.mod_self] at hmod
      exact absurd hmod (by decide)
    · exact hgt

end Erdos695.Aristotle
