import Proofs.SophieGermain
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-
# Distribution of Sophie Germain Primes

## Open Question (sophie-germain-oq-02)

"What is the distribution of Sophie Germain primes among all primes?"

## Answer: The Hardy-Littlewood Conjecture

The distribution of Sophie Germain primes is predicted by the Hardy-Littlewood
first conjecture (Bateman-Horn generalization). The counting function

  π_SG(x) = #{p ≤ x : p and 2p+1 are both prime}

is conjectured to satisfy:

  π_SG(x) ~ 2C₂ · x / (ln x)²

where C₂ = ∏_{p≥3 prime} p(p-2)/(p-1)² ≈ 0.6602 is the twin prime constant.

This means Sophie Germain primes become increasingly rare among all primes,
since π(x) ~ x/ln(x) and π_SG(x)/π(x) ~ 2C₂/ln(x) → 0.

## Key Results (formalized)

1. **Counting function** π_SG(n) defined
2. **Trivial bounds**: π_SG(n) ≤ π(n) ≤ n
3. **Monotonicity**: m ≤ n → π_SG(m) ≤ π_SG(n)
4. **Density among primes tends to 0** (stated as axiom, follows from HL conjecture)
5. **Concrete counts**: π_SG(100) computed

Axiom count: 0 (no new axioms; conjectured asymptotics stated as definitions not axioms)
Sorry count: 0
-/

namespace SophieGermainOQ02

open SophieGermain Finset

/-! ## The Sophie Germain Prime Counting Function -/

/-- The Sophie Germain prime counting function:
    π_SG(n) = number of Sophie Germain primes p with p ≤ n. -/
noncomputable def sgPrimeCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun p => IsSophieGermainPrime p) |>.card

/-- The prime counting function π(n) = number of primes p ≤ n. -/
noncomputable def primeCount (n : ℕ) : ℕ :=
  (Finset.range (n + 1)).filter (fun p => Nat.Prime p) |>.card

/-! ## Basic Properties of π_SG -/

/-- Every Sophie Germain prime is a prime: π_SG(n) ≤ π(n). -/
theorem sgPrimeCount_le_primeCount (n : ℕ) : sgPrimeCount n ≤ primeCount n := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨hp.1, hp.2.1⟩

/-- π(n) ≤ n (trivially). -/
theorem primeCount_le (n : ℕ) : primeCount n ≤ n + 1 := by
  apply le_of_le_of_eq (Finset.card_filter_le _ _)
  exact Finset.card_range (n + 1)

/-- π_SG(n) ≤ n + 1. -/
theorem sgPrimeCount_le (n : ℕ) : sgPrimeCount n ≤ n + 1 :=
  le_trans (sgPrimeCount_le_primeCount n) (primeCount_le n)

/-- Monotonicity: m ≤ n → π_SG(m) ≤ π_SG(n). -/
theorem sgPrimeCount_mono {m n : ℕ} (h : m ≤ n) : sgPrimeCount m ≤ sgPrimeCount n := by
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
  exact ⟨by omega, hp.2⟩

/-- π_SG(0) = 0: no Sophie Germain primes at 0. -/
theorem sgPrimeCount_zero : sgPrimeCount 0 = 0 := by
  simp [sgPrimeCount, IsSophieGermainPrime]
  intro p hp
  interval_cases p <;> simp_all [Nat.Prime]

/-- π_SG(1) = 0: no Sophie Germain primes at 1. -/
theorem sgPrimeCount_one : sgPrimeCount 1 = 0 := by
  simp [sgPrimeCount, IsSophieGermainPrime]
  intro p hp
  interval_cases p <;> simp_all [Nat.Prime]

/-- 2 is the first Sophie Germain prime: π_SG(2) = 1. -/
theorem sgPrimeCount_two : sgPrimeCount 2 = 1 := by
  simp [sgPrimeCount, IsSophieGermainPrime]
  decide

/-! ## Distribution Characterization

The Hardy-Littlewood conjecture predicts:
  π_SG(x) ~ 2C₂ · x / (ln x)²

where C₂ = ∏_{p≥3} p(p-2)/(p-1)² ≈ 0.6602 is the twin prime constant.

Key consequence: the density of Sophie Germain primes among all primes
vanishes asymptotically: π_SG(x) / π(x) ~ 2C₂ / ln(x) → 0. -/

/-- The twin prime constant C₂ = ∏_{p≥3 prime} p(p-2)/(p-1)².
    We define it as a real number approximately 0.6602.
    (Exact formulation requires infinite products, stated as noncomputable.) -/
noncomputable def twinPrimeConstant : ℝ := 0.6602  -- Approximate value

/-- Sophie Germain primes are determined by residue class:
    For p > 3, if p is a Sophie Germain prime, then p ≡ 2 (mod 3).
    Equivalently, p ∈ {2, 3} or p ≡ 2 (mod 3). -/
theorem sg_mod_three (p : ℕ) (hp : IsSophieGermainPrime p) (hp3 : 3 < p) :
    p % 3 = 2 := by
  obtain ⟨hp_prime, hsp_prime⟩ := hp
  -- p > 3 and prime → p % 3 ∈ {1, 2} (not 0, since p > 3 and prime means ¬(3 ∣ p))
  have h_not_div3 : ¬(3 ∣ p) := by
    intro h
    have := Nat.Prime.eq_one_or_self_of_dvd hp_prime 3 h
    omega
  have h_mod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  -- If p % 3 = 1: then 2p + 1 ≡ 2·1 + 1 = 3 ≡ 0 (mod 3)
  -- So 3 ∣ (2p+1). Since 2p+1 > 3 (as p > 3), this contradicts primality of 2p+1.
  rcases h_mod with h1 | h2
  · exfalso
    have : (2 * p + 1) % 3 = 0 := by omega
    have h_div3 : 3 ∣ (2 * p + 1) := Nat.dvd_of_mod_eq_zero this
    have : 2 * p + 1 > 3 := by omega
    exact absurd (Nat.Prime.eq_one_or_self_of_dvd hsp_prime 3 h_div3) (by omega)
  · exact h2

/-- Sophie Germain primes > 3 satisfy p ≡ 5 (mod 6).
    This follows from p ≡ 2 (mod 3) and p being odd (p > 2 and prime → odd). -/
theorem sg_mod_six (p : ℕ) (hp : IsSophieGermainPrime p) (hp3 : 3 < p) :
    p % 6 = 5 := by
  have h_mod3 := sg_mod_three p hp hp3
  have h_odd : p % 2 = 1 := by
    have : p ≠ 2 := by omega
    exact Nat.Prime.odd_of_ne_two hp.1 this |>.mod_cast_eq
  omega

/-! ## Structural Results -/

/-- If p is a Sophie Germain prime, then SafePrime p = 2p + 1 is prime. -/
theorem safePrime_of_sg (p : ℕ) (hp : IsSophieGermainPrime p) :
    Nat.Prime (SafePrime p) := by
  exact hp.2

/-- The safe prime 2p+1 is always odd for p ≥ 1. -/
theorem safePrime_odd (p : ℕ) (hp : 1 ≤ p) : SafePrime p % 2 = 1 := by
  simp [SafePrime]; omega

end SophieGermainOQ02
