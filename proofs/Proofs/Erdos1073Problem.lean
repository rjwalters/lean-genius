/- Erdős Problem 1073: Composites Dividing Factorial Plus One

Let `A(x)` count the number of composite `u < x` such that `n! + 1 ≡ 0 (mod u)`
for some positive integer `n`. Is `A(x) ≤ x^{o(1)}`?

By Wilson's theorem, every prime `p` divides `(p-1)! + 1`. This problem asks
how many composites share this property. Known composites: 25, 121, 169, 437, ...

*Reference:* [erdosproblems.com/1073](https://www.erdosproblems.com/1073) -/

import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModCast
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Nat Filter

/- ## Core definitions -/

/-- `DividesFactorialPlusOne u` means there exists `n` with `u ∣ n! + 1`. -/
def DividesFactorialPlusOne (u : ℕ) : Prop :=
    ∃ n : ℕ, u ∣ n ! + 1

/-- The set of composites less than `x` dividing some `n! + 1`. -/
def compositeFactorialSet (x : ℕ) : Set ℕ :=
    { u | u < x ∧ ¬u.Prime ∧ 2 ≤ u ∧ DividesFactorialPlusOne u }

/-- `A(x)` counts composites less than `x` dividing some `n! + 1`. -/
noncomputable def factorialCompositeCount (x : ℕ) : ℕ :=
    (compositeFactorialSet x).ncard

/- ## Main conjecture (OPEN) -/

/-- Erdős Problem 1073: `A(x) ≤ x^{o(1)}`, i.e., for every `ε > 0`,
`A(x) ≤ x^ε` for large `x`. -/
def ErdosProblem1073 : Prop :=
    ∀ ε : ℝ, 0 < ε →
      ∃ N₀ : ℕ, ∀ x : ℕ, N₀ ≤ x →
        (factorialCompositeCount x : ℝ) ≤ (x : ℝ) ^ ε

/- ## Wilson's theorem connection -/

/-- Wilson's theorem (divisibility form): a prime `p ≥ 2` divides `(p-1)! + 1`.
    Derived from Mathlib's `ZMod.wilsons_lemma`. -/
theorem wilson_theorem (p : ℕ) (hp : p.Prime) :
    p ∣ (p - 1)! + 1 := by
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have h := ZMod.wilsons_lemma p
  -- h : (↑(p - 1)! : ZMod p) = -1
  -- Show (↑((p-1)! + 1) : ZMod p) = 0
  have h2 : (↑((p - 1)! + 1) : ZMod p) = 0 := by
    push_cast
    rw [h]
    ring
  exact (ZMod.natCast_zmod_eq_zero_iff_dvd _ _).mp h2

/-- Every prime satisfies `DividesFactorialPlusOne` via Wilson's theorem. -/
theorem prime_divides_factorial_plus_one (p : ℕ) (hp : p.Prime) :
    DividesFactorialPlusOne p :=
  ⟨p - 1, wilson_theorem p hp⟩

/- ## Known composite witnesses (all verified computationally) -/

/-- 25 divides 4! + 1. Proof: 4! + 1 = 25. -/
theorem composite_25 : DividesFactorialPlusOne 25 :=
    ⟨4, by native_decide⟩

/-- 121 = 11² divides 5! + 1. Proof: 5! + 1 = 121. -/
theorem composite_121 : DividesFactorialPlusOne 121 :=
    ⟨5, by native_decide⟩

/-- 169 = 13² divides 12! + 1. Proof: 12! + 1 = 479001601 = 169 × 2834329. -/
theorem composite_169 : DividesFactorialPlusOne 169 :=
    ⟨12, by native_decide⟩

/-- 437 = 19 × 23 divides 18! + 1. -/
theorem composite_437 : DividesFactorialPlusOne 437 :=
    ⟨18, by native_decide⟩

/- ## Basic properties -/

/-- 1 divides n! + 1 for all n. -/
theorem one_divides_factorial_plus_one : DividesFactorialPlusOne 1 :=
    ⟨0, one_dvd _⟩

/-- If u divides n! + 1 and d divides u, then d divides n! + 1. -/
theorem dvd_factorial_plus_one_of_dvd {u d : ℕ} (hdu : d ∣ u)
    (hu : DividesFactorialPlusOne u) : DividesFactorialPlusOne d := by
  obtain ⟨n, hn⟩ := hu
  exact ⟨n, dvd_trans hdu hn⟩

/-- The composite factorial set is monotone: if x ≤ y then
    compositeFactorialSet x ⊆ compositeFactorialSet y. -/
theorem compositeFactorialSet_mono {x y : ℕ} (hxy : x ≤ y) :
    compositeFactorialSet x ⊆ compositeFactorialSet y := by
  intro u ⟨hux, hnp, h2, hdvd⟩
  exact ⟨lt_of_lt_of_le hux hxy, hnp, h2, hdvd⟩

/-- A(x) is monotone in x. -/
theorem factorialCompositeCount_mono :
    Monotone factorialCompositeCount := by
  intro x y hxy
  exact Set.ncard_le_ncard (compositeFactorialSet_mono hxy)

/- ## Structural observations -/

/-- If u | n! + 1 and u ≥ 2, then gcd(u, n!) = 1, i.e., u is coprime to n!.
    This is because u | (n! + 1) and u | n! would imply u | 1. -/
theorem coprime_of_dvd_factorial_plus_one {u n : ℕ} (hu : 2 ≤ u)
    (hdvd : u ∣ n ! + 1) : Nat.Coprime u (n !) := by
  rw [Nat.Coprime]
  by_contra h
  -- gcd(u, n!) ≠ 1, so gcd divides both u and n!
  have hg1 : Nat.gcd u (n !) ∣ u := Nat.gcd_dvd_left u (n !)
  have hg2 : Nat.gcd u (n !) ∣ n ! := Nat.gcd_dvd_right u (n !)
  -- gcd | u | n!+1 and gcd | n!, so gcd | 1
  have h1 : Nat.gcd u (n !) ∣ n ! + 1 := dvd_trans hg1 hdvd
  have h2 : Nat.gcd u (n !) ∣ 1 := by
    have := Nat.dvd_sub' h1 hg2
    simp [Nat.add_sub_cancel] at this
    exact this
  exact h (Nat.eq_one_of_dvd_one h2)

/-- All prime factors of u must exceed n when u | n! + 1.
    If p ≤ n is prime and p | u, then p | n! (since p appears in the factorial),
    but u | n!+1 means p | n!+1, contradiction since gcd(n!, n!+1) = 1. -/
theorem prime_factors_exceed {u n p : ℕ} (hu : 2 ≤ u)
    (hdvd : u ∣ n ! + 1) (hp : p.Prime) (hpu : p ∣ u) (hpn : p ≤ n) : False := by
  have hcop := coprime_of_dvd_factorial_plus_one hu hdvd
  -- p | u and p | n! (since p ≤ n and p is prime)
  have hp_dvd_fact : p ∣ n ! := hp.dvd_factorial.mpr hpn
  -- p | u and Coprime u (n!)
  have : p ∣ Nat.gcd u (n !) := Nat.dvd_gcd hpu hp_dvd_fact
  rw [hcop] at this
  exact Nat.Prime.one_lt hp |>.not_le (Nat.le_of_dvd one_pos this)

/-- 25 is not prime (concrete check for the first known composite). -/
theorem not_prime_25 : ¬ Nat.Prime 25 := by decide

/-- 121 is not prime. -/
theorem not_prime_121 : ¬ Nat.Prime 121 := by decide

/-- 169 is not prime. -/
theorem not_prime_169 : ¬ Nat.Prime 169 := by decide

/-- 437 is not prime. -/
theorem not_prime_437 : ¬ Nat.Prime 437 := by decide

/-- All four known small composites are in compositeFactorialSet 500. -/
theorem four_known_composites :
    25 ∈ compositeFactorialSet 500 ∧
    121 ∈ compositeFactorialSet 500 ∧
    169 ∈ compositeFactorialSet 500 ∧
    437 ∈ compositeFactorialSet 500 := by
  refine ⟨⟨by omega, not_prime_25, by omega, composite_25⟩,
          ⟨by omega, not_prime_121, by omega, composite_121⟩,
          ⟨by omega, not_prime_169, by omega, composite_169⟩,
          ⟨by omega, not_prime_437, by omega, composite_437⟩⟩
