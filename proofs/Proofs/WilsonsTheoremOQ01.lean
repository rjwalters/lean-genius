import Mathlib.NumberTheory.Wilson
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic
import Proofs.WilsonsTheoremOQ02

/-
# Generalizations of Wilson's Theorem to Non-Prime Moduli

## What This Proves

Wilson's theorem states that (p-1)! ≡ -1 (mod p) iff p is prime.
This file explores what happens for non-prime (composite) moduli:

1. Composite factorial vanishing: For composite n > 4, n divides (n-1)!,
   so (n-1)! ≡ 0 (mod n).

2. The special case n = 4: 3! = 6 ≡ 2 (mod 4), the only composite
   number where (n-1)! is neither 0 nor -1 mod n.

3. Complete classification: For n ≥ 2, exactly one of three cases holds:
   - n is prime and (n-1)! ≡ -1 (mod n)
   - n = 4 and (n-1)! ≡ 2 (mod n)
   - n is composite, n > 4, and (n-1)! ≡ 0 (mod n)

4. Wilson quotient: For a prime p, the Wilson quotient is
   W_p = ((p-1)! + 1) / p. This is always an integer.

5. Wilson primes: A prime p is a Wilson prime if p² | (p-1)! + 1.
   The only known Wilson primes are 5, 13, and 563.

6. Gauss generalization: The product of all units mod n satisfies
   ∏ (units) ≡ -1 (mod n) iff n ∈ {1, 2, 4, p^k, 2p^k}.

## Status
- [x] Composite factorial theorem (n > 4) - full proof
- [x] Special case n = 4 verified
- [x] Complete classification theorem - full proof
- [x] Wilson quotient definition and properties
- [x] Wilson prime verification for 5, 13
- [x] Gauss generalization verified computationally for n ≤ 50
- [x] Gauss-Wilson classification via Mathlib's ZMod.isCyclic_units_iff
- [x] Bridge: unitsProduct ↔ IsCyclic (proved via WilsonsTheoremOQ02)
-/

namespace WilsonsTheoremGeneralization

open Nat

/-
## Infrastructure: Factorial as Finset Product
-/

-- Express n! as a product over Finset.Icc 1 n
lemma factorial_eq_Icc_prod (n : ℕ) : n.factorial = (Finset.Icc 1 n).prod id := by
  induction n with
  | zero => simp [Nat.factorial]
  | succ n ih =>
    rw [Nat.factorial_succ, ih]
    have hmem : n + 1 ∉ Finset.Icc 1 n := by simp
    have hinsert : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext x; simp [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hinsert, Finset.prod_insert hmem, id, mul_comm]

-- If a, b are distinct elements of {1,...,n}, then a*b | n!
lemma distinct_factors_dvd_factorial {a b n : ℕ}
    (ha : 1 ≤ a) (ha' : a ≤ n) (hb : 1 ≤ b) (hb' : b ≤ n) (hab : a ≠ b) :
    a * b ∣ n.factorial := by
  rw [factorial_eq_Icc_prod]
  have hpair : ({a, b} : Finset ℕ).prod id = a * b := by
    rw [Finset.prod_pair hab]; rfl
  rw [← hpair]
  apply Finset.prod_dvd_prod_of_subset
  intro x hx
  simp at hx
  simp [Finset.mem_Icc]
  rcases hx with rfl | rfl <;> omega

/-
## Part 1: Composite Factorial Vanishing

For any composite number n > 4, we have n | (n-1)!.
-/

theorem composite_factorial_dvd {n : ℕ} (hn_comp : ¬Nat.Prime n) (hn_gt : n > 4) :
    n ∣ (n - 1).factorial := by
  have hn_pos : 0 < n := by omega
  have hn_ne_one : n ≠ 1 := by omega
  set p := n.minFac with hp_def
  have hp_prime : Nat.Prime p := Nat.minFac_prime hn_ne_one
  have hp_dvd : p ∣ n := Nat.minFac_dvd n
  have hp_gt_one : 1 < p := hp_prime.one_lt
  set q := n / p with hq_def
  have hpq : p * q = n := Nat.mul_div_cancel' hp_dvd
  have hp_sq_le : p ^ 2 ≤ n := Nat.minFac_sq_le_self hn_pos hn_comp
  have hq_ge_p : p ≤ q := by
    by_contra h
    push_neg at h
    have h1 : p * q < p * p := by nlinarith
    nlinarith
  have hq_gt_one : 1 < q := by linarith
  have hp_lt_n : p < n := by nlinarith
  have hq_lt_n : q < n := by nlinarith
  by_cases hpq_eq : p = q
  · -- Case: n = p² (p = q), so p ≥ 3
    have hn_eq : n = p * p := by rw [← hpq, hpq_eq]
    have hp_ge_3 : p ≥ 3 := by
      by_contra h
      push_neg at h
      have hp2 : p = 2 := by omega
      rw [hp2] at hn_eq; omega
    have h2p_lt : 2 * p < p * p := by nlinarith
    have h2p_le : 2 * p ≤ n - 1 := by omega
    have hp_ne_2p : p ≠ 2 * p := by omega
    have h_prod_dvd : p * (2 * p) ∣ (n - 1).factorial :=
      distinct_factors_dvd_factorial (by omega) (by omega) (by omega) h2p_le hp_ne_2p
    have h_pp_dvd : p * p ∣ p * (2 * p) := ⟨2, by ring⟩
    have h_goal : p * p ∣ (n - 1).factorial := dvd_trans h_pp_dvd h_prod_dvd
    exact hn_eq ▸ h_goal
  · -- Case: p ≠ q, both in {1,...,n-1}
    rw [← hpq]
    exact distinct_factors_dvd_factorial (by omega) (by omega) (by omega) (by omega) hpq_eq

-- Equivalent ZMod formulation
theorem composite_factorial_zero {n : ℕ} (hn_comp : ¬Nat.Prime n) (hn_gt : n > 4) :
    (↑(n - 1).factorial : ZMod n) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact composite_factorial_dvd hn_comp hn_gt

/-
## Part 2: Special Cases and Complete Classification
-/

-- n = 4 is the unique anomaly: 3! = 6 ≡ 2 (mod 4)
theorem factorial_mod_four : (↑(4 - 1).factorial : ZMod 4) = 2 := by native_decide
theorem factorial_mod_four_not_zero : (↑(4 - 1).factorial : ZMod 4) ≠ 0 := by native_decide
theorem factorial_mod_four_not_neg_one : (↑(4 - 1).factorial : ZMod 4) ≠ -1 := by native_decide

-- Small prime verifications of Wilson's theorem
example : (↑(2 - 1).factorial : ZMod 2) = -1 := by native_decide
example : (↑(3 - 1).factorial : ZMod 3) = -1 := by native_decide
example : (↑(5 - 1).factorial : ZMod 5) = -1 := by native_decide
example : (↑(7 - 1).factorial : ZMod 7) = -1 := by native_decide
example : (↑(11 - 1).factorial : ZMod 11) = -1 := by native_decide
example : (↑(13 - 1).factorial : ZMod 13) = -1 := by native_decide

-- Small composite verifications (all ≡ 0 mod n for n > 4)
example : (↑(6 - 1).factorial : ZMod 6) = 0 := by native_decide
example : (↑(8 - 1).factorial : ZMod 8) = 0 := by native_decide
example : (↑(9 - 1).factorial : ZMod 9) = 0 := by native_decide
example : (↑(10 - 1).factorial : ZMod 10) = 0 := by native_decide
example : (↑(12 - 1).factorial : ZMod 12) = 0 := by native_decide
example : (↑(15 - 1).factorial : ZMod 15) = 0 := by native_decide
example : (↑(16 - 1).factorial : ZMod 16) = 0 := by native_decide
example : (↑(20 - 1).factorial : ZMod 20) = 0 := by native_decide
example : (↑(25 - 1).factorial : ZMod 25) = 0 := by native_decide

-- For n ≥ 2, the factorial residue determines primality
theorem wilson_complete_classification {n : ℕ} (hn : n ≥ 2) :
    (Nat.Prime n ∧ (↑(n - 1).factorial : ZMod n) = -1) ∨
    (n = 4 ∧ (↑(n - 1).factorial : ZMod n) = 2) ∨
    (¬Nat.Prime n ∧ n ≠ 4 ∧ (↑(n - 1).factorial : ZMod n) = 0) := by
  by_cases hp : Nat.Prime n
  · left
    exact ⟨hp, (Nat.prime_iff_fac_equiv_neg_one (by omega : n ≠ 1)).mp hp⟩
  · right
    by_cases h4 : n = 4
    · left
      exact ⟨h4, by subst h4; native_decide⟩
    · right
      refine ⟨hp, h4, ?_⟩
      have hgt4 : n > 4 := by
        by_contra h_le
        push_neg at h_le
        interval_cases n
        · exact hp Nat.prime_two
        · exact hp Nat.prime_three
        · exact h4 rfl
      exact composite_factorial_zero hp hgt4

-- Primality test via factorial (biconditional from Mathlib)
theorem prime_iff_factorial_neg_one {n : ℕ} (hn : n ≥ 2) :
    Nat.Prime n ↔ (↑(n - 1).factorial : ZMod n) = -1 :=
  Nat.prime_iff_fac_equiv_neg_one (by omega)

/-
## Part 3: Wilson Quotient
-/

def wilsonQuotient (p : ℕ) : ℕ := ((p - 1).factorial + 1) / p

theorem prime_dvd_factorial_succ {p : ℕ} (hp : Nat.Prime p) :
    p ∣ (p - 1).factorial + 1 := by
  have h1 : p ≠ 1 := Nat.Prime.one_lt hp |>.ne'
  have h2 := (Nat.prime_iff_fac_equiv_neg_one h1).mp hp
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [h2]
  ring

theorem wilsonQuotient_mul {p : ℕ} (hp : Nat.Prime p) :
    wilsonQuotient p * p = (p - 1).factorial + 1 := by
  unfold wilsonQuotient
  exact Nat.div_mul_cancel (prime_dvd_factorial_succ hp)

-- Wilson quotient is always positive for primes
theorem wilsonQuotient_pos {p : ℕ} (hp : Nat.Prime p) :
    0 < wilsonQuotient p := by
  rw [Nat.pos_iff_ne_zero]
  intro h
  have := wilsonQuotient_mul hp
  rw [h, zero_mul] at this
  exact absurd this (by positivity)

-- Compute Wilson quotients for small primes
example : wilsonQuotient 2 = 1 := by native_decide
example : wilsonQuotient 3 = 1 := by native_decide
example : wilsonQuotient 5 = 5 := by native_decide
example : wilsonQuotient 7 = 103 := by native_decide
example : wilsonQuotient 11 = 329891 := by native_decide
example : wilsonQuotient 13 = 36846277 := by native_decide

/-
## Part 4: Wilson Primes
-/

def IsWilsonPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ p ^ 2 ∣ (p - 1).factorial + 1

theorem isWilsonPrime_iff_quotient {p : ℕ} (hp : Nat.Prime p) :
    IsWilsonPrime p ↔ p ∣ wilsonQuotient p := by
  unfold IsWilsonPrime wilsonQuotient
  constructor
  · intro ⟨_, h⟩
    rw [Nat.dvd_div_iff_mul_dvd (prime_dvd_factorial_succ hp)]
    rw [show p ^ 2 = p * p from sq p] at h
    exact h
  · intro h
    refine ⟨hp, ?_⟩
    rw [show p ^ 2 = p * p from sq p]
    rwa [Nat.dvd_div_iff_mul_dvd (prime_dvd_factorial_succ hp)] at h

-- Verify: 5 is a Wilson prime (4! + 1 = 25 = 5²)
theorem five_is_wilson_prime : IsWilsonPrime 5 := by
  constructor
  · decide
  · native_decide

-- Verify: 13 is a Wilson prime
theorem thirteen_is_wilson_prime : IsWilsonPrime 13 := by
  constructor
  · decide
  · native_decide

-- Verify non-Wilson primes
theorem two_not_wilson_prime : ¬IsWilsonPrime 2 := by
  intro ⟨_, h⟩; revert h; native_decide

theorem three_not_wilson_prime : ¬IsWilsonPrime 3 := by
  intro ⟨_, h⟩; revert h; native_decide

theorem seven_not_wilson_prime : ¬IsWilsonPrime 7 := by
  intro ⟨_, h⟩; revert h; native_decide

theorem eleven_not_wilson_prime : ¬IsWilsonPrime 11 := by
  intro ⟨_, h⟩; revert h; native_decide

/-
## Part 5: Gauss's Generalization (Product of Units)

For any n ≥ 1, the product of all units mod n (integers coprime to n)
satisfies:
- ∏ units ≡ -1 (mod n) if n ∈ {1, 2, 4, p^k, 2p^k} (p odd prime)
- ∏ units ≡  1 (mod n) otherwise
-/

def unitsProduct (n : ℕ) : ℕ :=
  ((Finset.range n).filter (fun a => Nat.Coprime a n)).prod id

-- n ∈ {1,2,4,p^k,2p^k}: product ≡ -1 (mod n)
example : unitsProduct 2 % 2 = 1 := by native_decide
example : unitsProduct 3 % 3 = 2 := by native_decide
example : unitsProduct 4 % 4 = 3 := by native_decide
example : unitsProduct 5 % 5 = 4 := by native_decide
example : unitsProduct 6 % 6 = 5 := by native_decide
example : unitsProduct 7 % 7 = 6 := by native_decide
example : unitsProduct 9 % 9 = 8 := by native_decide
example : unitsProduct 10 % 10 = 9 := by native_decide
example : unitsProduct 11 % 11 = 10 := by native_decide
example : unitsProduct 13 % 13 = 12 := by native_decide
example : unitsProduct 25 % 25 = 24 := by native_decide

-- n not of that form: product ≡ 1 (mod n)
example : unitsProduct 8 % 8 = 1 := by native_decide
example : unitsProduct 12 % 12 = 1 := by native_decide
example : unitsProduct 15 % 15 = 1 := by native_decide
example : unitsProduct 16 % 16 = 1 := by native_decide
example : unitsProduct 24 % 24 = 1 := by native_decide

/-
## Part 6: The Gauss-Wilson Classification

Gauss proved that ∏ units ≡ -1 (mod n) iff n ∈ {1, 2, 4, p^k, 2p^k}
where p is an odd prime. This is equivalent to (ℤ/nℤ)* being cyclic.

We provide:
1. A decidable Bool check `hasGaussWilsonForm`
2. A computable verification `gaussWilsonCheck` that tests both sides
3. The classification verified computationally for n ≤ 50
4. The general statement via Mathlib's ZMod.isCyclic_units_iff (see Part 12)
-/

-- Check if x is a power of base
def isPowerOfAux (base x : ℕ) : Bool :=
  if x == 0 then false
  else if x == 1 then true
  else if base < 2 then false
  else if x % base == 0 then isPowerOfAux base (x / base)
  else false
termination_by x
decreasing_by
  simp_all only [beq_iff_eq, bne_iff_ne, Bool.not_eq_true, decide_eq_false_iff_not,
    not_lt, ge_iff_le]
  exact Nat.div_lt_self (by omega) (by omega)

-- Check if n has the form p^k or 2*p^k (p odd prime) or n ≤ 4
def hasGaussWilsonForm (n : ℕ) : Bool :=
  if n ≤ 2 then true  -- n=1,2 trivially have the property
  else if n == 4 then true
  else
    let p := n.minFac
    if p == 2 then
      -- n is even: check if n/2 = q^j for odd prime q
      let m := n / 2
      if m < 3 then false
      else
        let q := m.minFac
        if q < 3 then false
        else isPowerOfAux q m
    else
      -- n is odd: check if n is a power of p
      isPowerOfAux p n

-- The Bool check that both sides agree for a given n
def gaussWilsonCheck (n : ℕ) : Bool :=
  if n < 3 then true  -- skip small n
  else (unitsProduct n % n == n - 1) == hasGaussWilsonForm n

-- Verify the classification holds for all n from 3 to 50
theorem gaussWilson_verified_le_50 :
    ∀ n : Fin 51, n.val ≥ 3 → gaussWilsonCheck n.val = true := by native_decide

-- Odd prime powers: units product ≡ -1
example : unitsProduct 27 % 27 = 27 - 1 := by native_decide -- 3³
example : unitsProduct 49 % 49 = 49 - 1 := by native_decide -- 7²

-- Twice odd prime powers: units product ≡ -1
example : unitsProduct 14 % 14 = 14 - 1 := by native_decide  -- 2·7
example : unitsProduct 18 % 18 = 18 - 1 := by native_decide  -- 2·3²
example : unitsProduct 50 % 50 = 50 - 1 := by native_decide  -- 2·5²

-- Other n: units product ≡ 1
example : unitsProduct 20 % 20 = 1 := by native_decide    -- 4·5
example : unitsProduct 21 % 21 = 1 := by native_decide    -- 3·7
example : unitsProduct 30 % 30 = 1 := by native_decide    -- 2·3·5
example : unitsProduct 32 % 32 = 1 := by native_decide    -- 2⁵
example : unitsProduct 36 % 36 = 1 := by native_decide    -- 4·9
example : unitsProduct 40 % 40 = 1 := by native_decide    -- 8·5
example : unitsProduct 48 % 48 = 1 := by native_decide    -- 16·3

/-
## Part 7: Bridge Between unitsProduct and Factorial

For prime p, the units mod p are exactly {1,...,p-1}, so
unitsProduct p = (p-1)!. Combined with Wilson's theorem,
this gives unitsProduct p % p = p - 1.
-/

-- For primes, coprimality to p is equivalent to being nonzero
lemma prime_coprime_iff_pos {p a : ℕ} (hp : Nat.Prime p) (ha : a < p) :
    Nat.Coprime a p ↔ 0 < a := by
  constructor
  · intro hc
    by_contra h
    push_neg at h
    have ha0 : a = 0 := by omega
    subst ha0
    simp [Nat.Coprime] at hc
    exact (hp.one_lt).ne' hc
  · intro ha_pos
    have hndvd : ¬ p ∣ a := fun hdvd => absurd ha (not_lt.mpr (Nat.le_of_dvd ha_pos hdvd))
    exact (hp.coprime_iff_not_dvd.mpr hndvd).symm

-- The filter of coprime elements in {0,...,p-1} equals {1,...,p-1} for prime p
lemma unitsProduct_eq_factorial {p : ℕ} (hp : Nat.Prime p) :
    unitsProduct p = (p - 1).factorial := by
  unfold unitsProduct
  have hp2 : p ≥ 2 := hp.two_le
  -- Both sides are products over {1,...,p-1}
  -- LHS: ∏ a in (range p).filter (coprime · p), id a
  -- RHS: (p-1)! = ∏ a in Icc 1 (p-1), id a
  rw [factorial_eq_Icc_prod]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range, id]
  constructor
  · intro ⟨ha_lt, ha_cop⟩
    rw [prime_coprime_iff_pos hp ha_lt] at ha_cop
    simp [Finset.mem_Icc]; omega
  · intro ha_mem
    simp [Finset.mem_Icc] at ha_mem
    constructor
    · omega
    · rw [prime_coprime_iff_pos hp (by omega)]
      omega

-- For all primes p ≥ 2, unitsProduct p % p = p - 1
-- This is Wilson's theorem translated to our unitsProduct definition
theorem unitsProduct_prime {p : ℕ} (hp : Nat.Prime p) (_hp2 : p ≥ 2) :
    unitsProduct p % p = p - 1 := by
  rw [unitsProduct_eq_factorial hp]
  -- Wilson's theorem: p | (p-1)! + 1, i.e. (p-1)! + 1 = p * k
  have h_wilson : p ∣ (p - 1).factorial + 1 := prime_dvd_factorial_succ hp
  obtain ⟨k, hk⟩ := h_wilson
  have hk_pos : 0 < k := by
    rcases k with _ | k
    · simp at hk; omega
    · omega
  -- (p-1)! = p * k - 1 = p * (k - 1) + (p - 1)
  have key : (p - 1).factorial = p * (k - 1) + (p - 1) := by omega
  rw [key]
  exact Nat.add_mul_mod_self_left (p - 1) p (k - 1)

-- Wilson's theorem in product form (from Mathlib)
theorem wilson_product_form (p : ℕ) [hp : Fact (Nat.Prime p)] :
    ∏ x ∈ Finset.Ico 1 p, (x : ZMod p) = -1 :=
  ZMod.prod_Ico_one_prime p

/-
## Part 8: Square Roots of Unity Analysis

The key to the Gauss-Wilson classification is counting solutions to
x² ≡ 1 (mod n) among units. The involution a ↦ a⁻¹ pairs non-self-inverse
elements, so ∏ units = ∏ {self-inverse units}.

- If exactly 2 self-inverse units (1 and n-1): product = n-1 ≡ -1
- If more: the self-inverse units form (ℤ/2ℤ)^k, k ≥ 2, product = 1
-/

-- Count square roots of unity mod n (units a with a² ≡ 1)
def sqRootsOfUnity (n : ℕ) : Finset ℕ :=
  ((Finset.range n).filter (fun a => Nat.Coprime a n)).filter (fun a => a * a % n = 1)

-- For primes ≥ 3, exactly 2 square roots of unity: {1, p-1}
theorem sqRootsOfUnity_prime_card : ∀ p : Fin 50, p.val ≥ 3 →
    Nat.Prime p.val → (sqRootsOfUnity p.val).card = 2 := by native_decide

-- For n = 4: exactly 2 square roots: {1, 3}
example : (sqRootsOfUnity 4).card = 2 := by native_decide

-- For odd prime powers: still exactly 2
example : (sqRootsOfUnity 9).card = 2 := by native_decide   -- 3²
example : (sqRootsOfUnity 25).card = 2 := by native_decide  -- 5²
example : (sqRootsOfUnity 27).card = 2 := by native_decide  -- 3³
example : (sqRootsOfUnity 49).card = 2 := by native_decide  -- 7²

-- For 2·(odd prime power): exactly 2
example : (sqRootsOfUnity 6).card = 2 := by native_decide   -- 2·3
example : (sqRootsOfUnity 10).card = 2 := by native_decide  -- 2·5
example : (sqRootsOfUnity 14).card = 2 := by native_decide  -- 2·7
example : (sqRootsOfUnity 18).card = 2 := by native_decide  -- 2·3²
example : (sqRootsOfUnity 50).card = 2 := by native_decide  -- 2·5²

-- For non-Gauss-Wilson forms: more than 2 square roots
example : (sqRootsOfUnity 8).card = 4 := by native_decide   -- 2³
example : (sqRootsOfUnity 12).card = 4 := by native_decide  -- 4·3
example : (sqRootsOfUnity 15).card = 4 := by native_decide  -- 3·5
example : (sqRootsOfUnity 16).card = 4 := by native_decide  -- 2⁴
example : (sqRootsOfUnity 21).card = 4 := by native_decide  -- 3·7
example : (sqRootsOfUnity 24).card = 8 := by native_decide  -- 2³·3
example : (sqRootsOfUnity 30).card = 4 := by native_decide  -- 2·3·5
example : (sqRootsOfUnity 32).card = 4 := by native_decide  -- 2⁵

-- The square root count characterizes Gauss-Wilson form
def sqRootGaussCheck (n : ℕ) : Bool :=
  if n < 3 then true
  else ((sqRootsOfUnity n).card == 2) == hasGaussWilsonForm n

-- Verified: n has Gauss-Wilson form ↔ exactly 2 square roots of unity, for n ≤ 100
theorem sqRoot_gaussWilson_le_100 :
    ∀ n : Fin 101, n.val ≥ 3 → sqRootGaussCheck n.val = true := by native_decide

/-
## Part 9: Involution-Product Connection

The product of all units equals the product of self-inverse units,
because non-self-inverse elements pair as (a, a⁻¹ mod n) contributing
a · a⁻¹ ≡ 1 to the product. This is the key structural lemma.
-/

-- Verify: ∏ units = ∏ self-inverse units (mod n) for n ≤ 100
def selfInverseProductCheck (n : ℕ) : Bool :=
  if n < 3 then true
  else
    let selfInvProd := (sqRootsOfUnity n).prod id % n
    let fullProd := unitsProduct n % n
    fullProd == selfInvProd

theorem selfInverse_product_le_100 :
    ∀ n : Fin 101, n.val ≥ 3 → selfInverseProductCheck n.val = true := by native_decide

/-
## Part 10: Extended Computational Verification

The Gauss-Wilson classification verified for increasing ranges.
-/

-- Extended verification: n ≤ 100
theorem gaussWilson_verified_le_100 :
    ∀ n : Fin 101, n.val ≥ 3 → gaussWilsonCheck n.val = true := by native_decide

-- Extended verification: n ≤ 150
theorem gaussWilson_verified_le_150 :
    ∀ n : Fin 151, n.val ≥ 3 → gaussWilsonCheck n.val = true := by native_decide

-- Extended verification: n ≤ 200
theorem gaussWilson_verified_le_200 :
    ∀ n : Fin 201, n.val ≥ 3 → gaussWilsonCheck n.val = true := by native_decide

/-
## Part 11: The Gauss-Wilson Classification

**Theorem** (Gauss): ∏ units ≡ -1 (mod n) iff n ∈ {4, p^k, 2p^k} (p odd prime, k ≥ 1).

### Proof Architecture (three-lemma decomposition)

1. **Involution lemma**: ∏ units = ∏ self-inverse units (mod n)
   - Algebraic proof via `Finset.prod_involution` on the map a ↦ n - a
   - Verified computationally for n ≤ 100 (`selfInverse_product_le_100`)

2. **Square root counting**: n has Gauss-Wilson form ↔ exactly 2 solutions
   to x² ≡ 1 (mod n) among units
   - Forward: For p^k (odd prime), x²-1=(x-1)(x+1) in integral domain → ≤2 roots.
     Hensel lifting shows exactly 2 for all k. CRT gives 2 for 2p^k. Direct for n=4.
   - Backward: CRT → each odd prime power factor doubles root count, 2^k (k≥3) gives 4.
   - Verified computationally for n ≤ 100 (`sqRoot_gaussWilson_le_100`)

3. **Product evaluation**: When self-inverse units = {1, n-1}, product = n-1 ≡ -1.
   When |self-inverse| ≥ 4, they form exponent-2 subgroup, product = 1.
   - Verified computationally for n ≤ 100 (`selfInverse_product_le_100`)

### Mathlib Now Provides (as of current version)
- `ZMod.isCyclic_units_iff`: Complete classification of when (ℤ/nℤ)* is cyclic
  (includes primitive root existence via Hensel lifting, CRT for unit groups)
- See Part 12 for the proof using this Mathlib API.
- Bridge proved via OQ02's `gaussWilson_abstract` and `unitsProduct_cast_eq_abstract`
-/

/-
## Part 12: Abstract Gauss-Wilson via Mathlib

Mathlib now provides `ZMod.isCyclic_units_iff`, the complete classification
of when (ℤ/nℤ)* is cyclic. We use this to prove the Gauss-Wilson theorem.

The condition for (ℤ/nℤ)* to be cyclic (from Mathlib):
  IsCyclic (ZMod n)ˣ ↔ n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 4 ∨
    ∃ p m, Nat.Prime p ∧ Odd p ∧ 1 ≤ m ∧ (n = p^m ∨ n = 2*p^m)

This is exactly the Gauss-Wilson condition (for n ≥ 3, excluding n=0,1,2).
-/

-- Restate the cyclic units classification for n ≥ 3
theorem isCyclic_units_iff_gaussWilson {n : ℕ} (hn : n ≥ 3) :
    IsCyclic (ZMod n)ˣ ↔
    n = 4 ∨ (∃ p k, Nat.Prime p ∧ Odd p ∧ k ≥ 1 ∧ (n = p ^ k ∨ n = 2 * p ^ k)) := by
  rw [ZMod.isCyclic_units_iff]
  constructor
  · intro h
    rcases h with rfl | rfl | rfl | rfl | ⟨p, m, hp, hodd, hm, hform⟩
    · omega
    · omega
    · omega
    · left; rfl
    · right; exact ⟨p, m, hp, hodd, hm, hform⟩
  · intro h
    rcases h with rfl | ⟨p, k, hp, hodd, hk, hform⟩
    · right; right; right; left; rfl
    · right; right; right; right; exact ⟨p, k, hp, hodd, hk, hform⟩

/-
### Gauss-Wilson in terms of the concrete unitsProduct

The bridge between IsCyclic (ZMod n)ˣ and unitsProduct n % n = n - 1
requires showing that:
- In a cyclic (ℤ/nℤ)*, the involution pairing leaves only {1, n-1},
  so the product is n-1 ≡ -1.
- In a non-cyclic (ℤ/nℤ)*, there are ≥ 4 self-inverse elements,
  forming a (ℤ/2ℤ)^k subgroup whose product is 1.

We state the classification with the concrete unitsProduct and
provide a partial proof: the RHS condition is reformulated using
Mathlib's isCyclic_units_iff, and the LHS ↔ IsCyclic bridge is
established through the involution-product argument.
-/

-- For n ≥ 3, Odd p ↔ p ≠ 2 for primes
private lemma prime_odd_iff_ne_two {p : ℕ} (hp : Nat.Prime p) : Odd p ↔ p ≠ 2 := by
  constructor
  · intro ⟨k, hk⟩ h2
    rw [h2] at hk; omega
  · exact hp.odd_of_ne_two

/-
### Bridge Lemma: unitsProduct n % n = n - 1 ↔ IsCyclic (ZMod n)ˣ

Both directions follow from the involution-product structure:
  ∏ units = ∏ {self-inverse units} (mod n)  [a ↦ a⁻¹ pairs non-fixed]
  |{self-inverse}| = 2 iff cyclic (for n ≥ 3)  [cyclic ↔ x²=1 has ≤ 2 solutions]
  When |{self-inverse}| = 2: product = 1·(n-1) = n-1 ≡ -1
  When |{self-inverse}| ≥ 4: product of (ℤ/2)^k subgroup = 1

Computationally verified for n ≤ 200 (gaussWilson_verified_le_200).
-/

/-
### Bridge Proof via WilsonsTheoremOQ02

WilsonsTheoremOQ02 proves (sorry-free):
1. `unitsProduct_cast_eq_abstract`: ↑(unitsProduct n) = ∏ units in ZMod n
2. `gaussWilson_abstract`: ∏ units = -1 ↔ IsCyclic (ZMod n)ˣ

We connect the concrete `unitsProduct n % n = n - 1` to the abstract
`∏ units = -1` via ZMod.val, then use the abstract theorem.
-/

/-- In ZMod n, casting n - 1 gives -1. -/
private lemma natCast_sub_one_eq_neg_one' {n : ℕ} (hn : n ≥ 1) :
    (↑(n - 1) : ZMod n) = -1 := by
  haveI : NeZero n := ⟨by omega⟩
  rw [eq_neg_iff_add_eq_zero]
  rw [← Nat.cast_one, ← Nat.cast_add, Nat.sub_add_cancel hn, ZMod.natCast_self_eq_zero]

theorem unitsProduct_eq_neg_one_iff_cyclic {n : ℕ} (hn : n ≥ 3) :
    unitsProduct n % n = n - 1 ↔ IsCyclic (ZMod n)ˣ := by
  haveI : NeZero n := ⟨by omega⟩
  -- Both OQ01 and OQ02 define unitsProduct identically, so OQ02's proven
  -- lemmas apply directly (Lean unfolds both to the same expression).
  -- OQ02.unitsProduct_cast_eq_abstract: ↑(unitsProduct n) = ∏ units in ZMod n
  -- OQ02.gaussWilson_abstract: ∏ units = -1 ↔ IsCyclic (ZMod n)ˣ
  have hcast : (↑(unitsProduct n) : ZMod n) = ∏ x : (ZMod n)ˣ, (x : ZMod n) :=
    WilsonsTheoremOQ02.unitsProduct_cast_eq_abstract (show n ≥ 1 by omega)
  constructor
  · -- Forward: unitsProduct n % n = n - 1 → IsCyclic
    intro h
    have hzmod : (↑(unitsProduct n) : ZMod n) = -1 := by
      rw [← natCast_sub_one_eq_neg_one' (show n ≥ 1 by omega)]
      exact ZMod.val_injective (by
        rw [ZMod.val_natCast, ZMod.val_natCast, h, Nat.mod_eq_of_lt (by omega)])
    rw [hcast] at hzmod
    exact (WilsonsTheoremOQ02.gaussWilson_abstract hn).mp hzmod
  · -- Backward: IsCyclic → unitsProduct n % n = n - 1
    intro hcyc
    have hzmod : ∏ x : (ZMod n)ˣ, (x : ZMod n) = -1 :=
      (WilsonsTheoremOQ02.gaussWilson_abstract hn).mpr hcyc
    rw [← hcast, ← natCast_sub_one_eq_neg_one' (show n ≥ 1 by omega)] at hzmod
    have hval := congrArg ZMod.val hzmod
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)] at hval

-- The full Gauss-Wilson classification
-- Reduces to: unitsProduct bridge (above) + isCyclic_units_iff_gaussWilson (Mathlib)
theorem gaussWilson_classification (n : ℕ) (hn : n ≥ 3) :
    unitsProduct n % n = n - 1 ↔
    (∃ p k, Nat.Prime p ∧ p ≠ 2 ∧ k ≥ 1 ∧ (n = p ^ k ∨ n = 2 * p ^ k)) ∨ n = 4 := by
  rw [unitsProduct_eq_neg_one_iff_cyclic hn, isCyclic_units_iff_gaussWilson hn]
  constructor
  · intro h
    rcases h with rfl | ⟨p, k, hp, hodd, hk, hform⟩
    · left; rfl
    · right; exact ⟨p, k, hp, ((prime_odd_iff_ne_two hp).mp hodd), hk, hform⟩
  · intro h
    rcases h with ⟨p, k, hp, hne2, hk, hform⟩ | rfl
    · right; exact ⟨p, k, hp, (prime_odd_iff_ne_two hp).mpr hne2, hk, hform⟩
    · left; rfl

end WilsonsTheoremGeneralization
