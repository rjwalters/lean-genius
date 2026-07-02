import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Int.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-
# Counting the square roots of unity modulo `n` (odd case)

For a modulus `n`, let `N(n) = #{x : ZMod n | x² = 1}` be the number of square roots
of unity.  This file proves, for **odd** `n`, the exact count

$$N(n) = 2^{\omega(n)},$$

where `ω(n) = n.primeFactors.card` is the number of distinct prime factors of `n`.

This is the odd-modulus half of `gauss-wilson-non-cyclic` openQuestions[2], which asks for
`N(n) = 2^{ω_odd(n) + δ}` with a 2-adic correction `δ ∈ {0,1,2}`.  For odd `n` we have
`δ = 0` and `ω_odd(n) = ω(n)`, and this is the case treated here.  The full even case is
left as a follow-up.

## Strategy

1. **Local count at an odd prime power** (`sq_eq_one_iff_prime_pow`, `sqrtOneCount_prime_pow`).
   In `ZMod (p^k)` with `p` an odd prime, `x² = 1 ↔ x = 1 ∨ x = -1`.  The forward direction
   is elementary: lifting `x` to an integer `a`, `p^k ∣ (a-1)(a+1)`; since `p` is odd it cannot
   divide both `a-1` and `a+1` (their difference is `2`), so `p^k` divides one of them.
   As `1 ≠ -1` (because `p^k ≥ 3`), this gives exactly two roots.

2. **Multiplicativity via CRT** (`sqrtOneCount_mul`).  For coprime `m, n` the ring isomorphism
   `ZMod (m*n) ≃+* ZMod m × ZMod n` (`ZMod.chineseRemainder`) transports `x² = 1` componentwise,
   so `N(m*n) = N(m) · N(n)`.

3. **Assembly** (`sqrtOneCount_odd`).  `N` is multiplicative with `N(1) = 1`, so by
   `Nat.multiplicative_factorization`, `N(n) = ∏_{p^k ‖ n} N(p^k)`.  For odd `n` every prime is
   odd, each factor is `2`, and the product is `2^{ω(n)}`.
-/

namespace GaussWilsonSqrtCount

open scoped Classical
open Finset

/-- The number of square roots of unity modulo `n`, i.e. `#{x : ZMod n | x² = 1}`. -/
noncomputable def sqrtOneCount (n : ℕ) : ℕ := Nat.card {x : ZMod n // x ^ 2 = 1}

/-- `sqrtOneCount 1 = 1`: modulo `1` everything collapses to a point. -/
theorem sqrtOneCount_one : sqrtOneCount 1 = 1 := by
  rw [sqrtOneCount]
  have : Subsingleton {x : ZMod 1 // x ^ 2 = 1} := by
    constructor; intro a b; apply Subtype.ext; apply Subsingleton.elim
  have hne : Nonempty {x : ZMod 1 // x ^ 2 = 1} := ⟨⟨1, one_pow 2⟩⟩
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨this, hne⟩

/-- **Odd prime power, local classification.**  In `ZMod (p^k)` with `p` an odd prime and
`k ≥ 1`, the only square roots of unity are `1` and `-1`. -/
theorem sq_eq_one_iff_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (_hk : k ≠ 0)
    (x : ZMod (p ^ k)) : x ^ 2 = 1 ↔ x = 1 ∨ x = -1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  constructor
  · intro hx
    -- Integer lift `a` of `x`.
    set a : ℤ := (x.val : ℤ) with ha
    have hxa : ((a : ℤ) : ZMod (p ^ k)) = x := by
      rw [ha]; push_cast; rw [ZMod.natCast_zmod_val]
    -- `(p^k : ℤ) ∣ (a-1)(a+1)`.
    have hpk_cast : ((p ^ k : ℕ) : ℤ) = (p : ℤ) ^ k := by push_cast; ring
    have hdvd : ((p : ℤ) ^ k) ∣ (a - 1) * (a + 1) := by
      have hx0 : (x - 1) * (x + 1) = 0 := by linear_combination hx
      have hz : (((a - 1) * (a + 1) : ℤ) : ZMod (p ^ k)) = 0 := by
        push_cast; rw [hxa]; exact hx0
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((a - 1) * (a + 1)) (p ^ k)).mp hz
      rwa [hpk_cast] at this
    have hp_int : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    -- `p ∤ 2`.
    have hp_not2 : ¬ (p : ℤ) ∣ (2 : ℤ) := by
      intro h
      have h2 : p ∣ 2 := by
        have : (p : ℤ) ∣ ((2 : ℕ) : ℤ) := by exact_mod_cast h
        exact_mod_cast (Int.natCast_dvd_natCast.mp this)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    by_cases hL : (p : ℤ) ∣ (a - 1)
    · by_cases hR : (p : ℤ) ∣ (a + 1)
      · exact absurd (by simpa using dvd_sub hR hL) hp_not2
      · left
        have hco : IsCoprime ((p : ℤ) ^ k) (a + 1) :=
          (hp_int.coprime_iff_not_dvd.mpr hR).pow_left
        have hdvd1 : ((p : ℤ) ^ k) ∣ (a - 1) := hco.dvd_of_dvd_mul_right hdvd
        have hz1 : ((a - 1 : ℤ) : ZMod (p ^ k)) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hpk_cast]; exact hdvd1
        have : x - 1 = 0 := by push_cast at hz1; rwa [hxa] at hz1
        exact sub_eq_zero.mp this
    · right
      have hco : IsCoprime ((p : ℤ) ^ k) (a - 1) :=
        (hp_int.coprime_iff_not_dvd.mpr hL).pow_left
      have hdvd2 : ((p : ℤ) ^ k) ∣ (a + 1) := hco.dvd_of_dvd_mul_left hdvd
      have hz2 : ((a + 1 : ℤ) : ZMod (p ^ k)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, hpk_cast]; exact hdvd2
      have : x + 1 = 0 := by push_cast at hz2; rwa [hxa] at hz2
      exact eq_neg_of_add_eq_zero_left this
  · rintro (rfl | rfl) <;> ring

/-- `1 ≠ -1` in `ZMod (p^k)` for an odd prime power (since the modulus is `≥ 3`). -/
theorem one_ne_neg_one_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : k ≠ 0) :
    (1 : ZMod (p ^ k)) ≠ -1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hpk3 : 3 ≤ p ^ k := le_trans hp3 (Nat.le_self_pow hk p)
  intro h
  have h2 : (2 : ZMod (p ^ k)) = 0 := by linear_combination h
  have h2n : ((2 : ℕ) : ZMod (p ^ k)) = 0 := by exact_mod_cast h2
  have hdvd : p ^ k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p ^ k)).mp h2n
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **Odd prime power count.**  `#{x : ZMod (p^k) | x² = 1} = 2` for an odd prime power. -/
theorem sqrtOneCount_prime_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {k : ℕ} (hk : k ≠ 0) :
    sqrtOneCount (p ^ k) = 2 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  rw [sqrtOneCount, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hset : (univ.filter (fun x : ZMod (p ^ k) => x ^ 2 = 1)) = {1, -1} := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact sq_eq_one_iff_prime_pow hp hp2 hk x
  rw [hset, Finset.card_pair (one_ne_neg_one_prime_pow hp hp2 hk)]

/-- **Multiplicativity via CRT.**  For coprime `m, n`, the count of square roots of unity is
multiplicative. -/
theorem sqrtOneCount_mul {m n : ℕ} (h : m.Coprime n) :
    sqrtOneCount (m * n) = sqrtOneCount m * sqrtOneCount n := by
  rw [sqrtOneCount, sqrtOneCount, sqrtOneCount, ← Nat.card_prod]
  refine Nat.card_congr ?_
  -- CRT ring isomorphism.
  let e := ZMod.chineseRemainder h
  -- Step 1: transport the predicate `x² = 1` across `e`.
  have e1 : {x : ZMod (m * n) // x ^ 2 = 1} ≃ {x : ZMod m × ZMod n // x ^ 2 = 1} :=
    Equiv.subtypeEquiv e.toEquiv (by
      intro x
      constructor
      · intro hx
        have : e (x ^ 2) = e 1 := by rw [hx]
        rwa [map_pow, map_one] at this
      · intro hx
        have hx' : e (x ^ 2) = e 1 := by rw [map_pow, map_one]; exact hx
        exact e.injective hx')
  -- Step 2: split the product predicate componentwise.
  have e2 : {x : ZMod m × ZMod n // x ^ 2 = 1} ≃
      {a : ZMod m // a ^ 2 = 1} × {b : ZMod n // b ^ 2 = 1} := by
    refine (Equiv.subtypeEquivRight ?_).trans (Equiv.subtypeProdEquivProd)
    intro x
    rw [Prod.pow_def, Prod.ext_iff]
    simp [Prod.one_eq_mk]
  exact e1.trans e2

/-- **Main theorem (odd case).**  For odd `n`, the number of square roots of unity modulo `n`
is `2^{ω(n)}`, where `ω(n)` is the number of distinct prime factors of `n`. -/
theorem sqrtOneCount_odd {n : ℕ} (hn : Odd n) :
    sqrtOneCount n = 2 ^ n.primeFactors.card := by
  have hn0 : n ≠ 0 := by rintro rfl; rw [Nat.odd_iff] at hn; omega
  rw [Nat.multiplicative_factorization sqrtOneCount
        (fun x y hxy => sqrtOneCount_mul hxy) sqrtOneCount_one hn0]
  calc n.factorization.prod (fun p k => sqrtOneCount (p ^ k))
      = ∏ p ∈ n.factorization.support, 2 := by
        rw [Finsupp.prod]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        rw [Nat.support_factorization] at hp
        have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpdvd : p ∣ n := Nat.dvd_of_mem_primeFactors hp
        have hk : n.factorization p ≠ 0 := by
          have : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
          rwa [Finsupp.mem_support_iff] at this
        have hp2 : p ≠ 2 := by
          rintro rfl
          rw [Nat.odd_iff] at hn
          omega
        exact sqrtOneCount_prime_pow hpp hp2 hk
    _ = 2 ^ n.factorization.support.card := by rw [Finset.prod_const]
    _ = 2 ^ n.primeFactors.card := by rw [Nat.support_factorization]

end GaussWilsonSqrtCount
