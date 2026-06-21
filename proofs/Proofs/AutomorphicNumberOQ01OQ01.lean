import Mathlib
import Proofs.AutomorphicNumberOQ01

/-!
# Why exactly four? Counting automorphic residues for an arbitrary modulus

## What This Proves

The parent file `AutomorphicNumberOQ01` shows that `ZMod (10 ^ k)` has **exactly four
idempotents** for every `k ≥ 1`, equivalently four `k`-digit automorphic residues
`n ^ 2 ≡ n (mod 10 ^ k)`.  The number `4` is not magic: it is `2 ^ 2`, and the exponent
`2` is the number of *distinct primes* dividing `10 ^ k` (namely `2` and `5`).

This file proves the underlying general law.  For **every** `n ≥ 1`,

```
idempotent_count :
  Nat.card {e : ZMod n // e * e = e} = 2 ^ n.primeFactors.card
```

i.e. the number of idempotents (= "automorphic residues") of `ZMod n` is `2 ^ ω(n)`,
where `ω(n)` is the number of distinct prime factors of `n`.  The parent's "exactly four
mod `10 ^ k`" is the special case `ω(10 ^ k) = 2`.

## Strategy

The counting function `numIdem n := #{idempotents of ZMod n}` is a **multiplicative
arithmetic function**:

* `numIdem 1 = 1`;
* for coprime `m, n ≥ 1`, the Chinese Remainder isomorphism
  `ZMod (m * n) ≃+* ZMod m × ZMod n` transports idempotents (`idemCongr` from the parent)
  and idempotents of a product split componentwise (`idemProd`), so
  `numIdem (m * n) = numIdem m · numIdem n`.

Evaluating a multiplicative function over the prime factorization
(`IsMultiplicative.multiplicative_factorization`) reduces the count to the prime-power
case, which the parent already settled: `numIdem (p ^ k) = 2` for every prime `p` and
`k ≥ 1` (`idem_card_prime_pow`).  The product of `2` over the `ω(n)` prime factors is
`2 ^ ω(n)`.

## Status

Fully machine-checked: `0` sorries, `0` axioms.  Builds on the verified parent file.
-/

namespace AutomorphicNumberOQ01OQ01

open Finset AutomorphicNumberOQ01 ArithmeticFunction

/-- The arithmetic function `n ↦ #{idempotents of ZMod n}`.  By the arithmetic-function
convention the value at `0` is set to `0` (so that it is a genuine `ArithmeticFunction`);
all results below concern `n ≥ 1`, where the value is the honest idempotent count. -/
noncomputable def numIdem : ArithmeticFunction ℕ :=
  ⟨fun n => if n = 0 then 0 else Nat.card {e : ZMod n // e * e = e}, by simp⟩

@[simp] lemma numIdem_apply (n : ℕ) :
    numIdem n = if n = 0 then 0 else Nat.card {e : ZMod n // e * e = e} := rfl

/-- For `n ≥ 1`, `numIdem n` is exactly the number of idempotents of `ZMod n`. -/
lemma numIdem_pos {n : ℕ} (hn : n ≠ 0) :
    numIdem n = Nat.card {e : ZMod n // e * e = e} := by
  rw [numIdem_apply, if_neg hn]

/-- `ZMod 1` is trivial, so its unique element is the only idempotent. -/
lemma numIdem_one : numIdem 1 = 1 := by
  rw [numIdem_pos one_ne_zero, Nat.card_eq_fintype_card]
  decide

/-- The idempotent count of a prime power is `2` — the parent's `idem_card_prime_pow`. -/
lemma numIdem_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    numIdem (p ^ k) = 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.pos.ne'⟩
  rw [numIdem_pos (pow_ne_zero k hp.pos.ne'), Nat.card_eq_fintype_card]
  exact idem_card_prime_pow hk

/-- Idempotent counts multiply across coprime moduli, via the Chinese Remainder
isomorphism (`idemCongr`) and componentwise splitting over a product (`idemProd`). -/
lemma numIdem_mul_coprime {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (h : m.Coprime n) :
    numIdem (m * n) = numIdem m * numIdem n := by
  rw [numIdem_pos (mul_ne_zero hm hn), numIdem_pos hm, numIdem_pos hn,
      Nat.card_congr (idemCongr (ZMod.chineseRemainder h).toMulEquiv),
      Nat.card_congr (idemProd (R := ZMod m) (S := ZMod n)),
      Nat.card_prod]

/-- `numIdem` is a multiplicative arithmetic function. -/
lemma numIdem_isMultiplicative : numIdem.IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  exact ⟨numIdem_one, fun hm hn h => numIdem_mul_coprime hm hn h⟩

/-- **Main theorem (arithmetic-function form).** For every `n ≥ 1`,
`numIdem n = 2 ^ ω(n)`, where `ω(n) = n.primeFactors.card`. -/
theorem numIdem_eq_two_pow (n : ℕ) (hn : 0 < n) :
    numIdem n = 2 ^ n.primeFactors.card := by
  rw [numIdem_isMultiplicative.multiplicative_factorization numIdem hn.ne']
  have hterm : n.factorization.prod (fun p k => numIdem (p ^ k))
      = n.factorization.prod (fun _ _ => 2) := by
    apply Finsupp.prod_congr
    intro p hp
    have hk : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp
    rw [Nat.support_factorization] at hp
    exact numIdem_prime_pow (Nat.prime_of_mem_primeFactors hp) (Nat.pos_of_ne_zero hk)
  rw [hterm, Finsupp.prod, Finset.prod_const, Nat.support_factorization]

/-- **Main theorem.** The number of idempotents of `ZMod n` — equivalently, the number of
`automorphic` residues `e ^ 2 ≡ e (mod n)` — is `2 ^ ω(n)`, where `ω(n)` is the number of
distinct primes dividing `n`. -/
theorem idempotent_count (n : ℕ) (hn : 0 < n) :
    Nat.card {e : ZMod n // e * e = e} = 2 ^ n.primeFactors.card := by
  rw [← numIdem_pos hn.ne', numIdem_eq_two_pow n hn]

/-- The count is `2` exactly when `n` is a prime power (one distinct prime). -/
theorem idempotent_count_prime_pow {p : ℕ} (hp : p.Prime) {k : ℕ} (hk : 0 < k) :
    Nat.card {e : ZMod (p ^ k) // e * e = e} = 2 := by
  rw [← numIdem_pos (pow_ne_zero k hp.pos.ne'), numIdem_prime_pow hp hk]

/-- `10 ^ k` has exactly the two prime factors `2` and `5`. -/
lemma primeFactors_ten_pow {k : ℕ} (hk : 0 < k) :
    (10 ^ k).primeFactors.card = 2 := by
  rw [Nat.primeFactors_pow 10 hk.ne', show (10 : ℕ) = 2 * 5 from rfl,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 2),
      Nat.Prime.primeFactors (by norm_num : Nat.Prime 5)]
  decide

/-- **Recovers the parent's count.** Since `ω(10 ^ k) = 2`, the modulus `10 ^ k` has
`2 ^ 2 = 4` automorphic residues — the four idempotents `0, 1, …5, …6`. -/
theorem automorphic_count_ten_pow (k : ℕ) (hk : 0 < k) :
    Nat.card {e : ZMod (10 ^ k) // e * e = e} = 4 := by
  have hpos : 0 < (10 : ℕ) ^ k := pow_pos (by norm_num) k
  rw [idempotent_count _ hpos, primeFactors_ten_pow hk]
  norm_num

end AutomorphicNumberOQ01OQ01
