import Mathlib
import Proofs.AutomorphicNumberOQ01

/-!
# Idempotents of `ZMod (m ^ k)`: the count is `2 ^ ω(m)`

## What This Proves

The parent entry `automorphic-number-oq-01-oq-02` pins down the idempotents of
`ZMod (10 ^ k)` — the automorphic residues `n² ≡ n (mod 10^k)` — showing there are
exactly **four**, split into two complementary pairs.  The first follow-up
(`AutomorphicNumberOQ01`) reframed that count as `2 ^ ω(10) = 2²` and proved, for a
single prime power, that `ZMod (p ^ a)` has exactly two idempotents.

This entry removes the base `10` entirely and settles the count for an **arbitrary**
modulus `m ≥ 2`:

```
card_idempotents_eq_two_pow_omega :
  Fintype.card {e : ZMod (m ^ k) // e * e = e} = 2 ^ m.primeFactors.card
```

Here `m.primeFactors.card = ω(m)` is the number of distinct prime divisors of `m`.
The exponent `k ≥ 1` never appears on the right — the count depends only on `ω(m)`.
So `ZMod (12 ^ k)` (`12 = 2²·3`, two primes) has `4` idempotents, `ZMod (30 ^ k)`
(`30 = 2·3·5`, three primes) has `8`, and `ZMod (p ^ k)` for a prime power has only the
trivial two.

## Strategy

The proof is the structural statement of which the parent's `10^k` computation is a
shadow, assembled from three reusable pieces:

* **Local factors have two idempotents.**  `AutomorphicNumberOQ01.idem_card_prime_pow`
  already proves `Fintype.card {a : ZMod (p^a) // a*a=a} = 2` for prime `p`, `a ≥ 1`
  (a prime-power ring is local, so `a*(a-1)=0` forces `a ∈ {0,1}`).
* **Chinese Remainder over all primes.**  `ZMod.equivPi` gives the ring isomorphism
  `ZMod (m^k) ≃+* Π p ∈ (m^k).primeFactors, ZMod (p ^ v_p(m^k))`.
* **Idempotents of a product are families of idempotents.**  `idemPi` (below, the
  dependent-product analogue of the parent's binary `idemProd`) turns the idempotent
  subtype of a `Π`-ring into the product of the factors' idempotent subtypes, so the
  count multiplies: `∏_{p} 2 = 2 ^ #primeFactors(m^k) = 2 ^ ω(m)`.

The complementation involution `e ↦ 1 - e` (Mathlib's `HasCompl`/`compl_compl` on the
idempotent subtype) is recorded as `compl_involutive`.

## Status

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace AutomorphicNumberOQ01OQ02OQ01

open Finset AutomorphicNumberOQ01

/-- An idempotent of a dependent product ring is exactly a family of idempotents of the
factors.  This is the `Π`-type analogue of the parent's binary `idemProd`. -/
def idemPi {ι : Type*} {R : ι → Type*} [∀ i, Mul (R i)] :
    {e : (∀ i, R i) // e * e = e} ≃ (∀ i, {a : R i // a * a = a}) where
  toFun e i := ⟨e.1 i, by have h := congrFun e.2 i; rwa [Pi.mul_apply] at h⟩
  invFun f := ⟨fun i => (f i).1, funext fun i => by rw [Pi.mul_apply]; exact (f i).2⟩
  left_inv e := by ext i; rfl
  right_inv f := by ext i; rfl

/-- **Main theorem.**  For a nonzero modulus `m` (the interesting range is `m ≥ 2`) and
`k ≥ 1`, the ring `ZMod (m ^ k)` has exactly `2 ^ ω(m)` idempotents, where
`ω(m) = m.primeFactors.card` is the number of distinct primes dividing `m`.  The exponent
`k` does not affect the count.  (`[NeZero m]` is required so that `ZMod (m ^ k)` is a finite
type; it holds automatically for any concrete `m ≥ 1`.) -/
theorem card_idempotents_eq_two_pow_omega (m k : ℕ) [NeZero m] (hk : 1 ≤ k) :
    Fintype.card {e : ZMod (m ^ k) // e * e = e} = 2 ^ m.primeFactors.card := by
  have hk0 : k ≠ 0 := by omega
  have hn : m ^ k ≠ 0 := pow_ne_zero k (NeZero.ne m)
  -- Each prime-power factor is a nonzero (hence finite) ring.
  haveI hNZ : ∀ p : (m ^ k).primeFactors,
      NeZero ((p : ℕ) ^ ((m ^ k).factorization (p : ℕ))) :=
    fun p => ⟨pow_ne_zero _ (Nat.prime_of_mem_primeFactors p.2).pos.ne'⟩
  -- Transport idempotents across the Chinese-Remainder product decomposition
  -- (`ZMod.equivPi`), then split them componentwise (`idemPi`).
  rw [Fintype.card_congr ((idemCongr (ZMod.equivPi (m ^ k) hn).toMulEquiv).trans idemPi),
      Fintype.card_pi]
  -- Every local factor contributes exactly two idempotents.
  have hfac : ∀ p : (m ^ k).primeFactors,
      Fintype.card {a : ZMod ((p : ℕ) ^ ((m ^ k).factorization (p : ℕ))) // a * a = a} = 2 := by
    intro p
    haveI : Fact ((p : ℕ).Prime) := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    have hpos : 0 < (m ^ k).factorization (p : ℕ) := by
      obtain ⟨hp, hdvd, -⟩ := Nat.mem_primeFactors.mp p.2
      exact hp.factorization_pos_of_dvd hn hdvd
    exact idem_card_prime_pow hpos
  simp only [hfac]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe, Nat.primeFactors_pow m hk0]

/-- **Complementation involution.**  On the idempotents of `ZMod (m ^ k)` the orthogonal
complement `e ↦ 1 - e` (Mathlib's `HasCompl` on the idempotent subtype) is an involution;
it pairs the `2 ^ ω(m)` idempotents by `e ↔ 1 - e`. -/
theorem compl_involutive (m k : ℕ) :
    Function.Involutive
      (fun e : {e : ZMod (m ^ k) // IsIdempotentElem e} => eᶜ) :=
  fun e => compl_compl e

/-! ## Sanity checks

The count `2 ^ ω(m)` reproduces the known small cases. -/

/-- Base `10 = 2·5` has `ω = 2`, giving `4` idempotents mod `10 ^ k` — the parent's count. -/
example (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card {e : ZMod (10 ^ k) // e * e = e} = 4 := by
  have h : (10 : ℕ).primeFactors.card = 2 := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
    decide
  have key := card_idempotents_eq_two_pow_omega 10 k hk
  rw [h] at key
  exact key

/-- A prime power `m = 3²` still has `ω = 1`, so only the trivial two idempotents. -/
example (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card {e : ZMod (9 ^ k) // e * e = e} = 2 := by
  have h : (9 : ℕ).primeFactors.card = 1 := by
    rw [show (9 : ℕ) = 3 * 3 from rfl, Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors (by norm_num)]
    decide
  have key := card_idempotents_eq_two_pow_omega 9 k hk
  rw [h] at key
  exact key

/-- `30 = 2·3·5` has `ω = 3`, giving `8` idempotents mod `30 ^ k`. -/
example (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card {e : ZMod (30 ^ k) // e * e = e} = 8 := by
  have h : (30 : ℕ).primeFactors.card = 3 := by
    rw [show (30 : ℕ) = 2 * (3 * 5) from rfl,
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.primeFactors_mul (by norm_num) (by norm_num),
        Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
        Nat.Prime.primeFactors (by norm_num)]
    decide
  have key := card_idempotents_eq_two_pow_omega 30 k hk
  rw [h] at key
  exact key

end AutomorphicNumberOQ01OQ02OQ01
