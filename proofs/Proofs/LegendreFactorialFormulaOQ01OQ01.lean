/-
# Kummer's Carry-Count Theorem for Binomial Valuations

Kummer's theorem gives a strikingly combinatorial description of the exact power
of a prime `p` dividing a binomial coefficient:

  `vₚ(C(n,k))` = the number of **carries** that occur when adding `k` and `n − k`
  in base `p`.

This is the binomial-coefficient companion of the parent entry's packaging of
Legendre's factorial formula `vₚ(n!) = (n − Sₚ(n))/(p − 1)`.  Mathlib already
proves the underlying identity (`Nat.factorization_choose`), where the carry count
appears as the cardinality of

  `{ i ≥ 1 : pⁱ ≤ (k mod pⁱ) + ((n − k) mod pⁱ) }`.

The predicate `pⁱ ≤ (k mod pⁱ) + ((n − k) mod pⁱ)` is exactly the statement that a
carry propagates into base-`p` digit position `i`, so the cardinality is the carry
count.  This entry isolates a named `carryCount` definition, restates Kummer's
theorem in the parent's `padicValNat` style, and derives two classical corollaries:

* **Divisibility criterion**: `p ∣ C(n,k)` iff adding `k` and `n − k` in base `p`
  produces at least one carry (equivalently, `C(n,k)` is coprime to `p` iff the
  addition is carry-free — the digit-wise Lucas condition).
* **Central binomial coefficient**: `vₚ(C(2n, n))` equals the number of carries in
  the base-`p` self-addition `n + n`, and `p ∣ C(2n, n)` iff that addition carries.

All results are fully verified with no `sorry` and no extra axioms (the single
numerical `decide` is kernel reduction on a small `Finset`, so `Lean.ofReduceBool`
is not used).
-/

import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Padics.PadicVal.Basic

open Nat Finset

namespace LegendreFactorialFormulaOQ01OQ01

variable {p : ℕ}

/-- **Base-`p` carry count.**
The number of carries produced when adding `a` and `b` in base `p`, counted over
digit positions `1 ≤ i < bound`.  A carry propagates into position `i` precisely
when the truncated sum `(a mod pⁱ) + (b mod pⁱ)` reaches the modulus `pⁱ`; this is
Kummer's carry indicator.  Any `bound` exceeding `log p (a + b)` captures every
carry (for larger `i` both summands are taken mod `pⁱ > a + b`, so no carry
occurs), matching the bound used by Mathlib's `Nat.factorization_choose`. -/
def carryCount (p a b bound : ℕ) : ℕ :=
  #{i ∈ Finset.Ico 1 bound | p ^ i ≤ a % p ^ i + b % p ^ i}

/-- **Kummer's theorem.**
For a prime `p`, `k ≤ n`, and any bound `b` strictly above `log p n`, the `p`-adic
valuation of `C(n,k)` equals the number of carries when adding `k` and `n − k` in
base `p`.  This is the binomial analogue of Legendre's factorial formula. -/
theorem padicValNat_choose_eq_carryCount [hp : Fact p.Prime] {n k b : ℕ}
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    padicValNat p (n.choose k) = carryCount p k (n - k) b := by
  rw [← Nat.factorization_def _ hp.out, Nat.factorization_choose hp.out hkn hnb]
  rfl

/-- **Kummer's divisibility criterion.**
A prime `p` divides `C(n,k)` iff adding `k` and `n − k` in base `p` produces at
least one carry. -/
theorem prime_dvd_choose_iff_carryCount_pos [hp : Fact p.Prime] {n k b : ℕ}
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    p ∣ n.choose k ↔ 0 < carryCount p k (n - k) b := by
  have hne : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  rw [hp.out.dvd_iff_one_le_factorization hne, Nat.factorization_def _ hp.out,
    padicValNat_choose_eq_carryCount hkn hnb]
  omega

/-- **Carry-free corollary (Lucas condition).**
`C(n,k)` is coprime to `p` iff the base-`p` addition of `k` and `n − k` is
carry-free.  This is the divisibility criterion in contrapositive form. -/
theorem not_dvd_choose_iff_carryCount_eq_zero [hp : Fact p.Prime] {n k b : ℕ}
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    ¬ p ∣ n.choose k ↔ carryCount p k (n - k) b = 0 := by
  rw [prime_dvd_choose_iff_carryCount_pos hkn hnb]; omega

/-- **Central binomial coefficient via carries.**
The `p`-adic valuation of `C(2n, n)` equals the number of carries in the base-`p`
self-addition `n + n`. -/
theorem padicValNat_centralBinom_eq_carryCount [hp : Fact p.Prime] {n b : ℕ}
    (hnb : Nat.log p (2 * n) < b) :
    padicValNat p (centralBinom n) = carryCount p n n b := by
  have hkn : n ≤ 2 * n := by omega
  have e : 2 * n - n = n := by omega
  show padicValNat p ((2 * n).choose n) = carryCount p n n b
  rw [← Nat.factorization_def _ hp.out, Nat.factorization_choose hp.out hkn hnb, e]
  rfl

/-- **Divisibility of the central binomial coefficient.**
A prime `p` divides `C(2n, n)` iff adding `n` to itself in base `p` carries.  Since
every prime in `(n, 2n]` forces such a carry, this recovers the classical fact that
`C(2n, n)` is divisible by all primes in that range. -/
theorem prime_dvd_centralBinom_iff_carryCount_pos [hp : Fact p.Prime] {n b : ℕ}
    (hnb : Nat.log p (2 * n) < b) :
    p ∣ centralBinom n ↔ 0 < carryCount p n n b := by
  have hne : centralBinom n ≠ 0 := (Nat.centralBinom_pos n).ne'
  rw [hp.out.dvd_iff_one_le_factorization hne, Nat.factorization_def _ hp.out,
    padicValNat_centralBinom_eq_carryCount hnb]
  omega

/-- Worked instance: `v₂(C(4,2)) = v₂(6) = 1`.
Adding `2 + 2 = 100₂` in base `2` carries exactly once (out of the units place into
the `4`s place), so the carry count — and hence the valuation — is `1`. -/
example : padicValNat 2 ((4).choose 2) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [padicValNat_choose_eq_carryCount (p := 2) (n := 4) (k := 2) (b := 4)
    (by norm_num) (Nat.log_lt_of_lt_pow (by norm_num) (by norm_num))]
  decide

end LegendreFactorialFormulaOQ01OQ01
