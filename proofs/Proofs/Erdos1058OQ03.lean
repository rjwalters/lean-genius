/-
  Erdős Problem #1058 — Companion (oq-03):
  Extending the factorial-expression technique to `n! ± 1`, axiom-free.

  The parent file `Erdos1058Problem.lean` studies the primes dividing `n! + 1`
  for `n` between consecutive primes (Erdős–Stewart / Luca 2001).  Its entire
  arithmetic content — the prime sequence `prime_seq`, the finiteness conjecture,
  and Luca's classification — is *axiomatized* (`opaque`/`axiom`), so no genuine
  divisibility fact is actually derived there.

  OQ-03 asks whether the underlying *technique* extends to other factorial-based
  expressions.  This companion answers YES and does so with **0 axioms / 0
  sorries**: the engine behind #1058 is Wilson's theorem, and it yields a *complete*
  characterisation of when the natural "shift" `n + 1` divides the factorial-based
  expressions `n! + 1` and its sibling `n! - 1`.

  Main results (all 0 axioms / 0 sorries):
    • `succ_dvd_factorial_add_one_iff_prime` — **flagship**: `(n+1) ∣ n! + 1 ↔
        (n+1).Prime`.  A universal, exact characterisation (the parent only lists
        the five known example values); the composite obstruction falls out for
        free (`not_succ_dvd_factorial_add_one_of_not_prime`).
    • `prime_dvd_factorial_pred_add_one` — the classical Wilson divisibility
        `p ∣ (p-1)! + 1` for prime `p`, phrased for the `+1` expression.
    • `prime_dvd_factorial_pred_sub_one_iff` — the technique transfers to the
        **sibling** `n! - 1`: for prime `p`, `p ∣ (p-1)! - 1 ↔ p = 2`.
    • `not_dvd_factorial_add_one_of_dvd_factorial` — general obstruction: any
        divisor of `n!` bigger than `1` divides neither `n! + 1`.
    • `eq_of_prime_dvd_of_isPrimePow` — reusable: a prime-power has a unique prime
        divisor; used to *prove* (axiom-free) that `6! + 1 = 721 = 7·103` and
        `5! - 1 = 119 = 7·17` are **not** prime powers, alongside the prime-power
        cases `4!+1 = 5²`, `5!+1 = 11²`, `3!-1 = 5`.

  Reference: https://erdosproblems.com/1058
-/

import Mathlib

namespace Erdos1058OQ03

open Nat

/-! ## The general obstruction: a proper divisor of `n!` cannot divide `n! + 1` -/

/-- If `1 < d` divides `n!`, then `d` does not divide `n! + 1`: otherwise `d`
    would divide their difference `1`.  This is the elementary reason that any
    prime `≤ n` is barred from dividing `n! + 1` — the observation underlying
    Erdős–Stewart's restriction to primes near `n`. -/
theorem not_dvd_factorial_add_one_of_dvd_factorial {d n : ℕ}
    (hd : 1 < d) (hdvd : d ∣ n !) : ¬ d ∣ (n ! + 1) := by
  intro h
  have h1 : d ∣ 1 := (Nat.dvd_add_right hdvd).mp h
  exact absurd (Nat.dvd_one.mp h1) (by omega)

/-! ## Wilson's theorem for the `+1` expression -/

/-- **Wilson divisibility.**  For a prime `p`, `p ∣ (p-1)! + 1`.  This is the
    classical statement of Wilson's theorem for the factorial-based expression
    `(p-1)! + 1`. -/
theorem prime_dvd_factorial_pred_add_one {p : ℕ} (hp : p.Prime) :
    p ∣ ((p - 1)! + 1) := by
  haveI := Fact.mk hp
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.wilsons_lemma]
  ring

/-- **Flagship characterisation.**  The shift `n + 1` divides `n! + 1` *exactly
    when* `n + 1` is prime (`n ≥ 1`).  This is the sharp, universal form of the
    parent file's example-by-example computations: it settles the divisibility for
    every `n` at once, both the prime case (Wilson) and the composite case. -/
theorem succ_dvd_factorial_add_one_iff_prime {n : ℕ} (hn : 1 ≤ n) :
    (n + 1) ∣ (n ! + 1) ↔ (n + 1).Prime := by
  have hne : n + 1 ≠ 1 := by omega
  have hpred : (n + 1) - 1 = n := by omega
  rw [Nat.prime_iff_fac_equiv_neg_one hne, hpred, ← ZMod.natCast_eq_zero_iff]
  push_cast
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

/-- **Composite obstruction (corollary).**  If `n + 1` is *not* prime (`n ≥ 1`),
    then `n + 1` does not divide `n! + 1`.  A one-line consequence of the flagship
    characterisation — the exact statement used to rule out composite candidates. -/
theorem not_succ_dvd_factorial_add_one_of_not_prime {n : ℕ} (hn : 1 ≤ n)
    (hnp : ¬ (n + 1).Prime) : ¬ (n + 1) ∣ (n ! + 1) := by
  rw [succ_dvd_factorial_add_one_iff_prime hn]; exact hnp

/-! ## Transferring the technique to the sibling `n! - 1` -/

/-- **The technique extends to `n! - 1`.**  For a prime `p`, the shift `p`
    divides `(p-1)! - 1` if and only if `p = 2`.  (For odd primes Wilson gives
    `(p-1)! ≡ -1`, so `(p-1)! - 1 ≡ -2 ≢ 0`.)  This is the sibling of
    `prime_dvd_factorial_pred_add_one`: the same Wilson engine, a different but
    equally sharp answer. -/
theorem prime_dvd_factorial_pred_sub_one_iff {p : ℕ} (hp : p.Prime) :
    p ∣ ((p - 1)! - 1) ↔ p = 2 := by
  haveI := Fact.mk hp
  have hfac : 1 ≤ (p - 1)! := Nat.factorial_pos (p - 1)
  rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hfac, Nat.cast_one, ZMod.wilsons_lemma,
      show (-1 - 1 : ZMod p) = -((2 : ℕ) : ZMod p) by push_cast; ring, neg_eq_zero,
      ZMod.natCast_eq_zero_iff]
  exact Nat.prime_dvd_prime_iff_eq hp Nat.prime_two

/-! ## Prime-power classification of small values (axiom-free) -/

/-- A prime power has a *unique* prime divisor: if `p, q` are primes dividing a
    prime power `m`, then `p = q`.  Reusable tool for proving that a specific
    number is *not* a prime power (exhibit two distinct prime divisors). -/
theorem eq_of_prime_dvd_of_isPrimePow {m p q : ℕ}
    (h : IsPrimePow m) (hp : p.Prime) (hq : q.Prime)
    (hpm : p ∣ m) (hqm : q ∣ m) : p = q := by
  rw [isPrimePow_nat_iff] at h
  obtain ⟨r, _, hr, _, rfl⟩ := h
  rw [(Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpm),
      (Nat.prime_dvd_prime_iff_eq hq hr).mp (hq.dvd_of_dvd_pow hqm)]

/-- `4! + 1 = 25 = 5²` is a prime power. -/
theorem isPrimePow_four_factorial_add_one : IsPrimePow (4 ! + 1) :=
  (isPrimePow_nat_iff _).mpr ⟨5, 2, by norm_num, by norm_num, by decide⟩

/-- `5! + 1 = 121 = 11²` is a prime power. -/
theorem isPrimePow_five_factorial_add_one : IsPrimePow (5 ! + 1) :=
  (isPrimePow_nat_iff _).mpr ⟨11, 2, by norm_num, by norm_num, by decide⟩

/-- `6! + 1 = 721 = 7 · 103` is **not** a prime power (first failure of the `+1`
    prime-power pattern), proved axiom-free via the two distinct prime divisors
    `7` and `103`. -/
theorem not_isPrimePow_six_factorial_add_one : ¬ IsPrimePow (6 ! + 1) := by
  intro h
  have h7 : (7 : ℕ) ∣ 6 ! + 1 := by decide
  have h103 : (103 : ℕ) ∣ 6 ! + 1 := by decide
  have : (7 : ℕ) = 103 :=
    eq_of_prime_dvd_of_isPrimePow h (by norm_num) (by norm_num) h7 h103
  norm_num at this

/-- Sibling: `3! - 1 = 5` is a (trivial) prime power. -/
theorem isPrimePow_three_factorial_sub_one : IsPrimePow (Nat.factorial 3 - 1) := by
  rw [show Nat.factorial 3 - 1 = 5 by decide]
  exact (by norm_num : Nat.Prime 5).isPrimePow

/-- Sibling: `5! - 1 = 119 = 7 · 17` is **not** a prime power, proved axiom-free
    via the two distinct prime divisors `7` and `17`. -/
theorem not_isPrimePow_five_factorial_sub_one : ¬ IsPrimePow (Nat.factorial 5 - 1) := by
  intro h
  have h7 : (7 : ℕ) ∣ Nat.factorial 5 - 1 := by decide
  have h17 : (17 : ℕ) ∣ Nat.factorial 5 - 1 := by decide
  have : (7 : ℕ) = 17 :=
    eq_of_prime_dvd_of_isPrimePow h (by norm_num) (by norm_num) h7 h17
  norm_num at this

end Erdos1058OQ03
