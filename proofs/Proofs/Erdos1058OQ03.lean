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

/-! ## The sharp composite companion: composites (except `4`) divide `(n-1)!`

  The obstruction `not_dvd_factorial_add_one_of_dvd_factorial` shows only that a
  *proper* divisor of `n!` cannot divide `n! + 1`.  Here we prove the sharper
  positive companion to Wilson: a composite modulus (with the single exception
  `n = 4`) divides `(n-1)!` *outright*.  Combined with Wilson's `(n-1)! ≡ -1` for
  primes, this pins down the residue of `(n-1)!` modulo `n` in every case, and
  gives the "divisibility form" of Wilson's primality test:
      `n ∣ (n-1)!  ↔  n composite`   (for `2 ≤ n`, `n ≠ 4`).
  Mathlib's own Wilson proof only extracts a proper divisor, so this full
  divisibility statement is not available upstream. -/

/-- If `0 < p < q ≤ m`, the **product** `p * q` divides `m !`.  Two distinct
    factors below `m` both occur in `m ! = 1·2·⋯·m`, so their product divides it.
    This is the combinatorial heart of the composite case: `p ∣ (q-1)!` and `q`
    itself supplies the second factor of `q ! ∣ m !`. -/
theorem mul_dvd_factorial_of_lt {p q m : ℕ}
    (hp : 0 < p) (hpq : p < q) (hq : q ≤ m) : p * q ∣ m ! := by
  obtain ⟨k, hk⟩ : p ∣ (q - 1)! := Nat.dvd_factorial hp (by omega)
  have hqfac : q * (q - 1)! = q ! := Nat.mul_factorial_pred (by omega)
  have hpq' : p * q ∣ q ! := ⟨k, by rw [← hqfac, hk]; ring⟩
  exact hpq'.trans (Nat.factorial_dvd_factorial hq)

/-- **Composite companion to Wilson.**  Every composite modulus except `4`
    divides `(n-1)!`.  Precisely: if `2 ≤ n`, `n` is not prime, and `n ≠ 4`, then
    `n ∣ (n-1)!`.  The proof splits `n = a·b` at its least prime factor `a`; when
    the two factors differ they contribute distinct terms to `(n-1)!`, and the
    square case `n = a²` (with `a ≥ 3`, forced by `n ≠ 4`) uses the distinct
    factors `a` and `2a`. -/
theorem dvd_factorial_pred_of_composite {n : ℕ}
    (hn : 2 ≤ n) (hnp : ¬ n.Prime) (hn4 : n ≠ 4) : n ∣ (n - 1)! := by
  set a := n.minFac with ha
  have hn1 : n ≠ 1 := by omega
  have hap : a.Prime := Nat.minFac_prime hn1
  have hadvd : a ∣ n := Nat.minFac_dvd n
  have ha2 : 2 ≤ a := hap.two_le
  -- `a` is a *proper* divisor, since `n` is not prime.
  have hane : a ≠ n := fun h => hnp (Nat.prime_def_minFac.mpr ⟨hn, h⟩)
  set b := n / a with hb
  have hab : a * b = n := Nat.mul_div_cancel' hadvd
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, Nat.mul_zero] at hab; omega
    · exact h
  have hbdvd : b ∣ n := ⟨a, by rw [← hab]; ring⟩
  have hb2 : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with h | h
    · have hb1 : b = 1 := by omega
      rw [hb1, Nat.mul_one] at hab; exact absurd hab hane
    · exact h
  -- `a` is the least prime factor, so `a ≤ b`.
  have haleb : a ≤ b := Nat.minFac_le_of_dvd hb2 hbdvd
  have hbltn : b < n := by nlinarith [hab, ha2, hb0]
  rcases lt_or_eq_of_le haleb with hlt | heq
  · -- Distinct factors `a < b`, both `≤ n-1`.
    have hd := mul_dvd_factorial_of_lt (by omega : 0 < a) hlt (by omega : b ≤ n - 1)
    rwa [hab] at hd
  · -- Square case `n = a²`, with `a ≥ 3` since `n ≠ 4`.
    have hnaa : n = a * a := by rw [← hab, ← heq]
    have ha3 : 3 ≤ a := by
      rcases Nat.lt_or_ge a 3 with h | h
      · have ha2' : a = 2 := by omega  -- a = 2 forces n = 4, contradicting hn4
        rw [ha2'] at hnaa; omega
      · exact h
    have h3a : 3 * a ≤ a * a := by nlinarith [ha3]
    have h2a : 2 * a ≤ n - 1 := by omega
    have hd := mul_dvd_factorial_of_lt (by omega : 0 < a) (by omega : a < 2 * a) h2a
    have hn_dvd : n ∣ a * (2 * a) := ⟨2, by rw [hnaa]; ring⟩
    exact hn_dvd.trans hd

/-- **Full residue classification (composite case).**  For a composite modulus
    `n ≠ 4` (with `2 ≤ n`), `(n-1)! ≡ 0 (mod n)`.  This complements Wilson's
    `(n-1)! ≡ -1` for primes; the two exhaust every `n ≥ 2` except `n = 4`, where
    `3! = 6 ≡ 2`. -/
theorem factorial_pred_zmod_eq_zero_of_composite {n : ℕ}
    (hn : 2 ≤ n) (hnp : ¬ n.Prime) (hn4 : n ≠ 4) : ((n - 1)! : ZMod n) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact dvd_factorial_pred_of_composite hn hnp hn4

/-- **Wilson's primality test, divisibility form.**  For `2 ≤ n` with `n ≠ 4`,
    `n` divides `(n-1)!` *iff* `n` is composite.  This is the exact complement of
    the flagship shifted characterisation `(n+1) ∣ n! + 1 ↔ (n+1).Prime`: Wilson
    forces `(n-1)! ≡ -1` for primes (never `0` when `n ≥ 2`), and
    `dvd_factorial_pred_of_composite` supplies the `≡ 0` for composites. -/
theorem dvd_factorial_pred_iff_not_prime {n : ℕ} (hn : 2 ≤ n) (hn4 : n ≠ 4) :
    n ∣ (n - 1)! ↔ ¬ n.Prime := by
  refine ⟨fun hdvd hp => ?_, fun hnp => dvd_factorial_pred_of_composite hn hnp hn4⟩
  haveI := Fact.mk hp
  have hz : ((n - 1)! : ZMod n) = 0 := by rw [ZMod.natCast_eq_zero_iff]; exact hdvd
  have hw : ((n - 1)! : ZMod n) = -1 := ZMod.wilsons_lemma n
  rw [hz] at hw
  exact one_ne_zero (by linear_combination hw : (1 : ZMod n) = 0)

end Erdos1058OQ03
