/-
  Erdős Problem #729 — OQ-02 follow-up: the GENERAL-prime Legendre recurrences.

  Companion to `Erdos729Problem.lean`, `Erdos729LegendreGeneral.lean`, and the
  `p = 2` companion `Erdos729LegendreRecurrence.lean` (PR #27257).

  The `p = 2` companion proved the *2-adic* doubling recurrences
  `v_2((2n)!) = n + v_2(n!)`, `v_2((2n+1)!) = n + v_2(n!)`, the digit-sum
  invariants `s_2(2n) = s_2(n)`, `s_2(2n+1) = s_2(n)+1`, and the maximality
  `v_2(n!) = n-1 ⟺ s_2(n) = 1`. This file lifts ALL of those to an arbitrary
  prime `p`, unifying the even/odd split into a single statement.

  ## Results (all 0 axioms / 0 sorries / 0 `native_decide`)

  * `digitSum_prime_mul_add p n r (hr : r < p)` :
        `s_p(p·n + r) = s_p(n) + r`           (base-`p` left-shift adds a digit `r`)
  * `digitSum_prime_mul p n` :
        `s_p(p·n) = s_p(n)`                    (the `r = 0` corollary)
  * `padicValNat_factorial_prime_mul_add p n r (hr : r < p)` :
        `v_p((p·n + r)!) = n + v_p(n!)`        (general doubling recurrence — the
        value is INDEPENDENT of the residue `r`, so the whole block
        `pn, pn+1, …, pn+(p-1)` shares one valuation increment `n`)
  * `padicValNat_factorial_prime_mul p n` :
        `v_p((p·n)!) = n + v_p(n!)`            (the `r = 0` corollary)
  * `sub_one_mul_padicValNat_factorial_eq_pred_iff p n (hn : 1 ≤ n)` :
        `(p-1)·v_p(n!) = n - 1 ⟺ s_p(n) = 1`  (maximality)
  * `digitSum_pos p m (hm : m ≠ 0)` :
        `0 < s_p(m)`                          (nonzero numbers have positive digit sum)
  * `digitSum_prime_pow p k` :
        `s_p(p^k) = 1`                        (a prime power is a single leading `1`)
  * `digitSum_eq_one_iff_isPow p n` :
        `s_p(n) = 1 ⟺ ∃ k, n = p^k`           (the digit-sum-one characterization —
        previously DELEGATED here and in the `p = 2` companion, now proven)
  * `sub_one_mul_padicValNat_factorial_eq_pred_iff_isPow p n (hn : 1 ≤ n)` :
        `(p-1)·v_p(n!) = n - 1 ⟺ ∃ k, n = p^k`  (maximality in fully-closed form:
        `v_p(n!)` attains Legendre's ceiling exactly at the powers of `p`)

  ## The bridge

  Everything rests on Mathlib's multiplied Legendre theorem
  `sub_one_mul_padicValNat_factorial [Fact p.Prime] (n) :`
  `(p - 1) * padicValNat p (n!) = n - (p.digits n).sum`
  (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:587`) together with the
  base-`p` digit recursion `Nat.digits_def'` (`Data/Nat/Digits/Defs.lean:115`).
  The doubling recurrence is then a one-line cancellation of `p - 1 > 0` after
  observing `s_p(p·n + r) = s_p(n) + r` and `(p-1)·n + n = p·n`.

  None of the named results are Mathlib lemmas.

  Bearer lemmas verified against the Mathlib pin `v4.26.0`:
  `sub_one_mul_padicValNat_factorial`,
  `sub_one_mul_padicValNat_factorial_lt_of_ne_zero`,
  `Nat.digits_def'`, `Nat.digit_sum_le`, `Nat.add_mul_mod_self_left`,
  `Nat.mul_add_div`, `Nat.sub_one_mul`, `Nat.le_mul_of_pos_left`, `List.sum_cons`,
  `Nat.digits_base_pow_mul`, `Nat.digits_of_lt`, `Nat.getLast_digit_ne_zero`,
  `Nat.digits_ne_nil_iff_ne_zero`, `List.le_sum_of_mem`, `Nat.strong_induction_on`.
-/

import Mathlib

namespace Erdos729LegendrePrime

open Nat

/-- Base-`p` digit-sum left-shift law: appending the residue `r < p` as a new
    least-significant digit adds exactly `r` to the digit sum.
    `s_p(p·n + r) = s_p(n) + r`. -/
theorem digitSum_prime_mul_add (p n r : ℕ) (hp : 1 < p) (hr : r < p) :
    (Nat.digits p (p * n + r)).sum = (Nat.digits p n).sum + r := by
  rcases Nat.eq_zero_or_pos (p * n + r) with h0 | hpos
  · -- `p·n + r = 0` forces `n = 0` and then `r = 0`
    have hn0 : n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact h
      · have : 0 < p * n := Nat.mul_pos (by omega) h
        omega
    subst hn0
    simp only [Nat.mul_zero, Nat.zero_add] at h0
    subst h0
    simp
  · rw [Nat.digits_def' hp hpos]
    have hmod : (p * n + r) % p = r := by
      rw [Nat.add_comm (p * n) r, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]
    have hdiv : (p * n + r) / p = n := by
      rw [Nat.mul_add_div (by omega : 0 < p), Nat.div_eq_of_lt hr, Nat.add_zero]
    rw [hmod, hdiv, List.sum_cons]
    omega

/-- Special case `r = 0`: multiplying by `p` is a pure left-shift, so the base-`p`
    digit sum is invariant. `s_p(p·n) = s_p(n)`. -/
theorem digitSum_prime_mul (p n : ℕ) (hp : 1 < p) :
    (Nat.digits p (p * n)).sum = (Nat.digits p n).sum := by
  simpa using digitSum_prime_mul_add p n 0 hp (by omega)

/-- **General-prime doubling recurrence.** For every prime `p`, residue `r < p`,
    and `n`, the `p`-adic valuation of `(p·n + r)!` exceeds that of `n!` by
    exactly `n` — *independent of the residue* `r`:
        `v_p((p·n + r)!) = n + v_p(n!)`.
    Specializing `p = 2` recovers both `v_2((2n)!) = n + v_2(n!)` (`r = 0`) and
    `v_2((2n+1)!) = n + v_2(n!)` (`r = 1`). -/
theorem padicValNat_factorial_prime_mul_add
    (p n r : ℕ) [hp : Fact p.Prime] (hr : r < p) :
    padicValNat p (p * n + r).factorial = n + padicValNat p n.factorial := by
  have hp1 : 1 < p := hp.out.one_lt
  have hSle : (Nat.digits p n).sum ≤ n := Nat.digit_sum_le p n
  have hnle : n ≤ p * n := Nat.le_mul_of_pos_left n (by omega)
  have hpm : (p - 1) * n + n = p * n := by
    rw [Nat.sub_one_mul]; exact Nat.sub_add_cancel hnle
  -- multiply both sides by `p - 1` and cancel the positive factor
  have key : (p - 1) * padicValNat p (p * n + r).factorial
      = (p - 1) * (n + padicValNat p n.factorial) := by
    rw [sub_one_mul_padicValNat_factorial (p * n + r), Nat.mul_add,
      sub_one_mul_padicValNat_factorial n, digitSum_prime_mul_add p n r hp1 hr]
    omega
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-- Special case `r = 0`: `v_p((p·n)!) = n + v_p(n!)`. -/
theorem padicValNat_factorial_prime_mul
    (p n : ℕ) [hp : Fact p.Prime] :
    padicValNat p (p * n).factorial = n + padicValNat p n.factorial := by
  simpa using padicValNat_factorial_prime_mul_add p n 0 hp.out.pos

/-- **Maximality characterization.** For `n ≥ 1`, the `p`-adic valuation of `n!`
    attains the ceiling allowed by Legendre's bound `(p-1)·v_p(n!) < n` — namely
    `(p-1)·v_p(n!) = n - 1` — exactly when the base-`p` digit sum is `1`, i.e.
    `n` is a power of `p`. (The equivalence `s_p(n) = 1 ⟺ n = p^k` is delegated,
    as in the `p = 2` Kummer companion.) -/
theorem sub_one_mul_padicValNat_factorial_eq_pred_iff
    (p n : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) :
    (p - 1) * padicValNat p n.factorial = n - 1 ↔ (Nat.digits p n).sum = 1 := by
  have hSle : (Nat.digits p n).sum ≤ n := Nat.digit_sum_le p n
  have hSpos : 1 ≤ (Nat.digits p n).sum := by
    have hlt := sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (n := n) (by omega)
    rw [sub_one_mul_padicValNat_factorial n] at hlt
    omega
  rw [sub_one_mul_padicValNat_factorial n]
  omega

/-- **Digit-sum positivity.** For `1 < p` and `m ≠ 0` the base-`p` digit sum is
    positive.  The digit list of a nonzero `m` is nonempty and its top (last) digit
    is nonzero (`Nat.getLast_digit_ne_zero`); since every digit is `≥ 0`, that
    nonzero top digit is a lower bound for the whole sum. -/
theorem digitSum_pos (p m : ℕ) (hp : 1 < p) (hm : m ≠ 0) :
    0 < (Nat.digits p m).sum := by
  have hne : Nat.digits p m ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hm
  have hmem : (Nat.digits p m).getLast hne ∈ Nat.digits p m := List.getLast_mem hne
  have hlast : (Nat.digits p m).getLast hne ≠ 0 := Nat.getLast_digit_ne_zero p hm
  have hle : (Nat.digits p m).getLast hne ≤ (Nat.digits p m).sum := List.le_sum_of_mem hmem
  omega

/-- **The digit sum of a prime power is `1`.** In base `p`, `p^k` is a single
    leading `1` followed by `k` trailing zeros (`Nat.digits_base_pow_mul` with the
    unit part `m = 1`), so `s_p(p^k) = 1`.  This is the easy direction of the
    digit-sum-one characterization. -/
theorem digitSum_prime_pow (p k : ℕ) (hp : 1 < p) :
    (Nat.digits p (p ^ k)).sum = 1 := by
  have h := Nat.digits_base_pow_mul (b := p) (k := k) (m := 1) hp (by norm_num)
  rw [Nat.mul_one] at h
  rw [h, List.sum_append, Nat.digits_of_lt p 1 (by norm_num) hp]
  simp

/-- **Forward direction of the digit-sum-one characterization.** If the base-`p`
    digit sum of `n` is `1` then `n` is a power of `p`.  Strong induction on `n`
    via the left-shift law `s_p(p·q + r) = s_p(q) + r`: writing `n = p·(n/p) + n%p`
    forces the low digit `n%p ∈ {0,1}`.  When `n%p = 1` the remaining digit sum is
    `0`, so `n/p = 0` (`digitSum_pos`) and `n = 1 = p^0`; when `n%p = 0` the quotient
    `n/p` again has digit sum `1` and, being smaller, is a power `p^j` by induction,
    whence `n = p^{j+1}`. -/
theorem isPow_of_digitSum_eq_one (p : ℕ) (hp : 1 < p) :
    ∀ n, (Nat.digits p n).sum = 1 → ∃ k, n = p ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hs
    have hn0 : n ≠ 0 := by rintro rfl; simp at hs
    have hrlt : n % p < p := Nat.mod_lt n (by omega)
    have hdecomp : p * (n / p) + n % p = n := Nat.div_add_mod n p
    -- `s_p(n) = s_p(n/p) + n%p`
    have hsplit : (Nat.digits p (n / p)).sum + n % p = 1 := by
      have hh := digitSum_prime_mul_add p (n / p) (n % p) hp hrlt
      rw [hdecomp] at hh
      rw [← hh]; exact hs
    rcases Nat.eq_zero_or_pos (n % p) with hr0 | hrpos
    · -- `n%p = 0`: `s_p(n/p) = 1`; recurse on the strictly smaller `n/p`.
      rw [hr0, Nat.add_zero] at hsplit
      have hlt : n / p < n := Nat.div_lt_self (by omega) hp
      obtain ⟨j, hj⟩ := ih (n / p) hlt hsplit
      have hnp : p * (n / p) = n := by rw [hr0] at hdecomp; simpa using hdecomp
      exact ⟨j + 1, by rw [← hnp, hj, pow_succ]; ring⟩
    · -- `n%p ≥ 1`: forces `n%p = 1` and `s_p(n/p) = 0`, so `n/p = 0` and `n = p^0`.
      have hr1 : n % p = 1 := by omega
      have hsum0 : (Nat.digits p (n / p)).sum = 0 := by omega
      have hnp0 : n / p = 0 := by
        by_contra hc
        have := digitSum_pos p (n / p) hp hc
        omega
      exact ⟨0, by rw [pow_zero, ← hdecomp, hnp0, Nat.mul_zero, Nat.zero_add, hr1]⟩

/-- **Digit-sum-one characterization (fills the delegated equivalence).** For every
    base `1 < p`,
        `s_p(n) = 1  ↔  ∃ k, n = p^k`,
    i.e. a natural number has base-`p` digit sum `1` exactly when it is a power of
    `p`.  This discharges the equivalence `s_p(n) = 1 ⟺ n = p^k` that the
    maximality lemma `sub_one_mul_padicValNat_factorial_eq_pred_iff` (and its `p = 2`
    Kummer companion) previously left delegated. -/
theorem digitSum_eq_one_iff_isPow (p n : ℕ) (hp : 1 < p) :
    (Nat.digits p n).sum = 1 ↔ ∃ k, n = p ^ k := by
  constructor
  · exact isPow_of_digitSum_eq_one p hp n
  · rintro ⟨k, rfl⟩; exact digitSum_prime_pow p k hp

/-- **Maximality of `v_p(n!)` ⟺ `n` is a power of `p`.** Combining the digit-sum
    maximality characterization `sub_one_mul_padicValNat_factorial_eq_pred_iff` with
    the now-proven `digitSum_eq_one_iff_isPow`: for `n ≥ 1`, Legendre's bound
    `(p-1)·v_p(n!) ≤ n - 1` is attained with equality exactly when `n = p^k`.  This
    is the fully-closed form of the maximality statement — no delegated step. -/
theorem sub_one_mul_padicValNat_factorial_eq_pred_iff_isPow
    (p n : ℕ) [hp : Fact p.Prime] (hn : 1 ≤ n) :
    (p - 1) * padicValNat p n.factorial = n - 1 ↔ ∃ k, n = p ^ k := by
  rw [sub_one_mul_padicValNat_factorial_eq_pred_iff p n hn,
    digitSum_eq_one_iff_isPow p n hp.out.one_lt]

/-- Sanity instance: `p = 2` doubling recurrence falls out of the general one. -/
example (n : ℕ) :
    padicValNat 2 (2 * n).factorial = n + padicValNat 2 n.factorial := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat_factorial_prime_mul 2 n

end Erdos729LegendrePrime
