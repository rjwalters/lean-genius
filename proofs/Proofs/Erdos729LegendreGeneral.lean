/-
  Erdős Problem #729 — OQ-02 follow-up: the GENERAL textbook Legendre identity.

  Companion to `Erdos729Problem.lean`.

  Session S1 (PR #24474) discharged the file's `legendre_identity` *axiom* for the
  single case `p = 2`, proving `legendre_for_two : v_2(n!) = n - s_2(n)` from
  Mathlib's `sub_one_mul_padicValNat_factorial` and *deleting* the general-`p`
  axiom. This file restores the general statement — for EVERY prime `p` — as a
  fully machine-checked theorem (0 axioms / 0 sorries), so the classical

        v_p(n!) = (n - s_p(n)) / (p - 1)            (s_p = base-p digit sum)

  is available in proven form, not just the `p = 2` special case.

  ## The bridge

  Mathlib provides Legendre's theorem only in the *multiplied* form
  `sub_one_mul_padicValNat_factorial [Fact p.Prime] (n) :`
  `(p - 1) * padicValNat p (n!) = n - (p.digits n).sum`
  (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:587`). The classical
  *division* form `v_p(n!) = (n - s_p(n))/(p-1)` is not a named Mathlib lemma:
  it requires `(p-1) ∣ (n - s_p(n))`, which is exactly what the multiplied form
  guarantees. Dividing both sides by `p - 1 > 0` and cancelling
  (`Nat.mul_div_cancel_left`) gives the textbook identity in one step.

  We state it both in Mathlib's native digit sum `(p.digits n).sum` and in the
  recursive `digitSum` shape used by `Erdos729Problem.lean`, bridged by
  `digitSum_eq_digits_sum`.

  Bearer lemmas verified against the Mathlib pin `v4.26.0` (sibling checkout):
  `sub_one_mul_padicValNat_factorial` (PadicVal/Basic.lean:587),
  `Nat.mul_div_cancel_left` (usage form `_ (h : 0 < b)`),
  `Nat.digits_def'` (Data/Nat/Digits/Defs.lean:115), `List.sum_cons`,
  `Nat.div_lt_self`, `Nat.strong_induction_on`, `Nat.pos_of_ne_zero`.
-/

import Mathlib

namespace Erdos729Legendre

open Nat

/-- Base-`p` digit sum, matching `Erdos729Problem.digitSum`.  Defined directly as
`(Nat.digits p n).sum`: the naive recursion `n % p + digitSum p (n / p)` is ill-founded for
`p ≤ 1` (`n / 1 = n` never decreases), so — exactly as the repaired
`Erdos729Problem.digitSum` — we take Mathlib's digit list and sum it. -/
def digitSum (p n : ℕ) : ℕ := (p.digits n).sum

/-- The `digitSum p n` agrees with Mathlib's `(p.digits n).sum`.  Definitional; the `1 < p`
hypothesis is retained for call-site compatibility with the recursive shape. -/
theorem digitSum_eq_digits_sum (p : ℕ) (_hp : 1 < p) (n : ℕ) :
    digitSum p n = (p.digits n).sum := rfl

/-- **Legendre's identity, classical division form (Mathlib digit sum).**

For any prime `p` and any `n`,

  `v_p(n!) = (n - s_p(n)) / (p - 1)`,

where `s_p(n) = (p.digits n).sum`. Derived by dividing the Mathlib lemma
`sub_one_mul_padicValNat_factorial` (`(p-1)·v_p(n!) = n - s_p(n)`) through by
`p - 1`. Mathlib does not state this division form as a named lemma. -/
theorem padicValNat_factorial_eq_div (p n : ℕ) (hp : p.Prime) :
    padicValNat p n.factorial = (n - (p.digits n).sum) / (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  have h := sub_one_mul_padicValNat_factorial (p := p) n
  rw [← h, Nat.mul_div_cancel_left _ hp1]

/-- **Legendre's identity in the recursive `digitSum` shape** (the exact statement
of the `legendre_identity` axiom that S1 deleted, now proven for all primes). -/
theorem legendre_digit_sum_identity (p n : ℕ) (hp : p.Prime) :
    padicValNat p n.factorial = (n - digitSum p n) / (p - 1) := by
  rw [digitSum_eq_digits_sum p hp.one_lt n, padicValNat_factorial_eq_div p n hp]

/-- **Legendre's identity, multiplied form (recursive `digitSum` shape).**
The un-divided companion of `legendre_digit_sum_identity`: `(p-1)·v_p(n!) = n - s_p(n)`, the
recursive-`digitSum` restatement of Mathlib's `sub_one_mul_padicValNat_factorial`. Unlike the
division form it carries no truncated-division rounding, so it is the convenient starting
point for Kummer-type valuation arguments. -/
theorem sub_one_mul_padicValNat_factorial_digitSum (p n : ℕ) (hp : p.Prime) :
    (p - 1) * padicValNat p n.factorial = n - digitSum p n := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [digitSum_eq_digits_sum p hp.one_lt n]
  exact sub_one_mul_padicValNat_factorial (p := p) n

/-- **The base-`p` digit-sum defect is divisible by `p - 1`.**
For every prime `p`, `(p - 1) ∣ (n - s_p(n))` — the classical "casting out nines" fact
generalized to base `p` (`n ≡ s_p(n) (mod p - 1)`), here obtained as a corollary of
Legendre's formula: the defect `n - s_p(n)` equals `(p - 1)·v_p(n!)`. -/
theorem sub_one_dvd_sub_digitSum (p n : ℕ) (hp : p.Prime) :
    (p - 1) ∣ (n - digitSum p n) :=
  ⟨padicValNat p n.factorial, (sub_one_mul_padicValNat_factorial_digitSum p n hp).symm⟩

-- The numerical content (v_p(n!) = (n - s_p(n))/(p-1) for many p, n) is certified
-- independently in `research/problems/erdos-729-oq-02/verify_legendre_general.py`
-- (no Lean `decide` on `Nat.digits`, which is well-founded and does not reduce
-- reliably in the kernel).

#check @padicValNat_factorial_eq_div
#check @legendre_digit_sum_identity
#check @sub_one_mul_padicValNat_factorial_digitSum
#check @sub_one_dvd_sub_digitSum

end Erdos729Legendre
