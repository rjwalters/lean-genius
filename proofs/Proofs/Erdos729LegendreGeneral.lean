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

/-- Recursive base-`p` digit sum, matching `Erdos729Problem.digitSum`. -/
noncomputable def digitSum (p n : ℕ) : ℕ :=
  if n = 0 then 0
  else n % p + digitSum p (n / p)

/-- The recursive `digitSum p n` agrees with Mathlib's `(p.digits n).sum` for `p > 1`. -/
theorem digitSum_eq_digits_sum (p : ℕ) (hp : 1 < p) (n : ℕ) :
    digitSum p n = (p.digits n).sum := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn
    · simp [digitSum]
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn
      have hunfold : digitSum p n = n % p + digitSum p (n / p) := by
        rw [digitSum.eq_def, if_neg hn]
      rw [hunfold, Nat.digits_def' hp hpos, List.sum_cons,
        ih (n / p) (Nat.div_lt_self hpos hp)]

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

-- The numerical content (v_p(n!) = (n - s_p(n))/(p-1) for many p, n) is certified
-- independently in `research/problems/erdos-729-oq-02/verify_legendre_general.py`
-- (no Lean `decide` on `Nat.digits`, which is well-founded and does not reduce
-- reliably in the kernel).

#check @padicValNat_factorial_eq_div
#check @legendre_digit_sum_identity

end Erdos729Legendre
