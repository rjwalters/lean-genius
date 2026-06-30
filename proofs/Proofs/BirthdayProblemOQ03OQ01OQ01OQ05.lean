/-
Birthday problem — closed form for the k=3 count at n = 4 (OQ-03-OQ-01-OQ-01-OQ-05)

Parent entry `birthday-problem-oq-03-oq-01-oq-01` introduces the slot recurrence

  R 0 e s         = 1
  R (n+1) e s     = e · R n (e-1) (s+1) + s · R n e (s-1)

and `birthdayCount3 n d = R n d 0`, the number of ways to seat `n` labelled people on
`d` days with **at most two per day** (the configurations relevant to a 3-way birthday
coincidence).  It proves the closed forms
`birthdayCount3 1 d = d`, `= d²` for `n = 2`, and `= d³ − d` for `n = 3`.

This file proves the **next** closed form, for `n = 4`:

  birthdayCount3 4 d = d⁴ − 4 d² + 3 d   (equivalently  d(d−1)(d²+d−3)).

It is stated over `ℤ` to avoid truncated-subtraction artefacts, and proved directly by
unfolding the recurrence (no `native_decide`, hence `0` axioms — unlike several of the
parent's tabulated threshold values).

The recurrence definition is reproduced here so the file is self-contained and fast to
compile (the parent file is `import Mathlib` plus several expensive `native_decide`
evaluations).

Main results:
* `birthdayCount3_four` — the closed form `d⁴ − 4 d² + 3 d` over `ℤ`.
* `birthdayCount3_four_factored` — the factored form `d(d−1)(d²+d−3)` over `ℤ`.
* `birthdayCount3_four_eq_nat` — a clean `ℕ` identity for `d ≥ 1`.
-/

import Mathlib

namespace BirthdayN4Closed

/-- Slot recurrence for the k=3 birthday count (state `(e, s)` = empty / single days). -/
def R : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | n + 1, e, s => e * R n (e - 1) (s + 1) + s * R n e (s - 1)

/-- Number of ways to seat `n` labelled people on `d` days with at most two per day. -/
def birthdayCount3 (n d : ℕ) : ℕ := R n d 0

@[simp] theorem R_zero (e s : ℕ) : R 0 e s = 1 := rfl

@[simp] theorem R_succ (n e s : ℕ) :
    R (n + 1) e s = e * R n (e - 1) (s + 1) + s * R n e (s - 1) := rfl

theorem R_one (e s : ℕ) : R 1 e s = e + s := by simp

/-- **Closed form for `n = 4`.** The number of ways to seat four labelled people on
`d` days with at most two per day is `d⁴ − 4 d² + 3 d`. -/
theorem birthdayCount3_four (d : ℕ) :
    (birthdayCount3 4 d : ℤ) = d ^ 4 - 4 * d ^ 2 + 3 * d := by
  rcases d with _ | _ | _ | e
  · decide
  · decide
  · decide
  · simp only [birthdayCount3, R_succ, R_one, R_zero, Nat.succ_sub_one,
      Nat.zero_sub, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add]
    push_cast
    ring

/-- **Factored closed form for `n = 4`:** `d(d−1)(d²+d−3)`. -/
theorem birthdayCount3_four_factored (d : ℕ) :
    (birthdayCount3 4 d : ℤ) = d * (d - 1) * (d ^ 2 + d - 3) := by
  rw [birthdayCount3_four]; ring

/-- The closed form as a natural-number identity (valid for `d ≥ 1`, so that the
subtraction `d⁴ + 3d − 4d²` does not truncate). -/
theorem birthdayCount3_four_eq_nat (d : ℕ) (hd : 1 ≤ d) :
    birthdayCount3 4 d + 4 * d ^ 2 = d ^ 4 + 3 * d := by
  have h := birthdayCount3_four d
  zify
  linarith [h]

end BirthdayN4Closed
