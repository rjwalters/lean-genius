import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

/-!
# The parity of Euler's totient: `φ(n)` is even for `n > 2`, and the odd-totient
classification

**Open Question (`euler-totient-oq-06`)**: prove that Euler's totient `φ(n)` is
even for every `n > 2`.

Mathlib already supplies the one-directional fact `Nat.totient_even`
(`2 < n → Even n.totient`), proved through the unit `-1 ∈ (ZMod n)ˣ` having order
`2` and Lagrange's theorem `orderOf_dvd_card`.  Rather than restate that
one-liner, this file uses it as the seed for the **complete parity
classification**, which Mathlib does *not* package:

  `totient_odd_iff`:   `Odd (φ n)  ↔  n = 1 ∨ n = 2`,
  `totient_even_iff`:  `Even (φ n) ↔  n ≠ 1 ∧ n ≠ 2`.

So among all natural numbers, `φ` takes an odd value at **exactly** `1` and `2`
(`φ 1 = φ 2 = 1`); everywhere else — including `φ 0 = 0` — it is even.  The two
small odd values are the only obstruction to "totient is always even", and they
are pinned down precisely.

## Contents

* `totient_even_of_two_lt`  — the headline: `2 < n → Even (φ n)`.
* `two_dvd_totient_of_two_lt` — the divisibility restatement `2 < n → 2 ∣ φ n`.
* `le_two_of_odd_totient`   — the new contrapositive direction: an odd totient
  forces `n ≤ 2`.
* `totient_odd_iff`         — the full odd-totient classification.
* `totient_even_iff`        — its even complement.
* `even_totient_of_three_le` — convenience form `3 ≤ n → Even (φ n)`.

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace EulerTotientOQ06

open Nat

/-! ## The even direction (for `n > 2`) -/

/-- **Euler's totient is even for `n > 2`.**  This is `Nat.totient_even`; the
underlying reason is that `-1 ∈ (ZMod n)ˣ` has order `2` when `n > 2`, so `2`
divides `|(ZMod n)ˣ| = φ(n)` by Lagrange. -/
theorem totient_even_of_two_lt {n : ℕ} (hn : 2 < n) : Even (φ n) :=
  Nat.totient_even hn

/-- Divisibility restatement: `2 ∣ φ(n)` whenever `n > 2`. -/
theorem two_dvd_totient_of_two_lt {n : ℕ} (hn : 2 < n) : 2 ∣ φ n :=
  (totient_even_of_two_lt hn).two_dvd

/-- Convenience form with the `3 ≤ n` hypothesis. -/
theorem even_totient_of_three_le {n : ℕ} (hn : 3 ≤ n) : Even (φ n) :=
  totient_even_of_two_lt hn

/-! ## The odd-totient classification -/

/-- If `φ(n)` is odd then `n ≤ 2`.  This is the contrapositive of
`totient_even_of_two_lt` (an odd number is not even). -/
theorem le_two_of_odd_totient {n : ℕ} (h : Odd (φ n)) : n ≤ 2 := by
  by_contra hn
  push_neg at hn
  exact (Nat.not_odd_iff_even.2 (totient_even_of_two_lt hn)) h

/-- **Odd-totient classification.**  `φ(n)` is odd if and only if `n = 1` or
`n = 2`.  (`φ 1 = φ 2 = 1` are the only odd values; in particular `φ 0 = 0` is
even.) -/
theorem totient_odd_iff {n : ℕ} : Odd (φ n) ↔ n = 1 ∨ n = 2 := by
  constructor
  · intro h
    have hle := le_two_of_odd_totient h
    interval_cases n <;> revert h <;> decide
  · rintro (rfl | rfl) <;> decide

/-- **Even-totient classification.**  `φ(n)` is even if and only if `n ∉ {1, 2}`.
The complement of `totient_odd_iff`. -/
theorem totient_even_iff {n : ℕ} : Even (φ n) ↔ n ≠ 1 ∧ n ≠ 2 := by
  rw [← Nat.not_odd_iff_even, totient_odd_iff, not_or]

end EulerTotientOQ06
