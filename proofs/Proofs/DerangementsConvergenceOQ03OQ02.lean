/-
  Derangements: the alternating one-term recurrence
  Open Question: derangements-convergence-oq-03-oq-02

  ## Main result (requested form)

  `numDerangements_succ_alt` :
    (numDerangements (n + 1) : ℤ) = (n + 1) * numDerangements n + (-1) ^ (n + 1)

  This is the `+(-1)^(n+1)` sign-convention form of Mathlib's
  `numDerangements_succ`, which states the same recurrence as
  `(n + 1) * numDerangements n - (-1) ^ n`.  The two are equivalent because
  `(-1)^(n+1) = -(-1)^n`, so the recurrence itself is a one-line restatement of
  the Mathlib lemma in the convention used by the open-question statement.

  ## What is genuinely new here

  Beyond presenting the recurrence in the requested convention, we record two
  consequences that Mathlib does not carry and that follow immediately from the
  one-term form:

  * `numDerangements_sub_eq` :
      (numDerangements (n + 1) : ℤ) - (n + 1) * numDerangements n = (-1) ^ (n + 1)
    The exact one-term "error" between D(n+1) and (n+1)·D(n) is always ±1; in
    particular |D(n+1) - (n+1)·D(n)| = 1.

  * `numDerangements_modEq` :
      (numDerangements (n + 1) : ℤ) ≡ (-1) ^ (n + 1) [ZMOD (n + 1)]
    Reducing the recurrence modulo (n+1) kills the (n+1)·D(n) term, so the
    derangement count is congruent to ±1 modulo its order: D(m) ≡ (-1)^m (mod m)
    for every m ≥ 1.

  All results are fully machine-checked with no `sorry` and no extra axioms
  (only Lean/Mathlib's foundational `propext`/`Classical.choice`/`Quot.sound`).
-/

import Mathlib

namespace DerangementsConvergenceOQ03OQ02

/-- **Alternating one-term derangement recurrence** in the `+(-1)^(n+1)`
convention requested by the open question:
`D(n+1) = (n+1)·D(n) + (-1)^(n+1)`.

Equivalent to Mathlib's `numDerangements_succ` (which uses `-(-1)^n`). -/
theorem numDerangements_succ_alt (n : ℕ) :
    (numDerangements (n + 1) : ℤ)
      = (n + 1) * (numDerangements n : ℤ) + (-1) ^ (n + 1) := by
  rw [numDerangements_succ, pow_succ]
  ring

/-- The exact one-term error: `D(n+1) - (n+1)·D(n) = (-1)^(n+1)`.
In particular `|D(n+1) - (n+1)·D(n)| = 1`. -/
theorem numDerangements_sub_eq (n : ℕ) :
    (numDerangements (n + 1) : ℤ) - (n + 1) * (numDerangements n : ℤ)
      = (-1) ^ (n + 1) := by
  rw [numDerangements_succ_alt]; ring

/-- `|D(n+1) - (n+1)·D(n)| = 1`: the one-term remainder always has size one. -/
theorem numDerangements_abs_sub (n : ℕ) :
    |(numDerangements (n + 1) : ℤ) - (n + 1) * (numDerangements n : ℤ)| = 1 := by
  rw [numDerangements_sub_eq, abs_pow, abs_neg, abs_one, one_pow]

/-- **Modular consequence.** Reducing the recurrence modulo `n+1` annihilates the
`(n+1)·D(n)` term, leaving `D(n+1) ≡ (-1)^(n+1) (mod n+1)`.

Equivalently, for every `m ≥ 1`, `D(m) ≡ (-1)^m (mod m)`: the number of
derangements is congruent to `±1` modulo its order. -/
theorem numDerangements_modEq (n : ℕ) :
    (numDerangements (n + 1) : ℤ) ≡ (-1) ^ (n + 1) [ZMOD ((n : ℤ) + 1)] := by
  rw [numDerangements_succ_alt]
  have hdvd : ((n : ℤ) + 1) ∣ ((n : ℤ) + 1) * (numDerangements n : ℤ) :=
    Dvd.intro _ rfl
  have h := Int.ModEq.add_right ((-1 : ℤ) ^ (n + 1))
    ((Int.modEq_zero_iff_dvd).mpr hdvd)
  rwa [zero_add] at h

/-- Sanity check on the small values: `D(4) = 9`, consistent with
`9 = 4·2 + (-1)^4 = 8 + 1`. -/
example : numDerangements 4 = 9 := by decide

end DerangementsConvergenceOQ03OQ02
