/-
# The Bertrand Ballot Number via the Cycle Lemma

The **Bertrand ballot problem** asks: in an election where candidate `A` receives
`a` votes and candidate `B` receives `b` votes with `a > b`, what is the probability
that `A` is *strictly* ahead throughout the count?  The classical answer is
`(a − b)/(a + b)`.

The combinatorial engine behind this answer is the **Dvoretzky–Motzkin cycle lemma**
(already formalised, `0`-axiom, in `Proofs.BallotProblemOQ01`): for a fixed sequence
of `a` up-steps `(+1)` and `b` down-steps `(−1)` with `a > b`, exactly `a − b` of its
`a + b` cyclic rotations have all partial sums positive.  Aggregating this over all
`C(a+b, a)` arrangements — each strictly-positive sequence is hit by exactly `a + b`
of the `(sequence, rotation)` pairs, each other by none — yields the exact count of
strictly-positive sequences, the **ballot number**

  `BN(a, b) = (a − b)/(a + b) · C(a+b, a)`.

This file is the *arithmetic* companion to that combinatorial story.  We take the
manifestly-integral **reflection form** `C(a+b−1, a−1) − C(a+b−1, a)` as the
definition of `BN` and prove:

* `ballotNumber_mul_add` — the defining relation `BN(a,b) · (a+b) = (a−b) · C(a+b, a)`.
  This is exactly the aggregate the cycle lemma produces; in particular it shows the
  ratio `(a−b)/(a+b) · C(a+b, a)` is a genuine natural number.
* `ballotNumber_div` — the Bertrand ballot **probability** `(a − b)/(a + b)`,
  as the fraction `BN(a,b) / C(a+b, a)` over `ℚ`.
* `ballotNumber_catalan` — the **Catalan** specialisation `BN(n+1, n) = catalan n`
  (Dyck paths).

Everything is elementary binomial arithmetic: the two absorption identities
`k · C(n,k) = n · C(n−1, k−1)` (`Nat.add_one_mul_choose_eq`, `Nat.choose_succ_right_eq`),
plus the Catalan/central-binomial bridge from Mathlib.  No axioms, no `sorry`,
no `native_decide`.

## References
* Dvoretzky, A. and Motzkin, Th. (1947), *A problem of arrangements*.
* Renault, M. (2008), *Lost (and found) in translation: André's actual method*.
-/
import Mathlib

namespace BallotProblemOQ05

/-- The **ballot number** `BN(a, b)`, in reflection form.

By the cycle lemma this counts the sequences of `a` up-steps and `b` down-steps whose
every partial sum is strictly positive; equivalently `(a − b)/(a + b) · C(a+b, a)`.
The reflection form below is manifestly a natural number. -/
def ballotNumber (a b : ℕ) : ℕ :=
  (a + b - 1).choose (a - 1) - (a + b - 1).choose a

/-- Absorption "up": `(a+b)·C(a+b−1, a−1) = a·C(a+b, a)`, written with `a = A+1`. -/
theorem aux_up (A b : ℕ) :
    (A + 1 + b) * (A + b).choose A = (A + 1) * (A + 1 + b).choose (A + 1) := by
  have h := Nat.add_one_mul_choose_eq (A + b) A
  -- h : (A + b + 1) * (A + b).choose A = (A + b + 1).choose (A + 1) * (A + 1)
  have e : A + b + 1 = A + 1 + b := by ring
  rw [e] at h
  rw [h]; ring

/-- Absorption "down": `(a+b)·C(a+b−1, a) = b·C(a+b, a)`, written with `a = A+1`.
Derived from the "up" identity via `Nat.choose_succ_right_eq`, valid for every `b`
(including `b = 0`, where both sides vanish). -/
theorem aux_down (A b : ℕ) :
    (A + 1 + b) * (A + b).choose (A + 1) = b * (A + 1 + b).choose (A + 1) := by
  have hsub : A + b - A = b := by omega
  have hsucc : (A + b).choose (A + 1) * (A + 1) = (A + b).choose A * b := by
    have h := Nat.choose_succ_right_eq (A + b) A
    rw [hsub] at h
    exact h
  have key : (A + 1) * ((A + 1 + b) * (A + b).choose (A + 1))
           = (A + 1) * (b * (A + 1 + b).choose (A + 1)) := by
    calc (A + 1) * ((A + 1 + b) * (A + b).choose (A + 1))
        = (A + 1 + b) * ((A + b).choose (A + 1) * (A + 1)) := by ring
      _ = (A + 1 + b) * ((A + b).choose A * b) := by rw [hsucc]
      _ = b * ((A + 1 + b) * (A + b).choose A) := by ring
      _ = b * ((A + 1) * (A + 1 + b).choose (A + 1)) := by rw [aux_up A b]
      _ = (A + 1) * (b * (A + 1 + b).choose (A + 1)) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by omega) key

/-- Core identity in `A = a − 1` form:
`(C(A+b, A) − C(A+b, A+1)) · (A+1+b) = (A+1−b) · C(A+1+b, A+1)`.
Truncated `ℕ` subtraction makes this hold unconditionally. -/
theorem ballotNumber_mul_aux (A b : ℕ) :
    ((A + b).choose A - (A + b).choose (A + 1)) * (A + 1 + b)
      = (A + 1 - b) * (A + 1 + b).choose (A + 1) := by
  rw [Nat.sub_mul, Nat.sub_mul,
      mul_comm ((A + b).choose A) (A + 1 + b),
      mul_comm ((A + b).choose (A + 1)) (A + 1 + b),
      aux_up A b, aux_down A b]

/-- **The defining relation of the ballot number.**  For `a ≥ 1`,

  `BN(a, b) · (a + b) = (a − b) · C(a+b, a)`.

This is precisely the aggregate count produced by the cycle lemma: summed over all
`C(a+b, a)` arrangements of `a` up-steps and `b` down-steps, the number that stay
strictly positive is `(a − b)/(a + b) · C(a+b, a)`.  In particular the right-hand
side is divisible by `a + b`. -/
theorem ballotNumber_mul_add (a b : ℕ) (ha : 1 ≤ a) :
    ballotNumber a b * (a + b) = (a - b) * (a + b).choose a := by
  obtain ⟨A, rfl⟩ : ∃ A, a = A + 1 := ⟨a - 1, by omega⟩
  have e1 : A + 1 + b - 1 = A + b := by omega
  have e2 : A + 1 - 1 = A := by omega
  simp only [ballotNumber, e1, e2]
  exact ballotNumber_mul_aux A b

/-- **Bertrand ballot probability.**  For `1 ≤ a` and `b ≤ a`, the fraction of
`(a, b)`-arrangements that stay strictly positive is `(a − b)/(a + b)`:

  `BN(a, b) / C(a+b, a) = (a − b)/(a + b)`   (over `ℚ`). -/
theorem ballotNumber_div (a b : ℕ) (ha : 1 ≤ a) (hab : b ≤ a) :
    (ballotNumber a b : ℚ) / ((a + b).choose a : ℚ)
      = ((a : ℚ) - b) / ((a : ℚ) + b) := by
  have hmul := ballotNumber_mul_add a b ha
  have h2 : (ballotNumber a b : ℚ) * ((a : ℚ) + b)
          = ((a : ℚ) - b) * ((a + b).choose a : ℚ) := by
    have hc := congrArg (fun n : ℕ => (n : ℚ)) hmul
    push_cast [Nat.cast_sub hab] at hc
    linear_combination hc
  have hC : ((a + b).choose a : ℚ) ≠ 0 := by
    have : 0 < (a + b).choose a := Nat.choose_pos (Nat.le_add_right a b)
    exact_mod_cast this.ne'
  have hS : ((a : ℚ) + b) ≠ 0 := by
    have hpos : (0 : ℚ) < (a : ℚ) + b := by
      have : 0 < a + b := by omega
      exact_mod_cast this
    exact hpos.ne'
  rw [div_eq_div_iff hC hS]
  linear_combination h2

/-- **Catalan specialisation.**  The ballot number `BN(n+1, n)` counts Dyck paths of
semilength `n` and equals the `n`-th Catalan number. -/
theorem ballotNumber_catalan (n : ℕ) : ballotNumber (n + 1) n = catalan n := by
  have hBN : ballotNumber (n + 1) n = (2 * n).choose n - (2 * n).choose (n + 1) := by
    have e1 : n + 1 + n - 1 = 2 * n := by omega
    have e2 : n + 1 - 1 = n := by omega
    simp only [ballotNumber, e1, e2]
  -- (n+1) · catalan n = C(2n, n)
  have hcat : (n + 1) * catalan n = (2 * n).choose n := by
    rw [catalan_eq_centralBinom_div, Nat.mul_div_cancel' (Nat.succ_dvd_centralBinom n),
        Nat.centralBinom_eq_two_mul_choose]
  -- (n+1) · C(2n, n+1) = n · C(2n, n)
  have hstep : (n + 1) * (2 * n).choose (n + 1) = n * (2 * n).choose n := by
    have h := Nat.choose_succ_right_eq (2 * n) n
    have e : 2 * n - n = n := by omega
    rw [e] at h
    -- h : (2*n).choose (n+1) * (n+1) = (2*n).choose n * n
    rw [mul_comm ((2 * n).choose n) n] at h
    rw [mul_comm (n + 1) ((2 * n).choose (n + 1))]
    exact h
  -- (n+1) · BN(n+1, n) = C(2n, n)
  have hBNmul : (n + 1) * ballotNumber (n + 1) n = (2 * n).choose n := by
    rw [hBN, mul_comm, Nat.sub_mul,
        mul_comm ((2 * n).choose (n + 1)) (n + 1), hstep,
        mul_comm ((2 * n).choose n) (n + 1), add_one_mul]
    exact Nat.add_sub_cancel_left _ _
  have hcombine : (n + 1) * ballotNumber (n + 1) n = (n + 1) * catalan n := by
    rw [hBNmul, hcat]
  exact Nat.eq_of_mul_eq_mul_left (by omega) hcombine

/-! ### Worked examples (checked by `decide`, hence `0`-axiom) -/

/-- `a = 3, b = 1`: `(3−1)/(3+1)·C(4,3) = (1/2)·4 = 2`. -/
example : ballotNumber 3 1 = 2 := by decide

/-- `a = 4, b = 3`: `(4−3)/(4+3)·C(7,4) = (1/7)·35 = 5 = catalan 3`. -/
example : ballotNumber 4 3 = 5 := by decide

/-- Tie `a = b` gives `0` strictly-positive sequences. -/
example : ballotNumber 5 5 = 0 := by decide

/-- All up-steps `b = 0`: the unique sequence is strictly positive. -/
example : ballotNumber 4 0 = 1 := by decide

end BallotProblemOQ05
