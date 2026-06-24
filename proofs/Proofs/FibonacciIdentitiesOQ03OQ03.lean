import Mathlib

/-
# The symmetric even-doubling identity `F_{2n} = F_{n+1}² − F_{n−1}²` and its Lucas factorization

The parent entry `FibonacciIdentitiesOQ03` records the fast-doubling identities in the
form Mathlib stores them:

* `Nat.fib_two_mul_add_one` : `fib (2n+1) = fib (n+1)² + fib n²`   (odd → sum of two squares),
* an even **difference of squares** `fib (2n+2) = fib (n+2)² − fib n²`.

This entry supplies the *symmetric* reading of the even case, the form in which the
open question states it,

  `F_{2n} = F_{n+1}² − F_{n−1}²`,

and — the new content — recognises that as a **difference of two squares that factors**:

  `F_{n+1}² − F_{n−1}² = (F_{n+1} − F_{n−1})·(F_{n+1} + F_{n−1}) = F_n · L_n`,

where `L_n = F_{n−1} + F_{n+1}` is the `n`-th **Lucas number**.  This is the classical
Fibonacci–Lucas doubling identity

  `F_{2n} = F_n · L_n`.

Lucas numbers appear nowhere in the Fibonacci gallery and are not packaged in Mathlib's
`Nat.fib` API, so we introduce them here with the standard recurrence `L_0 = 2`, `L_1 = 1`,
`L_{n+2} = L_n + L_{n+1}`, prove the bridge `L_{n+1} = F_n + F_{n+2}` (equivalently
`L_m = F_{m−1} + F_{m+1}`) by two-step induction, and read off the factorisation.

Everything is elementary: the bridge is two-step induction on the shared recurrence, and
the doubling/factorisation identities combine Mathlib's `Nat.fib_two_mul_add_two` with the
Fibonacci recurrence `Nat.fib_add_two` and close by `ring`/`linarith`.  All `decide` checks
use kernel reduction (no `native_decide`), so the entry carries no axioms.
-/

namespace FibonacciIdentitiesOQ03OQ03

/-- **Lucas numbers** `L_n`: `L_0 = 2`, `L_1 = 1`, `L_{n+2} = L_n + L_{n+1}`.
The Lucas sequence shares the Fibonacci recurrence but starts `2, 1, 3, 4, 7, 11, …`. -/
def lucas : ℕ → ℕ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas n + lucas (n + 1)

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl

@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining Lucas recurrence `L_{n+2} = L_n + L_{n+1}`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-- **Lucas via Fibonacci.** `L_{n+1} = F_n + F_{n+2}`, i.e. `L_m = F_{m−1} + F_{m+1}`.
Proof by two-step induction: both sequences obey `x_{n+2} = x_n + x_{n+1}` and agree on the
two base indices, so the closed combination of Fibonacci values satisfies the Lucas
recurrence and matches the Lucas initial data. -/
theorem lucas_succ_eq_fib_add_fib (n : ℕ) :
    lucas (n + 1) = Nat.fib n + Nat.fib (n + 2) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h0 h1 =>
    -- `Nat.twoStepInduction` hands back `h1` with un-normalised indices
    -- (`lucas (n+1+1)`, `Nat.fib (n+1+2)`); restate it in canonical `n+2 / n+3`
    -- form so `omega` shares atoms with the recurrence facts below.
    have h1' : lucas (n + 2) = Nat.fib (n + 1) + Nat.fib (n + 3) := h1
    show lucas (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 4)
    have e2 : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
    have e3 : Nat.fib (n + 3) = Nat.fib (n + 1) + Nat.fib (n + 2) := Nat.fib_add_two
    have e4 : Nat.fib (n + 4) = Nat.fib (n + 2) + Nat.fib (n + 3) := Nat.fib_add_two
    have el : lucas (n + 3) = lucas (n + 1) + lucas (n + 2) := lucas_add_two (n + 1)
    omega

/-- **Odd-index Fibonacci numbers are sums of two consecutive squares.**
`fib (2n+1) = fib (n+1)² + fib n²` — Mathlib's `Nat.fib_two_mul_add_one`, recorded here as
the odd half of the sum / difference-of-squares pair named in the open question. -/
theorem fib_odd_sq_add_sq (n : ℕ) :
    Nat.fib (2 * n + 1) = Nat.fib (n + 1) ^ 2 + Nat.fib n ^ 2 :=
  Nat.fib_two_mul_add_one n

/-- **Fibonacci–Lucas doubling (shifted form).** `fib (2n+2) = fib (n+1) · L_{n+1}`.
The Mathlib even-doubling lemma is the product `fib (n+1)·(2·fib n + fib (n+1))`; the second
factor is exactly `fib n + fib (n+2) = L_{n+1}`, exhibiting the Lucas factor. -/
theorem fib_two_mul_add_two_eq_fib_mul_lucas (n : ℕ) :
    Nat.fib (2 * n + 2) = Nat.fib (n + 1) * lucas (n + 1) := by
  rw [Nat.fib_two_mul_add_two, lucas_succ_eq_fib_add_fib, Nat.fib_add_two]
  ring

/-- **Fibonacci–Lucas doubling identity** `F_{2n} = F_n · L_n` (for `n ≥ 1`).
This is the headline classical identity; reindexing `m = n+1` turns the shifted form above
into the symmetric `fib (2m) = fib m · L_m`. -/
theorem fib_two_mul_eq_fib_mul_lucas {m : ℕ} (hm : 1 ≤ m) :
    Nat.fib (2 * m) = Nat.fib m * lucas m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e : 2 * (n + 1) = 2 * n + 2 := by ring
  rw [e]
  exact fib_two_mul_add_two_eq_fib_mul_lucas n

/-- **Difference of squares factors as the Lucas product** (over `ℤ`).
`fib (n+2)² − fib n² = fib (n+1) · L_{n+1}`.  This is the bridge between the even-index
"difference of two squares" reading and the `F_n·L_n` product reading of `F_{2n}`. -/
theorem fib_sq_sub_sq_eq_fib_mul_lucas (n : ℕ) :
    (Nat.fib (n + 2) : ℤ) ^ 2 - (Nat.fib n : ℤ) ^ 2
      = (Nat.fib (n + 1) : ℤ) * (lucas (n + 1) : ℤ) := by
  have hprod : (Nat.fib (2 * n + 2) : ℤ) = (Nat.fib (n + 1) : ℤ) * (lucas (n + 1) : ℤ) := by
    exact_mod_cast fib_two_mul_add_two_eq_fib_mul_lucas n
  have hdiff : Nat.fib (2 * n + 2) + Nat.fib n ^ 2 = Nat.fib (n + 2) ^ 2 := by
    rw [Nat.fib_two_mul_add_two, Nat.fib_add_two]; ring
  have hdiffZ : (Nat.fib (2 * n + 2) : ℤ) + (Nat.fib n : ℤ) ^ 2 = (Nat.fib (n + 2) : ℤ) ^ 2 := by
    exact_mod_cast hdiff
  linarith

/-- **The symmetric even-doubling identity** `F_{2n} = F_{n+1}² − F_{n−1}²` (over `ℤ`, `n ≥ 1`),
the exact form named in the open question.  Combined with `fib_sq_sub_sq_eq_fib_mul_lucas`
this difference of squares equals the Lucas product `F_n · L_n`. -/
theorem fib_two_mul_symmetric_diff_sq {m : ℕ} (hm : 1 ≤ m) :
    (Nat.fib (2 * m) : ℤ) = (Nat.fib (m + 1) : ℤ) ^ 2 - (Nat.fib (m - 1) : ℤ) ^ 2 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have e : 2 * (n + 1) = 2 * n + 2 := by ring
  simp only [Nat.add_sub_cancel]
  rw [e]
  show (Nat.fib (2 * n + 2) : ℤ) = (Nat.fib (n + 2) : ℤ) ^ 2 - (Nat.fib n : ℤ) ^ 2
  have hdiff : Nat.fib (2 * n + 2) + Nat.fib n ^ 2 = Nat.fib (n + 2) ^ 2 := by
    rw [Nat.fib_two_mul_add_two, Nat.fib_add_two]; ring
  have hdiffZ : (Nat.fib (2 * n + 2) : ℤ) + (Nat.fib n : ℤ) ^ 2 = (Nat.fib (n + 2) : ℤ) ^ 2 := by
    exact_mod_cast hdiff
  linarith

/-- **Existential reading.** Every even-index Fibonacci number `fib (2m)` (`m ≥ 1`) is a
product of a Fibonacci number and a Lucas number. -/
theorem fib_two_mul_isFibLucasProduct {m : ℕ} (hm : 1 ≤ m) :
    ∃ a b : ℕ, Nat.fib (2 * m) = a * b ∧ a = Nat.fib m ∧ b = lucas m :=
  ⟨Nat.fib m, lucas m, fib_two_mul_eq_fib_mul_lucas hm, rfl, rfl⟩

/-- Numerical checks (kernel `decide`, no `native_decide`).
Lucas values `L_0..L_6 = 2,1,3,4,7,11,18`; `F_{10} = 55 = F_5 · L_5 = 5 · 11`. -/
example : lucas 5 = 11 := by decide

example : Nat.fib (2 * 5) = Nat.fib 5 * lucas 5 := by decide

example : Nat.fib (2 * 6) = Nat.fib 6 * lucas 6 := by decide   -- F_12 = 144 = 8 · 18

end FibonacciIdentitiesOQ03OQ03
