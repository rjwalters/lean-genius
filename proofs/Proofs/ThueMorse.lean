import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The Thue-Morse Sequence

## What This Proves

The **Thue-Morse sequence** `t : ℕ → ZMod 2` assigns to each natural number the
parity of the number of `1`s in its binary expansion.  Equivalently it is the
unique sequence determined by

* `t 0 = 0`,
* `t (2n)   = t n`,
* `t (2n+1) = t n + 1`   (i.e. the bit is flipped).

We define `t` directly as the parity of the digit sum in base `2`
(`thueMorse n = ((Nat.digits 2 n).sum : ZMod 2)`) and prove that it satisfies
these defining recurrences.  From them we derive the value at powers of two and
the four-term **Prouhet-Tarry-Escott block identities**

* `t (4n)   = t (4n+3) = t n`,
* `t (4n+1) = t (4n+2) = t n + 1`,

which express the `0110 / 1001` block structure underlying Prouhet's equal-power
partition theorem.

## Historical Context

The sequence was studied by Eugène Prouhet (1851) in connection with partitioning
integers into classes with equal power sums, by Axel Thue (1906, 1912) as the
first explicit infinite cube-free / overlap-free word, and by Marston Morse (1921)
in symbolic dynamics.  Working in `ZMod 2` makes the "flip a bit" recurrence a
genuine algebraic identity (`t (2n+1) = t n + 1`).

## Status

Fully machine-checked: `0` sorries, `0` axioms.  The base-`2` digit expansion is
provided by Mathlib (`Nat.digits`), and all results are elementary consequences
of its recursion.
-/

namespace ThueMorse

open scoped BigOperators

/-- The Thue-Morse sequence: the parity of the number of `1`s in the binary
expansion of `n`, valued in `ZMod 2`.  Since the base-`2` digits are each `0`
or `1`, their sum counts the `1`s, and reducing mod `2` gives the Thue-Morse
value. -/
def thueMorse (n : ℕ) : ZMod 2 := ((Nat.digits 2 n).sum : ZMod 2)

@[simp] theorem thueMorse_zero : thueMorse 0 = 0 := by
  simp [thueMorse]

/-- Even argument: doubling prepends a `0` bit, leaving the digit sum unchanged. -/
theorem thueMorse_two_mul (n : ℕ) : thueMorse (2 * n) = thueMorse n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · unfold thueMorse
    rw [Nat.digits_def' (by norm_num) (by omega)]
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    rw [h1, h2]
    simp [List.sum_cons]

/-- Odd argument: `2n+1` prepends a `1` bit, flipping the Thue-Morse value. -/
theorem thueMorse_two_mul_add_one (n : ℕ) :
    thueMorse (2 * n + 1) = thueMorse n + 1 := by
  unfold thueMorse
  rw [Nat.digits_def' (by norm_num) (by omega)]
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  rw [h1, h2]
  push_cast [List.sum_cons]
  ring

@[simp] theorem thueMorse_one : thueMorse 1 = 1 := by
  have := thueMorse_two_mul_add_one 0
  simpa using this

/-- Consecutive even/odd pairs always differ: `t (2n+1) = t (2n) + 1`. -/
theorem thueMorse_two_mul_add_one_eq (n : ℕ) :
    thueMorse (2 * n + 1) = thueMorse (2 * n) + 1 := by
  rw [thueMorse_two_mul, thueMorse_two_mul_add_one]

theorem thueMorse_ne_succ_two_mul (n : ℕ) : thueMorse (2 * n) ≠ thueMorse (2 * n + 1) := by
  rw [thueMorse_two_mul_add_one_eq]
  intro h
  have h1 : thueMorse (2 * n) + 0 = thueMorse (2 * n) + 1 := by rw [add_zero]; exact h
  exact absurd (add_left_cancel h1) (by decide)

/-- Value at powers of two: `2^k` has a single `1` bit, so `t (2^k) = 1`. -/
theorem thueMorse_two_pow (k : ℕ) : thueMorse (2 ^ k) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [this, thueMorse_two_mul, ih]

/-! ### Prouhet-Tarry-Escott block identities

The four residues mod `4` split into two pairs with a common value, giving the
length-four blocks `t(4n) t(4n+1) t(4n+2) t(4n+3) = a (a+1) (a+1) a` where
`a = t n`.  This is the combinatorial heart of Prouhet's equal-power partition. -/

theorem thueMorse_four_mul (n : ℕ) : thueMorse (4 * n) = thueMorse n := by
  have h : (4 : ℕ) * n = 2 * (2 * n) := by ring
  rw [h, thueMorse_two_mul, thueMorse_two_mul]

theorem thueMorse_four_mul_add_one (n : ℕ) :
    thueMorse (4 * n + 1) = thueMorse n + 1 := by
  have h : (4 : ℕ) * n + 1 = 2 * (2 * n) + 1 := by ring
  rw [h, thueMorse_two_mul_add_one, thueMorse_two_mul]

theorem thueMorse_four_mul_add_two (n : ℕ) :
    thueMorse (4 * n + 2) = thueMorse n + 1 := by
  have h : (4 : ℕ) * n + 2 = 2 * (2 * n + 1) := by ring
  rw [h, thueMorse_two_mul, thueMorse_two_mul_add_one]

theorem thueMorse_four_mul_add_three (n : ℕ) :
    thueMorse (4 * n + 3) = thueMorse n := by
  have h : (4 : ℕ) * n + 3 = 2 * (2 * n + 1) + 1 := by ring
  rw [h, thueMorse_two_mul_add_one, thueMorse_two_mul_add_one, add_assoc,
    show (1 : ZMod 2) + 1 = 0 from by decide, add_zero]

/-- The outer pair of a length-four block agree: `t(4n) = t(4n+3)`. -/
theorem thueMorse_four_mul_eq_add_three (n : ℕ) :
    thueMorse (4 * n) = thueMorse (4 * n + 3) := by
  rw [thueMorse_four_mul, thueMorse_four_mul_add_three]

/-- The inner pair of a length-four block agree: `t(4n+1) = t(4n+2)`. -/
theorem thueMorse_four_mul_add_one_eq_add_two (n : ℕ) :
    thueMorse (4 * n + 1) = thueMorse (4 * n + 2) := by
  rw [thueMorse_four_mul_add_one, thueMorse_four_mul_add_two]

/-- Prouhet's equal-sum partition at level `k = 2`: splitting `{0,1,2,3}` by
Thue-Morse value gives `{0,3}` and `{1,2}`, and `0 + 3 = 1 + 2`. -/
theorem prouhet_level_two :
    thueMorse 0 = thueMorse 3 ∧ thueMorse 1 = thueMorse 2 ∧ (0 + 3 = 1 + 2) := by
  refine ⟨?_, ?_, by norm_num⟩
  · have := thueMorse_four_mul_eq_add_three 0; simpa using this
  · have := thueMorse_four_mul_add_one_eq_add_two 0; simpa using this

end ThueMorse
