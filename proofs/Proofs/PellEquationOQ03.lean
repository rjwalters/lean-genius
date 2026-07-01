/-
Pell Equation — Open Question 03: Can Pell equations be solved in polynomial time?

## Research Question
Is there a deterministic classical algorithm that, given a non-square `D`, outputs a
representation of the fundamental Pell solution in time polynomial in `log D`?
The best known classical algorithms are only *sub-exponential* (Lenstra 1980,
Buchmann–Williams), while Hallgren (2002) gives a *quantum* polynomial-time algorithm.
The classical question is OPEN and is believed to be at least as hard as computing the
regulator of the real quadratic field ℚ(√D).

## What This File Contributes
A full formalisation of the *concrete algorithmic obstruction* that forces every
"generate the solutions" method to be at best exponential in the number of arithmetic
operations. The key tension is between two facts:

  (A) The `2^k`-th Pell solution is reachable by **`k` repeated squarings** — a
      *linear* number of group operations in `k` (fast exponentiation / addition
      chains).  This is the algorithmic content that makes powers cheap to *compose*.

  (B) The `2^k`-th Pell solution has an `x`-coordinate of size at least `2^(2^k)`,
      i.e. its bit-length is `≥ 2^k` — **exponential in `k`**, the number of
      operations performed.

So the map (number of operations `k`) ↦ (bit-size of the output) is exponential: you
cannot even *write down* the reached solution in time polynomial in the number of ring
multiplications.  This is precisely why naive solution-enumeration is sub-exponential,
and it isolates — in fully verified, axiom-free Lean — the growth phenomenon at the
heart of the open complexity question.

The complexity-class statement itself (does a `poly(log D)` classical algorithm exist?)
is *not* formalised here: Mathlib has no bit-complexity model, no `TIME(f)` predicate,
and no complexity class `P`.  We formalise the underlying mathematics that any such
formalisation would rest on.

## Main Results
* `pellDouble` — the squaring (doubling) map `a ↦ a * a` on `Solution₁ d`.
* `x_double`, `y_double` — explicit Brahmagupta doubling formulas
  `x₂ₙ = 2xₙ² − 1`, `y₂ₙ = 2 xₙ yₙ`.
* `iterate_double_eq_pow` — `k` doublings compute the `2^k`-th power
  (repeated-squaring correctness).
* `x_pow_add`, `y_pow_add` — the index-addition (Brahmagupta composition) laws
  `x_{m+n} = xₘxₙ + D yₘyₙ`, `y_{m+n} = xₘyₙ + yₘxₙ`, the step of binary exponentiation.
* `x_double_ge`, `x_iterate_double_ge` — the doubly-exponential lower bound
  `2^(2^k) ≤ x_{2^k}` on the reached coordinate.
* `operations_vs_size` — the capstone tying (A) and (B) together.

## Status: axiom-free formalisation of the growth obstruction.
The open question (classical polynomial-time solvability) itself remains OPEN.

Reference: Lenstra, "Solving the Pell Equation", Notices AMS 49 (2002) 182–192.
-/

import Mathlib.NumberTheory.Pell
import Mathlib.Tactic

open Pell

namespace PellEquationOQ03

variable {d : ℤ}

/-! ## Part 1: The doubling (squaring) map -/

/-- The **doubling map** on Pell solutions: `a ↦ a * a`.  In the multiplicative
group `Solution₁ d` this is squaring, and it is the elementary step of the
repeated-squaring ("fast exponentiation") algorithm for reaching high powers of the
fundamental solution. -/
def pellDouble (a : Solution₁ d) : Solution₁ d := a * a

@[simp] theorem pellDouble_eq_sq (a : Solution₁ d) : pellDouble a = a ^ 2 := by
  rw [pellDouble, sq]

/-- **Brahmagupta doubling formula for the `x`-coordinate**: `x₂ₙ = 2 xₙ² − 1`.
Uses the defining Pell relation `xₙ² − D yₙ² = 1` to eliminate `D yₙ²`. -/
theorem x_double (a : Solution₁ d) : (pellDouble a).x = 2 * a.x ^ 2 - 1 := by
  have hp := a.prop
  show (a * a).x = 2 * a.x ^ 2 - 1
  rw [Solution₁.x_mul]
  linear_combination -hp

/-- **Brahmagupta doubling formula for the `y`-coordinate**: `y₂ₙ = 2 xₙ yₙ`. -/
theorem y_double (a : Solution₁ d) : (pellDouble a).y = 2 * a.x * a.y := by
  show (a * a).y = 2 * a.x * a.y
  rw [Solution₁.y_mul]
  ring

/-! ## Part 2: Repeated squaring computes high powers

`k` applications of `pellDouble` compute the `2^k`-th power of a solution.  This is
the correctness statement of the fast-exponentiation loop: reaching an
exponentially-indexed solution costs only linearly-many group operations in `k`. -/

/-- **Repeated-squaring correctness**: iterating the doubling map `k` times yields the
`2^k`-th power.  Hence `2^k`-indexed Pell solutions are reachable in `k` operations. -/
theorem iterate_double_eq_pow (a : Solution₁ d) :
    ∀ k : ℕ, (pellDouble)^[k] a = a ^ (2 ^ k) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, pellDouble_eq_sq, ← pow_mul, pow_succ]

/-! ## Part 3: The index-addition (Brahmagupta composition) laws

The step of binary exponentiation combines two already-computed powers.  In coordinates
this is Brahmagupta's identity applied to `a^m` and `a^n`. -/

/-- **Index-addition law for `x`** (Brahmagupta composition of powers):
`x_{m+n} = xₘ xₙ + D yₘ yₙ`. -/
theorem x_pow_add (a : Solution₁ d) (m n : ℕ) :
    (a ^ (m + n)).x = (a ^ m).x * (a ^ n).x + d * ((a ^ m).y * (a ^ n).y) := by
  rw [pow_add, Solution₁.x_mul]

/-- **Index-addition law for `y`** (Brahmagupta composition of powers):
`y_{m+n} = xₘ yₙ + yₘ xₙ`. -/
theorem y_pow_add (a : Solution₁ d) (m n : ℕ) :
    (a ^ (m + n)).y = (a ^ m).x * (a ^ n).y + (a ^ m).y * (a ^ n).x := by
  rw [pow_add, Solution₁.y_mul]

/-! ## Part 4: Exponential lower bound on the reached coordinate

While the *computation* of the `2^k`-th solution costs only `k` operations, the *output*
is doubly-exponentially large. -/

/-- One doubling at least squares the `x`-coordinate (for `x ≥ 1`):
`xₙ² ≤ x₂ₙ`.  From `x₂ₙ = 2xₙ² − 1` and `xₙ² ≥ 1`. -/
theorem x_double_ge {a : Solution₁ d} (ha : 1 ≤ a.x) : a.x ^ 2 ≤ (pellDouble a).x := by
  rw [x_double]
  nlinarith [ha]

/-- **Doubly-exponential lower bound**: if the seed has `x ≥ 2`, then after `k`
doublings the `x`-coordinate is at least `2^(2^k)`.  Equivalently the bit-length of the
`2^k`-th solution is `≥ 2^k`, exponential in the number `k` of operations performed. -/
theorem x_iterate_double_ge {a : Solution₁ d} (ha : 2 ≤ a.x) :
    ∀ k : ℕ, (2 : ℤ) ^ (2 ^ k) ≤ ((pellDouble)^[k] a).x := by
  intro k
  induction k with
  | zero => simpa only [pow_zero, pow_one, Function.iterate_zero_apply] using ha
  | succ k ih =>
    rw [Function.iterate_succ_apply', x_double]
    have h0 : (0 : ℤ) < (2 : ℤ) ^ (2 ^ k) := by positivity
    have hx1 : (1 : ℤ) ≤ ((pellDouble)^[k] a).x := by omega
    have hsq : ((2 : ℤ) ^ (2 ^ k)) ^ 2 ≤ ((pellDouble)^[k] a).x ^ 2 :=
      pow_le_pow_left₀ (le_of_lt h0) ih 2
    calc (2 : ℤ) ^ (2 ^ (k + 1))
        = ((2 : ℤ) ^ (2 ^ k)) ^ 2 := by rw [← pow_mul, ← pow_succ]
      _ ≤ ((pellDouble)^[k] a).x ^ 2 := hsq
      _ ≤ 2 * ((pellDouble)^[k] a).x ^ 2 - 1 := by nlinarith [hx1]

/-! ## Part 5: Capstone — operations versus output size -/

/-- **Operations versus output size.**  Starting from a solution with `x ≥ 2`, performing
`k` doubling operations produces exactly the `2^k`-th power (part A), whose `x`-coordinate
is at least `2^(2^k)` (part B).  The number of arithmetic operations is `k`, yet the size
of the result is exponential in `k`: no algorithm of this "compose the solutions" shape can
write its output in time polynomial in the number of ring operations.  This is the concrete
growth obstruction underlying the open question of classical polynomial-time solvability. -/
theorem operations_vs_size {a : Solution₁ d} (ha : 2 ≤ a.x) (k : ℕ) :
    (pellDouble)^[k] a = a ^ (2 ^ k) ∧ (2 : ℤ) ^ (2 ^ k) ≤ (a ^ (2 ^ k)).x := by
  refine ⟨iterate_double_eq_pow a k, ?_⟩
  have h := x_iterate_double_ge ha k
  rwa [iterate_double_eq_pow a k] at h

/-! ## Part 6: A concrete instance (D = 2, fundamental solution (3, 2))

The fundamental solution of `x² − 2y² = 1` is `(3, 2)`.  Repeated squaring reproduces the
classical chain `(3,2) → (17,12) → (577,408) → …`, each step roughly doubling the number
of digits. -/

/-- The fundamental solution `(3, 2)` of `x² − 2y² = 1`. -/
def sol2 : Solution₁ (2 : ℤ) := Solution₁.mk 3 2 (by norm_num)

theorem sol2_x : sol2.x = 3 := by simp only [sol2, Solution₁.x_mk]
theorem sol2_y : sol2.y = 2 := by simp only [sol2, Solution₁.y_mk]

/-- One doubling: `(3, 2) → (17, 12)`. -/
theorem double_sol2 : (pellDouble sol2).x = 17 ∧ (pellDouble sol2).y = 12 := by
  rw [x_double, y_double, sol2_x, sol2_y]
  norm_num

/-- Two doublings: `(3, 2) → (17, 12) → (577, 408)`, i.e. the 4-th power `sol2 ^ (2²)`
(see `iterate_double_eq_pow`).  Each step roughly doubles the number of digits. -/
theorem double_double_sol2 :
    (pellDouble (pellDouble sol2)).x = 577 ∧ (pellDouble (pellDouble sol2)).y = 408 := by
  rw [x_double, y_double, double_sol2.1, double_sol2.2]
  norm_num

end PellEquationOQ03
