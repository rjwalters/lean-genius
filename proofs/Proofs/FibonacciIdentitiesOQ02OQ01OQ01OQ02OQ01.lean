import Proofs.FibonacciIdentitiesOQ02OQ01OQ01
import Mathlib.Tactic

/-
# The Degree-2 Identities for a General Lucas Sequence

## Open Question OQ-02-OQ-01-OQ-01-OQ-02-OQ-01

The parent (OQ-02-OQ-01-OQ-01-OQ-02) proved the three degree-2 relations between
the Fibonacci numbers `Fₙ` and the Lucas numbers `Lₙ`:

  Lₙ² − 5·Fₙ² = 4·(−1)ⁿ        (difference of squares)
  Lₙ² + 5·Fₙ² = 2·L₂ₙ          (sum of squares)
  Lₙ · Fₙ     =   F₂ₙ          (cross / doubling)

Its first open question asks to **generalize this trio to an arbitrary Lucas
sequence** `(P, Q)` with companion sequences `Uₙ`, `Vₙ` and discriminant
`D = P² − 4Q`, proving uniformly

  Vₙ² − D·Uₙ² = 4·Qⁿ           (difference of squares)        (Ⅰ)
  Vₙ² + D·Uₙ² = 2·V₂ₙ          (sum of squares)               (Ⅱ)
  Vₙ · Uₙ     =   U₂ₙ          (cross / doubling)             (Ⅲ)

and recovering the Fibonacci–Lucas identities at `P = 1`, `Q = −1`, `D = 5`.

## The Lucas sequences

For parameters `P Q : ℤ` the *Lucas sequences of the first and second kind* are

  U₀ = 0,  U₁ = 1,  Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ
  V₀ = 2,  V₁ = P,  Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ

At `(P, Q) = (1, −1)` these are exactly the Fibonacci numbers `Uₙ = Fₙ` and the
Lucas numbers `Vₙ = Lₙ`.

## Proof architecture

The whole degree-2 algebra rests on three inductive facts and two addition laws:

* `lucas_V_eq` — the linear bridge `Vₙ = 2·Uₙ₊₁ − P·Uₙ` (two-step induction),
  the single relation that ties the second-kind sequence to the first-kind one.
* `lucas_U_invariant` — `Uₙ₊₁² − P·Uₙ₊₁·Uₙ + Q·Uₙ² = Qⁿ`, a one-step induction.
  Combined with the bridge it instantly gives the **difference of squares (Ⅰ)**.
* `lucas_addU` / `lucas_addV` — the addition laws
  `2·Uₘ₊ₙ = Uₘ·Vₙ + Vₘ·Uₙ` and `2·Vₘ₊ₙ = Vₘ·Vₙ + D·Uₘ·Uₙ`
  (two-step induction in `n`, base cases supplied by the bridge).
  Setting `m = n` yields the **sum of squares (Ⅱ)** and the **cross identity (Ⅲ)**
  (the latter cancelling the factor 2 over `ℤ`).

The point of the generalization: (Ⅰ) needs only `lucas_U_invariant`, a *single*
clean one-step induction, while (Ⅱ) and (Ⅲ) are the diagonal `m = n`
specializations of the addition laws — the same Mathlib-free machinery the
Fibonacci proof used, now stated once at the level of an arbitrary `(P, Q)`.

## Axioms: 0 | Sorries: 0
-/

namespace FibonacciIdentitiesOQ02OQ01OQ01OQ02OQ01

/-- The pair `(Uₙ, Uₙ₊₁)` for the first-kind Lucas sequence with parameters `P, Q`. -/
def Upair (P Q : ℤ) : ℕ → ℤ × ℤ
  | 0 => (0, 1)
  | n + 1 => ((Upair P Q n).2, P * (Upair P Q n).2 - Q * (Upair P Q n).1)

/-- The first-kind Lucas sequence: `U₀ = 0`, `U₁ = 1`, `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`. -/
def U (P Q : ℤ) (n : ℕ) : ℤ := (Upair P Q n).1

/-- The pair `(Vₙ, Vₙ₊₁)` for the second-kind Lucas sequence with parameters `P, Q`. -/
def Vpair (P Q : ℤ) : ℕ → ℤ × ℤ
  | 0 => (2, P)
  | n + 1 => ((Vpair P Q n).2, P * (Vpair P Q n).2 - Q * (Vpair P Q n).1)

/-- The second-kind Lucas sequence: `V₀ = 2`, `V₁ = P`, `Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ`. -/
def V (P Q : ℤ) (n : ℕ) : ℤ := (Vpair P Q n).1

variable (P Q : ℤ)

@[simp] theorem U_zero : U P Q 0 = 0 := rfl
@[simp] theorem U_one : U P Q 1 = 1 := rfl
@[simp] theorem V_zero : V P Q 0 = 2 := rfl
@[simp] theorem V_one : V P Q 1 = P := rfl

/-- Defining recurrence for `U`: `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`. -/
theorem U_rec (n : ℕ) : U P Q (n + 2) = P * U P Q (n + 1) - Q * U P Q n := rfl

/-- Defining recurrence for `V`: `Vₙ₊₂ = P·Vₙ₊₁ − Q·Vₙ`. -/
theorem V_rec (n : ℕ) : V P Q (n + 2) = P * V P Q (n + 1) - Q * V P Q n := rfl

/-- **The linear bridge** `Vₙ = 2·Uₙ₊₁ − P·Uₙ`, the single relation linking the two
    kinds of Lucas sequence.  Proved by two-step induction. -/
theorem lucas_V_eq (n : ℕ) : V P Q n = 2 * U P Q (n + 1) - P * U P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
      have h2 : U P Q (1 + 1) = P * U P Q 1 - Q * U P Q 0 := rfl
      simp only [V_one, U_one, U_zero, h2]; ring
  | more n ih1 ih2 =>
      have e2 : U P Q (n + 1 + 1) = U P Q (n + 2) := rfl
      rw [e2] at ih2
      show V P Q (n + 2) = 2 * U P Q (n + 3) - P * U P Q (n + 2)
      have r2V : V P Q (n + 2) = P * V P Q (n + 1) - Q * V P Q n := rfl
      have r3U : U P Q (n + 3) = P * U P Q (n + 2) - Q * U P Q (n + 1) := rfl
      have r2U : U P Q (n + 2) = P * U P Q (n + 1) - Q * U P Q n := rfl
      rw [r2V, ih1, ih2, r3U, r2U]; ring

/-- **The fundamental `U`-invariant** `Uₙ₊₁² − P·Uₙ₊₁·Uₙ + Q·Uₙ² = Qⁿ`.  A clean
    one-step induction: the substitution `Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ` multiplies the
    quadratic form by exactly `Q`. -/
theorem lucas_U_invariant (n : ℕ) :
    U P Q (n + 1) ^ 2 - P * U P Q (n + 1) * U P Q n + Q * U P Q n ^ 2 = Q ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have r : U P Q (k + 1 + 1) = P * U P Q (k + 1) - Q * U P Q k := rfl
      rw [r, pow_succ]
      linear_combination Q * ih

/-- **Difference of squares (Ⅰ)** `Vₙ² − D·Uₙ² = 4·Qⁿ`, where `D = P² − 4Q`.
    Immediate from the bridge and the `U`-invariant: substituting
    `Vₙ = 2·Uₙ₊₁ − P·Uₙ` turns the left side into `4·(Uₙ₊₁² − P·Uₙ₊₁·Uₙ + Q·Uₙ²)`. -/
theorem lucas_sq_sub (n : ℕ) :
    V P Q n ^ 2 - (P ^ 2 - 4 * Q) * U P Q n ^ 2 = 4 * Q ^ n := by
  have hb := lucas_V_eq P Q n
  have hi := lucas_U_invariant P Q n
  rw [hb]; linear_combination 4 * hi

/-- **First addition law** `2·Uₘ₊ₙ = Uₘ·Vₙ + Vₘ·Uₙ`, by two-step induction on `n`.
    The base cases `n = 0, 1` are the bridge `lucas_V_eq` read off at `m`. -/
theorem lucas_addU (m n : ℕ) :
    2 * U P Q (m + n) = U P Q m * V P Q n + V P Q m * U P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [V_zero, U_zero, mul_zero, add_zero]; ring
  | one =>
      have hb := lucas_V_eq P Q m
      simp only [V_one, U_one, mul_one]
      linear_combination -hb
  | more n ih1 ih2 =>
      have a1 : m + (n + 1) = (m + n) + 1 := by omega
      have a2 : m + (n + 2) = (m + n) + 2 := by omega
      rw [a1] at ih2
      rw [a2]
      have rU : U P Q ((m + n) + 2) = P * U P Q ((m + n) + 1) - Q * U P Q (m + n) := rfl
      have rVn : V P Q (n + 2) = P * V P Q (n + 1) - Q * V P Q n := rfl
      have rUn : U P Q (n + 2) = P * U P Q (n + 1) - Q * U P Q n := rfl
      rw [rU, rVn, rUn]
      linear_combination P * ih2 - Q * ih1

/-- **Second addition law** `2·Vₘ₊ₙ = Vₘ·Vₙ + D·Uₘ·Uₙ` with `D = P² − 4Q`,
    by two-step induction on `n`. -/
theorem lucas_addV (m n : ℕ) :
    2 * V P Q (m + n) = V P Q m * V P Q n + (P ^ 2 - 4 * Q) * U P Q m * U P Q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp only [V_zero, U_zero, mul_zero, add_zero]; ring
  | one =>
      have hb1 := lucas_V_eq P Q m
      have hb2 := lucas_V_eq P Q (m + 1)
      have hu : U P Q (m + 1 + 1) = P * U P Q (m + 1) - Q * U P Q m := rfl
      simp only [V_one, U_one, mul_one]
      rw [hb2, hu, hb1]; ring
  | more n ih1 ih2 =>
      have a1 : m + (n + 1) = (m + n) + 1 := by omega
      have a2 : m + (n + 2) = (m + n) + 2 := by omega
      rw [a1] at ih2
      rw [a2]
      have rV : V P Q ((m + n) + 2) = P * V P Q ((m + n) + 1) - Q * V P Q (m + n) := rfl
      have rVn : V P Q (n + 2) = P * V P Q (n + 1) - Q * V P Q n := rfl
      have rUn : U P Q (n + 2) = P * U P Q (n + 1) - Q * U P Q n := rfl
      rw [rV, rVn, rUn]
      linear_combination P * ih2 - Q * ih1

/-- **Sum of squares (Ⅱ)** `Vₙ² + D·Uₙ² = 2·V₂ₙ`, the diagonal `m = n` case of the
    second addition law. -/
theorem lucas_sq_add (n : ℕ) :
    V P Q n ^ 2 + (P ^ 2 - 4 * Q) * U P Q n ^ 2 = 2 * V P Q (2 * n) := by
  have h := lucas_addV P Q n n
  rw [show (2 * n) = n + n from two_mul n]
  linear_combination -h

/-- **Cross identity (Ⅲ)** `Vₙ·Uₙ = U₂ₙ`, the diagonal `m = n` case of the first
    addition law; the factor 2 cancels over `ℤ`. -/
theorem lucas_mul (n : ℕ) :
    V P Q n * U P Q n = U P Q (2 * n) := by
  have h := lucas_addU P Q n n
  rw [show (2 * n) = n + n from two_mul n]
  have h2 : 2 * U P Q (n + n) = 2 * (V P Q n * U P Q n) := by linear_combination h
  exact (mul_left_cancel₀ two_ne_zero h2).symm

/-! ## Recovery: the Fibonacci–Lucas identities at `(P, Q) = (1, −1)`, `D = 5` -/

open FibonacciIdentitiesOQ02OQ01OQ01 in
/-- At `(P, Q) = (1, −1)` the first-kind Lucas sequence is the Fibonacci sequence. -/
theorem U_eq_fib (n : ℕ) : U 1 (-1) n = (Nat.fib n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
      have r : U 1 (-1) (n + 2) = 1 * U 1 (-1) (n + 1) - (-1) * U 1 (-1) n := rfl
      rw [r, ih1, ih2]
      have hf : Nat.fib (n + 2) = Nat.fib n + Nat.fib (n + 1) := Nat.fib_add_two
      rw [hf]; push_cast; ring

open FibonacciIdentitiesOQ02OQ01OQ01 in
/-- At `(P, Q) = (1, −1)` the second-kind Lucas sequence is the Lucas sequence. -/
theorem V_eq_lucas (n : ℕ) : V 1 (-1) n = (lucas n : ℤ) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
      have r : V 1 (-1) (n + 2) = 1 * V 1 (-1) (n + 1) - (-1) * V 1 (-1) n := rfl
      rw [r, ih1, ih2]
      have hl : lucas (n + 2) = lucas n + lucas (n + 1) := lucas_add_two n
      rw [hl]; push_cast; ring

open FibonacciIdentitiesOQ02OQ01OQ01 in
/-- Recovered difference of squares: `Lₙ² − 5·Fₙ² = 4·(−1)ⁿ`. -/
theorem fib_lucas_sq_sub (n : ℕ) :
    (lucas n : ℤ) ^ 2 - 5 * (Nat.fib n : ℤ) ^ 2 = 4 * (-1) ^ n := by
  have h := lucas_sq_sub 1 (-1) n
  rw [U_eq_fib, V_eq_lucas] at h
  linear_combination h

open FibonacciIdentitiesOQ02OQ01OQ01 in
/-- Recovered sum of squares: `Lₙ² + 5·Fₙ² = 2·L₂ₙ`. -/
theorem fib_lucas_sq_add (n : ℕ) :
    (lucas n : ℤ) ^ 2 + 5 * (Nat.fib n : ℤ) ^ 2 = 2 * (lucas (2 * n) : ℤ) := by
  have h := lucas_sq_add 1 (-1) n
  simp only [U_eq_fib, V_eq_lucas] at h
  linear_combination h

open FibonacciIdentitiesOQ02OQ01OQ01 in
/-- Recovered cross identity: `Lₙ · Fₙ = F₂ₙ`. -/
theorem fib_lucas_mul (n : ℕ) :
    (lucas n : ℤ) * (Nat.fib n : ℤ) = (Nat.fib (2 * n) : ℤ) := by
  have h := lucas_mul 1 (-1) n
  simp only [U_eq_fib, V_eq_lucas] at h
  linear_combination h

/-! ## Numeric sanity checks -/

-- Difference of squares for the Pell-Lucas sequence `(P, Q) = (2, -1)` at `n = 4`:
-- `U : 0,1,2,5,12`, `V : 2,2,6,14,34`; `D = 4 + 4 = 8`; `34² − 8·12² = 1156 − 1152 = 4 = 4·(−1)⁴`.
example : V 2 (-1) 4 ^ 2 - ((2 : ℤ) ^ 2 - 4 * (-1)) * U 2 (-1) 4 ^ 2 = 4 * (-1 : ℤ) ^ 4 :=
  lucas_sq_sub 2 (-1) 4

-- Cross identity for `(P, Q) = (3, 2)` (so `Uₙ = 2ⁿ − 1`) at `n = 3`:
-- `U₃ = 7`, `V₃ = 9`, `U₆ = 63 = 7·9`.
example : V 3 2 3 * U 3 2 3 = U 3 2 6 := lucas_mul 3 2 3

end FibonacciIdentitiesOQ02OQ01OQ01OQ02OQ01
