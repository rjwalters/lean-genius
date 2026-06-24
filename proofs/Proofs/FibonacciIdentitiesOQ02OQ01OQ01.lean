import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# The Fibonacci–Lucas Quadratic Identity `Lₙ² − 5Fₙ² = 4(−1)ⁿ`

## What This Proves

The parent entry (`fibonacci-identities-oq-02-oq-01`) settled the *divisibility*
question for the Lucas numbers `Lₙ` (`L₀ = 2, L₁ = 1, Lₙ₊₂ = Lₙ + Lₙ₊₁`):
the Lucas numbers are **not** a strong divisibility sequence, and its positive
engine was the **product identity** `F_{2n} = Fₙ · Lₙ`.

This entry supplies the *second* fundamental Fibonacci–Lucas identity — the one
that complements the product identity — as a **universally quantified theorem**
(not merely on instances):

    Lₙ² − 5·Fₙ² = 4·(−1)ⁿ                        (`lucas_sq_sub_five_fib_sq`)

over `ℤ`. Two structural consequences follow:

* **`Lₙ² = 5·Fₙ² ± 4`.** The Lucas number `Lₙ` is, up to the fixed defect `±4`,
  exactly `√5·Fₙ`. This is the integer shadow of Binet's formulas
  `Fₙ = (φⁿ − ψⁿ)/√5`, `Lₙ = φⁿ + ψⁿ`, with `φψ = −1`.

* **`gcd(Fₙ, Lₙ) ∣ 2`** (`gcd_fib_lucas_dvd_two`): the Fibonacci and Lucas
  numbers of the *same* index are coprime up to a factor of `2`. So
  `gcd(Fₙ, Lₙ) ∈ {1, 2}` always — the companion sequences barely interact
  multiplicatively at a fixed index, in sharp contrast to the product identity
  `Fₙ ∣ F_{2n}` and `Lₙ ∣ F_{2n}` linking index `n` to index `2n`.

## How It's Proved

Everything reduces, via the already-established bridge `Lₙ = 2·Fₙ₊₁ − Fₙ`, to a
single **pure Fibonacci identity**

    Fₙ₊₁² − Fₙ₊₁·Fₙ − Fₙ² = (−1)ⁿ              (`fib_sq_sub`)

— a sign-clean relative of Cassini's identity. This one closes under a
*one-step* induction: substituting `Fₙ₊₂ = Fₙ + Fₙ₊₁` turns the `(n+1)` form
into the negation of the `n` form (`ring`), so the value just flips sign at each
step. Substituting the bridge then gives `Lₙ² − 5Fₙ² = 4·(Fₙ₊₁² − Fₙ₊₁Fₙ − Fₙ²)
= 4(−1)ⁿ` by `linear_combination`.

The `gcd` corollary is elementary: any common divisor `d` of `Fₙ` and `Lₙ`
divides `Lₙ + Fₙ = 2·Fₙ₊₁`; since `Fₙ` and `Fₙ₊₁` are coprime
(`Nat.fib_coprime_fib_succ`), `d` is coprime to `Fₙ₊₁`, hence `d ∣ 2`.
-/

namespace FibonacciIdentitiesOQ02OQ01OQ01

open Nat

/-! ## Definition of the Lucas numbers

We reuse the structural pair recursion of the parent entry so this file is
self-contained. `lucas` reduces by `rfl` / `decide`. -/

/-- The pair `(Lₙ, Lₙ₊₁)`. -/
def lucasPair : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | n + 1 => ((lucasPair n).2, (lucasPair n).1 + (lucasPair n).2)

/-- The Lucas numbers `Lₙ`: `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ + Lₙ₊₁`. -/
def lucas (n : ℕ) : ℕ := (lucasPair n).1

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining recurrence `Lₙ₊₂ = Lₙ + Lₙ₊₁`. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-! ## The Fibonacci bridge `2·Fₙ₊₁ = Lₙ + Fₙ` -/

/-- The subtraction-free bridge `2·Fₙ₊₁ = Lₙ + Fₙ`, by two-step induction. -/
theorem two_mul_fib_succ (n : ℕ) : 2 * fib (n + 1) = lucas n + fib n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      have h1 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      have h2 : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two
      have h3 : lucas (n + 2) = lucas n + lucas (n + 1) := lucas_add_two n
      -- restate the IHs with `n+2` (defeq to `n+1+1`) so `omega` shares atoms
      have e1 : 2 * fib (n + 1) = lucas n + fib n := ih1
      have e2 : 2 * fib (n + 2) = lucas (n + 1) + fib (n + 1) := ih2
      show 2 * fib (n + 3) = lucas (n + 2) + fib (n + 2)
      omega

/-- The closed form over `ℤ`: `Lₙ = 2·Fₙ₊₁ − Fₙ` (no truncated subtraction). -/
theorem lucas_eq_int (n : ℕ) : (lucas n : ℤ) = 2 * fib (n + 1) - fib n := by
  have := two_mul_fib_succ n
  have : (2 * fib (n + 1) : ℤ) = lucas n + fib n := by exact_mod_cast this
  linarith

/-! ## The core Fibonacci identity `Fₙ₊₁² − Fₙ₊₁·Fₙ − Fₙ² = (−1)ⁿ` -/

/-- A sign-clean relative of Cassini's identity:
`Fₙ₊₁² − Fₙ₊₁·Fₙ − Fₙ² = (−1)ⁿ`, over `ℤ`. Proved by one-step induction —
substituting `Fₙ₊₂ = Fₙ + Fₙ₊₁` negates the form, so the sign alternates. -/
theorem fib_sq_sub (n : ℕ) :
    (fib (n + 1) : ℤ) ^ 2 - fib (n + 1) * fib n - (fib n) ^ 2 = (-1) ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have hrec : (fib (k + 1 + 1) : ℤ) = fib k + fib (k + 1) := by
        exact_mod_cast fib_add_two
      -- the `(k+1)`-form is the negation of the `k`-form (pure `ring` after `hrec`)
      have key : (fib (k + 1 + 1) : ℤ) ^ 2 - fib (k + 1 + 1) * fib (k + 1)
                   - (fib (k + 1)) ^ 2
               = -((fib (k + 1) : ℤ) ^ 2 - fib (k + 1) * fib k - (fib k) ^ 2) := by
        rw [hrec]; ring
      rw [key, ih]; ring

/-! ## The quadratic identity and its consequences -/

/-- **The Fibonacci–Lucas quadratic identity:** `Lₙ² − 5·Fₙ² = 4·(−1)ⁿ`,
over `ℤ`, for every `n`. The companion to the product identity
`F_{2n} = Fₙ·Lₙ`; the integer shadow of `φψ = −1` in Binet's formulas. -/
theorem lucas_sq_sub_five_fib_sq (n : ℕ) :
    (lucas n : ℤ) ^ 2 - 5 * (fib n) ^ 2 = 4 * (-1) ^ n := by
  have hb := lucas_eq_int n
  have hc := fib_sq_sub n
  -- substitute the bridge, then it is `4 ×` the core identity
  rw [hb]
  linear_combination 4 * hc

/-- `Lₙ² = 5·Fₙ² + 4·(−1)ⁿ`: the Lucas square is `5Fₙ²` shifted by the defect
`±4`. Rearrangement of `lucas_sq_sub_five_fib_sq`. -/
theorem lucas_sq_eq (n : ℕ) :
    (lucas n : ℤ) ^ 2 = 5 * (fib n) ^ 2 + 4 * (-1) ^ n := by
  have := lucas_sq_sub_five_fib_sq n; linarith

/-- The even-index specialisation `L_{2k}² = 5·F_{2k}² + 4` (defect `+4`). -/
theorem lucas_sq_even (k : ℕ) :
    (lucas (2 * k) : ℤ) ^ 2 = 5 * (fib (2 * k)) ^ 2 + 4 := by
  have h := lucas_sq_eq (2 * k)
  rw [Even.neg_one_pow ⟨k, by ring⟩] at h; linarith

/-- The odd-index specialisation `L_{2k+1}² = 5·F_{2k+1}² − 4` (defect `−4`). -/
theorem lucas_sq_odd (k : ℕ) :
    (lucas (2 * k + 1) : ℤ) ^ 2 = 5 * (fib (2 * k + 1)) ^ 2 - 4 := by
  have h := lucas_sq_eq (2 * k + 1)
  rw [Odd.neg_one_pow ⟨k, by ring⟩] at h; linarith

/-! ## `gcd(Fₙ, Lₙ) ∣ 2` -/

/-- **`gcd(Fₙ, Lₙ) ∣ 2`.** The Fibonacci and Lucas numbers of the same index
are coprime up to a factor of `2`, so `gcd(Fₙ, Lₙ) ∈ {1, 2}`. A common divisor
`d` of `Fₙ` and `Lₙ` divides `Lₙ + Fₙ = 2·Fₙ₊₁`; since `gcd(Fₙ, Fₙ₊₁) = 1`,
`d` is coprime to `Fₙ₊₁`, forcing `d ∣ 2`. -/
theorem gcd_fib_lucas_dvd_two (n : ℕ) : Nat.gcd (fib n) (lucas n) ∣ 2 := by
  set d := Nat.gcd (fib n) (lucas n) with hd
  have hdf : d ∣ fib n := Nat.gcd_dvd_left _ _
  have hdl : d ∣ lucas n := Nat.gcd_dvd_right _ _
  -- d divides 2·Fₙ₊₁ = Lₙ + Fₙ
  have hsum : lucas n + fib n = 2 * fib (n + 1) := (two_mul_fib_succ n).symm
  have hd2 : d ∣ 2 * fib (n + 1) := by
    rw [← hsum]; exact Dvd.dvd.add hdl hdf
  -- d is coprime to Fₙ₊₁ since it divides Fₙ and gcd(Fₙ, Fₙ₊₁) = 1
  have hcop : Nat.Coprime (fib n) (fib (n + 1)) := Nat.fib_coprime_fib_succ n
  have hdcop : Nat.Coprime d (fib (n + 1)) :=
    Nat.Coprime.coprime_dvd_left hdf hcop
  -- so d ∣ 2
  exact (Nat.Coprime.dvd_of_dvd_mul_right hdcop hd2)

/-- Consequently `gcd(Fₙ, Lₙ) ∈ {1, 2}`. -/
theorem gcd_fib_lucas_eq_one_or_two (n : ℕ) :
    Nat.gcd (fib n) (lucas n) = 1 ∨ Nat.gcd (fib n) (lucas n) = 2 := by
  have h := gcd_fib_lucas_dvd_two n
  exact (Nat.dvd_prime Nat.prime_two).mp h

/-! ## Concrete sanity checks -/

/-- `L₅² = 5·F₅² − 4`: `121 = 5·25 − 4`. -/
theorem check_five : (lucas 5 : ℤ) ^ 2 = 5 * (fib 5) ^ 2 - 4 := by decide

/-- `L₆² = 5·F₆² + 4`: `324 = 5·64 + 4`. -/
theorem check_six : (lucas 6 : ℤ) ^ 2 = 5 * (fib 6) ^ 2 + 4 := by decide

/-- `gcd(F₆, L₆) = gcd(8, 18) = 2` — the factor `2` is attained. -/
theorem gcd_six_attains_two : Nat.gcd (fib 6) (lucas 6) = 2 := by decide

/-- `gcd(F₅, L₅) = gcd(5, 11) = 1` — coprime case. -/
theorem gcd_five_coprime : Nat.gcd (fib 5) (lucas 5) = 1 := by decide

end FibonacciIdentitiesOQ02OQ01OQ01
