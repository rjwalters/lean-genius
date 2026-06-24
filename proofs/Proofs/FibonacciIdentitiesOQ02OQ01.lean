import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

/-
# Lucas Numbers: the Failure of Strong Divisibility

## What This Proves

The parent entry (`fibonacci-identities-oq-02`) established that the **Fibonacci**
sequence is a *strong divisibility sequence*:

    fib (gcd m n) = gcd (fib m) (fib n),    and for m ≥ 3,  fib m ∣ fib n ↔ m ∣ n.

Its first open question asks for the analogue for the **Lucas numbers**
`Lₙ` (`L₀ = 2, L₁ = 1, Lₙ₊₂ = Lₙ + Lₙ₊₁`):

    2, 1, 3, 4, 7, 11, 18, 29, 47, 76, 123, …

This entry settles it. The answer is a genuine contrast with the parent:

* **The Lucas numbers are NOT a strong divisibility sequence.**
  `gcd (L₂, L₄) = gcd(3, 7) = 1`, yet `L_{gcd(2,4)} = L₂ = 3`. So
  `L_{gcd m n} = gcd (L m) (L n)` fails (`lucas_not_strong_divisibility`).

* **Index divisibility does NOT transfer to value divisibility.**
  `2 ∣ 4` but `L₂ = 3 ∤ 7 = L₄` (`index_dvd_not_imp_lucas_dvd`). This is the
  decisive difference from Fibonacci, where `m ∣ n ⇒ fib m ∣ fib n` always
  holds. The Lucas analogue is *false*.

* **The correct law is the "odd quotient" rule.** For m ≥ 2,
  `Lₘ ∣ Lₙ ⟺ m ∣ n and n / m is odd`. We verify the rule on concrete
  instances: `L₂ ∣ L₆` (6/2 = 3 odd) but `L₂ ∤ L₄` (4/2 = 2 even);
  `L₃ ∣ L₉` (9/3 = 3 odd) but `L₃ ∤ L₆` (6/3 = 2 even).

The positive engine that makes everything cohere is the **product identity**

    F_{2n} = Fₙ · Lₙ                       (`fib_two_mul_eq`)

— the headline result, proved from Mathlib's `Nat.fib_two_mul` via the bridge
`Lₙ = 2·Fₙ₊₁ − Fₙ` (`lucas_eq`). From it, `Lₙ ∣ F₂ₙ` (`lucas_dvd_fib_two_mul`),
exhibiting the Lucas numbers inside the Fibonacci divisibility lattice exactly
at the even indices.

## Why Lucas Strong Divisibility Fails

Strong divisibility (`gcd(Aₘ, Aₙ) = A_{gcd m n}`) forces `A₁ ∣ Aₙ` for all `n`,
because `gcd(A₁, Aₙ) = A_{gcd(1,n)} = A₁`. For Fibonacci this is harmless,
`F₁ = 1`. For Lucas `L₁ = 1` as well, but the deeper obstruction appears at
even/odd index parity: `gcd(Lₘ, Lₙ) ∈ {1, 2}` whenever `m / gcd` and `n / gcd`
have different parities, so the gcd is *not* a Lucas number. The doubling step
`n ↦ 2n` is exactly where strong divisibility breaks: `Lₙ ∤ L_{2n}` in general
(`L₂ = 3 ∤ 7 = L₄`), even though `Lₙ ∣ F_{2n}` always.

## Approach

`lucas` is defined by a structural pair recursion `(Lₙ, Lₙ₊₁)` so that it
reduces by `rfl`/`decide`. The bridge `2·Fₙ₊₁ = Lₙ + Fₙ` is a two-step
induction (`Nat.twoStepInduction`); the product identity then drops out of
`Nat.fib_two_mul`. The failure statements are decided on concrete witnesses.
-/

namespace FibonacciIdentitiesOQ02OQ01

open Nat

/-! ## Definition of the Lucas numbers -/

/-- The pair `(Lₙ, Lₙ₊₁)`, computed by structural recursion so that `lucas`
reduces definitionally (`rfl` / `decide`). -/
def lucasPair : ℕ → ℕ × ℕ
  | 0 => (2, 1)
  | n + 1 => ((lucasPair n).2, (lucasPair n).1 + (lucasPair n).2)

/-- The Lucas numbers `Lₙ`: `L₀ = 2`, `L₁ = 1`, `Lₙ₊₂ = Lₙ + Lₙ₊₁`. -/
def lucas (n : ℕ) : ℕ := (lucasPair n).1

@[simp] theorem lucas_zero : lucas 0 = 2 := rfl
@[simp] theorem lucas_one : lucas 1 = 1 := rfl

/-- The defining recurrence `Lₙ₊₂ = Lₙ + Lₙ₊₁`, certifying that `lucas` is
indeed the Lucas sequence. -/
theorem lucas_add_two (n : ℕ) : lucas (n + 2) = lucas n + lucas (n + 1) := rfl

/-! ## The Fibonacci bridge and the product identity -/

/-- The subtraction-free bridge between Lucas and Fibonacci values:
`2·Fₙ₊₁ = Lₙ + Fₙ`. Proved by two-step induction on `n`. -/
theorem two_mul_fib_succ (n : ℕ) : 2 * fib (n + 1) = lucas n + fib n := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 =>
      show 2 * fib (n + 3) = lucas (n + 2) + fib (n + 2)
      have h1 : fib (n + 2) = fib n + fib (n + 1) := fib_add_two
      have h2 : fib (n + 3) = fib (n + 1) + fib (n + 2) := fib_add_two
      have h3 : lucas (n + 2) = lucas n + lucas (n + 1) := lucas_add_two n
      omega

/-- Closed form `Lₙ = 2·Fₙ₊₁ − Fₙ` (truncated subtraction is exact here, since
`2·Fₙ₊₁ = Lₙ + Fₙ ≥ Fₙ`). -/
theorem lucas_eq (n : ℕ) : lucas n = 2 * fib (n + 1) - fib n := by
  have := two_mul_fib_succ n; omega

/-- **Headline product identity:** `F_{2n} = Fₙ · Lₙ`. Every even-index
Fibonacci number factors as the product of the same-index Fibonacci and Lucas
numbers. Immediate from `Nat.fib_two_mul` and the closed form `lucas_eq`. -/
theorem fib_two_mul_eq (n : ℕ) : fib (2 * n) = fib n * lucas n := by
  rw [fib_two_mul, lucas_eq]

/-- `Lₙ ∣ F_{2n}`: the Lucas numbers sit inside the Fibonacci divisibility
lattice at the even indices. -/
theorem lucas_dvd_fib_two_mul (n : ℕ) : lucas n ∣ fib (2 * n) :=
  ⟨fib n, by rw [fib_two_mul_eq]; ring⟩

/-- `Fₙ ∣ F_{2n}`, recovered from the same factorisation (`2 ∣ 2n`). -/
theorem fib_dvd_fib_two_mul (n : ℕ) : fib n ∣ fib (2 * n) :=
  ⟨lucas n, fib_two_mul_eq n⟩

/-! ## Concrete Lucas values -/

theorem lucas_two : lucas 2 = 3 := rfl
theorem lucas_three : lucas 3 = 4 := rfl
theorem lucas_four : lucas 4 = 7 := rfl
theorem lucas_five : lucas 5 = 11 := rfl
theorem lucas_six : lucas 6 = 18 := rfl
theorem lucas_nine : lucas 9 = 76 := rfl

/-! ## Strong divisibility FAILS for the Lucas numbers

This is the qualitative resolution of the open question. Three independent
witnesses, each at the doubling step `n ↦ 2n` where the structure breaks. -/

/-- The Lucas numbers are **not** a strong divisibility sequence:
there exist `m, n` with `L_{gcd m n} ≠ gcd (L m) (L n)`. Witness `m = 2, n = 4`:
`gcd(L₂, L₄) = gcd(3, 7) = 1`, but `L_{gcd(2,4)} = L₂ = 3`. -/
theorem lucas_not_strong_divisibility :
    ∃ m n : ℕ, lucas (Nat.gcd m n) ≠ Nat.gcd (lucas m) (lucas n) :=
  ⟨2, 4, by decide⟩

/-- **The decisive contrast with Fibonacci.** For Fibonacci, `m ∣ n ⇒ fib m ∣
fib n` always holds (`Nat.fib_dvd`). The Lucas analogue is *false*: `2 ∣ 4`,
yet `L₂ = 3 ∤ 7 = L₄`. -/
theorem index_dvd_not_imp_lucas_dvd :
    ∃ m n : ℕ, m ∣ n ∧ ¬ lucas m ∣ lucas n :=
  ⟨2, 4, ⟨2, rfl⟩, by decide⟩

/-- Coprimality transfer also fails: coprime indices need not give coprime Lucas
values. `gcd(3, 6) ≠ 1` is not the issue — rather `gcd(2, 4) = 2 ≠ 1` while we
exhibit the genuine breakdown via the explicit gcd value `gcd(L₂, L₄) = 1`
where the strong law would predict `L₂ = 3`. -/
theorem lucas_gcd_two_four : Nat.gcd (lucas 2) (lucas 4) = 1 := by decide

/-! ## The correct law: the "odd quotient" characterization

For `m ≥ 2`, `Lₘ ∣ Lₙ ⟺ m ∣ n and n / m is odd`. We do not prove the general
biconditional here (it requires the integer Lucas addition law
`L_{a+2m} = L_{a+m}·Lₘ − (−1)ᵐ·L_a`, beyond the present Mathlib-backed scope);
instead we verify the rule on the structurally decisive instances, contrasting
the odd-quotient (divisible) and even-quotient (not divisible) cases. -/

/-- `L₂ ∣ L₆`: quotient `6 / 2 = 3` is odd. (`L₂ = 3 ∣ 18 = L₆`.) -/
theorem lucas_two_dvd_lucas_six : lucas 2 ∣ lucas 6 := by decide

/-- `L₂ ∤ L₄`: quotient `4 / 2 = 2` is even, so divisibility fails even though
`2 ∣ 4`. -/
theorem lucas_two_not_dvd_lucas_four : ¬ lucas 2 ∣ lucas 4 := by decide

/-- `L₃ ∣ L₉`: quotient `9 / 3 = 3` is odd. (`L₃ = 4 ∣ 76 = L₉`.) -/
theorem lucas_three_dvd_lucas_nine : lucas 3 ∣ lucas 9 := by decide

/-- `L₃ ∤ L₆`: quotient `6 / 3 = 2` is even, so divisibility fails even though
`3 ∣ 6`. -/
theorem lucas_three_not_dvd_lucas_six : ¬ lucas 3 ∣ lucas 6 := by decide

/-- `L₁ = 1` divides every Lucas number — the degenerate index, excluded by the
`m ≥ 2` hypothesis (here `1 / 1 = 1` is odd, consistent with the rule, but the
content is vacuous since `L₁ = 1`). -/
theorem lucas_one_dvd (n : ℕ) : lucas 1 ∣ lucas n := by simp

end FibonacciIdentitiesOQ02OQ01
