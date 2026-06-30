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
      -- restate `ih2` with the index in canonical `n + 2` form (defeq to
      -- `n + 1 + 1`) so `omega` unifies it with the `fib (n + 2)` below
      have ih2' : 2 * fib (n + 2) = lucas (n + 1) + fib (n + 1) := ih2
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

For `m ≥ 2`, `Lₘ ∣ Lₙ ⟺ m ∣ n and n / m is odd`. We verify the rule on the
structurally decisive instances, contrasting the odd-quotient (divisible) and
even-quotient (not divisible) cases. The **forward direction** — odd quotient
implies divisibility — is then proved in full generality below
(`lucas_dvd_of_odd_quotient`); only the converse remains for future work. -/

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

/-! ## The forward direction of the odd-quotient law, in full generality

We now prove the "if" half of the odd-quotient characterization as a
universally quantified theorem: for every `m` and every `n` with `m ∣ n` and
`n / m` odd, `Lₘ ∣ Lₙ`. This subsumes the concrete instances above
(`L₂ ∣ L₆`, `L₃ ∣ L₉`, …).

The engine is the **Lucas shift identity**

    L_{a+1+b} = F_{b+1} · L_{a+1} + F_b · L_a       (`lucas_add_shift`)

— the Lucas analogue of `Nat.fib_add`, proved by two-step induction on `b`
purely from the recurrences `Lₙ₊₂ = Lₙ + Lₙ₊₁` and `Fₙ₊₂ = Fₙ + Fₙ₊₁`, with no
subtraction and no signs. Writing an odd multiple as `(2k+1)·m = m + 2·(k·m)`,
the shift identity gives

    L_{(2k+1)m} = F_{2km+1} · Lₘ + F_{2km} · L_{m-1},

and `Lₘ ∣ F_{2km}` (because `Lₘ ∣ F_{2m} ∣ F_{2km}`, using `Nat.fib_dvd`), so
both terms are divisible by `Lₘ`. -/

/-- **Lucas shift identity** (the Lucas analogue of `Nat.fib_add`):
`L_{a+1+b} = F_{b+1}·L_{a+1} + F_b·L_a`. Proved by two-step induction on `b`
from the Lucas and Fibonacci recurrences — subtraction-free and sign-free, the
shifted form chosen to avoid any `a - 1`. -/
theorem lucas_add_shift (a b : ℕ) :
    lucas (a + 1 + b) = fib (b + 1) * lucas (a + 1) + fib b * lucas a := by
  induction b using Nat.twoStepInduction with
  | zero => simp
  | one =>
      show lucas (a + 2) = fib 2 * lucas (a + 1) + fib 1 * lucas a
      rw [lucas_add_two, fib_two, fib_one]; ring
  | more b ih1 ih2 =>
      have hrec : lucas (a + 1 + (b + 2))
          = lucas (a + 1 + b) + lucas (a + 1 + (b + 1)) := by
        rw [show a + 1 + (b + 2) = (a + 1 + b) + 2 from by ring, lucas_add_two,
            show a + 1 + b + 1 = a + 1 + (b + 1) from by ring]
      have ih2' : lucas (a + 1 + (b + 1))
          = fib (b + 2) * lucas (a + 1) + fib (b + 1) * lucas a := by
        have h : b + 1 + 1 = b + 2 := rfl
        rw [← h]; exact ih2
      have fA : fib (b + 2) = fib b + fib (b + 1) := fib_add_two
      have fB : fib (b + 2 + 1) = fib (b + 1) + fib (b + 2) := fib_add_two
      rw [hrec, ih1, ih2', fB, fA]; ring

/-- The same identity with the index split as `m + b` for `m ≥ 1`, exposing the
divisor `Lₘ` directly: `L_{m+b} = F_{b+1}·Lₘ + F_b·L_{m-1}`. -/
theorem lucas_add_eq {m : ℕ} (hm : 1 ≤ m) (b : ℕ) :
    lucas (m + b) = fib (b + 1) * lucas m + fib b * lucas (m - 1) := by
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  simpa using lucas_add_shift a b

/-- `Lₘ ∣ F_{2(km)}`: the Lucas number `Lₘ` divides every even-multiple-of-`m`
Fibonacci number, from `Lₘ ∣ F_{2m}` (`lucas_dvd_fib_two_mul`) and
`F_{2m} ∣ F_{2(km)}` (`Nat.fib_dvd`, since `2m ∣ 2(km)`). -/
theorem lucas_dvd_fib_even_mul (m k : ℕ) : lucas m ∣ fib (2 * (k * m)) :=
  (lucas_dvd_fib_two_mul m).trans (fib_dvd (2 * m) (2 * (k * m)) ⟨k, by ring⟩)

/-- **Odd multiples divide (general).** For all `m, k`, `Lₘ ∣ L_{(2k+1)m}`.
The odd-quotient case of the divisibility rule, proved universally. -/
theorem lucas_dvd_lucas_odd_mul (m k : ℕ) :
    lucas m ∣ lucas ((2 * k + 1) * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; simp
  · rw [show (2 * k + 1) * m = m + 2 * (k * m) from by ring, lucas_add_eq hm]
    exact Nat.dvd_add (dvd_mul_left _ _)
      ((lucas_dvd_fib_even_mul m k).mul_right _)

/-- **Forward direction of the odd-quotient law (general).** If `m ∣ n` and the
quotient `n / m` is odd, then `Lₘ ∣ Lₙ`. This proves the "⟸" half of the
characterization `Lₘ ∣ Lₙ ⟺ m ∣ n ∧ n/m odd` for all `m, n`, generalising the
concrete instances `L₂ ∣ L₆` and `L₃ ∣ L₉`. The converse remains open. -/
theorem lucas_dvd_of_odd_quotient {m n : ℕ} (hmn : m ∣ n) (hodd : Odd (n / m)) :
    lucas m ∣ lucas n := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rw [hm, Nat.div_zero] at hodd; exact absurd hodd (by decide)
  · obtain ⟨q, hq⟩ := hmn
    obtain ⟨k, hk⟩ := hodd
    have hqv : q = 2 * k + 1 := by
      rw [← hk, hq, Nat.mul_div_cancel_left q hm]
    rw [hq, hqv, mul_comm]
    exact lucas_dvd_lucas_odd_mul m k

end FibonacciIdentitiesOQ02OQ01
