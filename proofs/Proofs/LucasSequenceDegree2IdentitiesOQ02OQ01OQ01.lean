import Mathlib.Tactic
import Proofs.LucasSequenceDegree2Identities
import Proofs.LucasSequenceDegree2IdentitiesOQ02

/-
# The Fundamental Lucas Sequence is a Divisibility Sequence: `Uₘ ∣ Uₘₙ`

## Open Question (answered)

The sibling entry `LucasSequenceDegree2IdentitiesOQ02OQ01` (the sharp gcd bound
`gcd(Uₙ, Vₙ) ∣ 2`) closes with the explicit open question:

> Prove the multiplication-by-index divisibility `Uₘ ∣ Uₘₙ` and the strong
> divisibility `gcd(Uₘ, Uₙ) = U_{gcd(m,n)}` for the general Lucas sequence.

This entry answers the **first half**: for the fundamental Lucas sequence
`Uₙ(P,Q)` (`U₀ = 0, U₁ = 1, Uₙ₊₂ = P·Uₙ₊₁ − Q·Uₙ`) with *arbitrary* integer
parameters `P, Q`,

  **`Uₘ ∣ Uₘₖ`  for all `m, k`**,   equivalently   **`m ∣ n ⟹ Uₘ ∣ Uₙ`**.

So `U` is a *divisibility sequence*.  This generalizes the classical facts
`Fₘ ∣ Fₙ` (Fibonacci, `(P,Q) = (1,−1)`) and `Pₘ ∣ Pₙ` (Pell, `(2,−1)`) whenever
`m ∣ n`.

## Proof architecture

The engine is a **subtraction-free bilinear addition law**, genuinely new to this
family (the parent `OQ-02` only records the factor-2 law `2·U_{m+n} = U_m V_n + V_m U_n`):

  **`U_add_clean` :  `U_{m+n+1} = U_{m+1}·U_{n+1} − Q·U_m·U_n`.**

It is derived purely algebraically — *no new induction* — from the parent's
`two_U_add` together with the companion relation `V_eq` (`Vₙ = 2Uₙ₊₁ − P Uₙ`) and the
recurrence `U_add_two`: substituting `V_{n+1} = 2U_{n+2} − P U_{n+1}`,
`V_m = 2U_{m+1} − P U_m`, and `U_{n+2} = P U_{n+1} − Q U_n` into `2·U_{m+n+1}` and
cancelling the factor `2` collapses everything to the clean form
(`linear_combination` discharges the algebra).

With the clean law in hand, `Uₘ ∣ Uₘₖ` is a one-line induction on `k`:
writing `m = m'+1` and `m·(k+1) = (m·k) + m' + 1`,

  `U_{m(k+1)} = U_{m·k+1}·U_m − Q·U_{m·k}·U_{m'}`,

whose first summand is visibly a multiple of `Uₘ` and whose second is a multiple of
`U_{m·k}` — divisible by `Uₘ` by the inductive hypothesis.

## Results

* `U_add_clean`      — the subtraction-free addition law `U_{m+n+1} = U_{m+1}U_{n+1} − Q U_m U_n`.
* `dvd_U_mul`        — `Uₘ ∣ U_{m·k}` (divisibility-sequence property).
* `U_dvd_of_dvd`     — `m ∣ n ⟹ Uₘ ∣ Uₙ`.
* `fib_dvd_of_dvd`   — Fibonacci instance `m ∣ n ⟹ Fₘ ∣ Fₙ`.
* `pell_dvd_of_dvd`  — Pell instance `m ∣ n ⟹ Pₘ ∣ Pₙ`.
* `fib_three_dvd_six`, `fib_three_six_values` — concrete `F₃ = 2 ∣ 8 = F₆`.
* `V_not_dvd_seq`    — sharpness: the *companion* sequence `V` is **not** a divisibility
  sequence (`V₂ = 3 ∤ 7 = V₄` for Fibonacci/Lucas), so the property is special to `U`.

## Axioms: 0 | Sorries: 0
-/

namespace LucasSequenceDegree2IdentitiesOQ02OQ01OQ01

open LucasSequenceDegree2Identities
open LucasSequenceDegree2IdentitiesOQ02

/-- **Subtraction-free bilinear addition law.**
`U_{m+n+1} = U_{m+1}·U_{n+1} − Q·U_m·U_n`.

Unlike the parent's factor-2 law `2·U_{m+n} = U_m V_n + V_m U_n`, this carries no
factor of `2`, which is exactly what makes it usable for divisibility.  It is obtained
without any new induction: substitute the companion relation `V_eq` for `V_{n+1}` and
`V_m` into `two_U_add`, use the recurrence for `U_{n+2}`, and cancel the `2`. -/
theorem U_add_clean (P Q : ℤ) (m n : ℕ) :
    U P Q (m + n + 1) = U P Q (m + 1) * U P Q (n + 1) - Q * U P Q m * U P Q n := by
  have h1 := two_U_add P Q m (n + 1)
  rw [← Nat.add_assoc] at h1
  have hVn1 := V_eq P Q (n + 1)
  have hVm := V_eq P Q m
  have hUn2 := U_add_two P Q n
  have h2 : 2 * U P Q (m + n + 1)
      = 2 * (U P Q (m + 1) * U P Q (n + 1) - Q * U P Q m * U P Q n) := by
    linear_combination h1 + U P Q m * hVn1 + U P Q (n + 1) * hVm + 2 * U P Q m * hUn2
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

/-- **Divisibility-sequence property.** `Uₘ ∣ U_{m·k}` for all `m, k`.

Induction on `k`.  The step writes `m = m'+1` and `m·(k+1) = (m·k) + m' + 1`, applies
`U_add_clean`, and reads off that both summands of
`U_{m·k+1}·U_m − Q·U_{m·k}·U_{m'}` are multiples of `Uₘ` (the first trivially, the
second by the inductive hypothesis `Uₘ ∣ U_{m·k}`). -/
theorem dvd_U_mul (P Q : ℤ) (m k : ℕ) : U P Q m ∣ U P Q (m * k) := by
  induction k with
  | zero => simp
  | succ j ih =>
    cases m with
    | zero => simp
    | succ m' =>
      have e : (m' + 1) * (j + 1) = (m' + 1) * j + m' + 1 := by ring
      rw [e, U_add_clean]
      exact dvd_sub (dvd_mul_left _ _) ((ih.mul_left Q).mul_right _)

/-- **`U` is a divisibility sequence.** `m ∣ n ⟹ Uₘ ∣ Uₙ`. -/
theorem U_dvd_of_dvd (P Q : ℤ) {m n : ℕ} (h : m ∣ n) : U P Q m ∣ U P Q n := by
  obtain ⟨k, rfl⟩ := h
  exact dvd_U_mul P Q m k

/-- **Fibonacci instance.** `m ∣ n ⟹ Fₘ ∣ Fₙ`  (`(P,Q) = (1,−1)`). -/
theorem fib_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : U 1 (-1) m ∣ U 1 (-1) n :=
  U_dvd_of_dvd 1 (-1) h

/-- **Pell instance.** `m ∣ n ⟹ Pₘ ∣ Pₙ`  (`(P,Q) = (2,−1)`). -/
theorem pell_dvd_of_dvd {m n : ℕ} (h : m ∣ n) : U 2 (-1) m ∣ U 2 (-1) n :=
  U_dvd_of_dvd 2 (-1) h

/-- Concrete Fibonacci divisibility `F₃ ∣ F₆`. -/
theorem fib_three_dvd_six : U 1 (-1) 3 ∣ U 1 (-1) 6 := fib_dvd_of_dvd (by norm_num)

/-- The concrete values `F₃ = 2`, `F₆ = 8`, so `fib_three_dvd_six` is the non-vacuous
`2 ∣ 8`.  Kernel `decide` (no `native_decide`). -/
theorem fib_three_six_values : U 1 (-1) 3 = 2 ∧ U 1 (-1) 6 = 8 := by decide

/-- **Sharpness: the companion sequence is not a divisibility sequence.**
`V₂ = 3` does not divide `V₄ = 7` for the Fibonacci/Lucas pair `(1,−1)`, even though
`2 ∣ 4`.  Hence the divisibility-sequence property is genuinely special to the
*fundamental* sequence `U`; the companion `V` satisfies only the weaker
odd-index divisibility.  Kernel `decide`. -/
theorem V_not_dvd_seq : ¬ (V 1 (-1) 2 ∣ V 1 (-1) 4) := by decide

end LucasSequenceDegree2IdentitiesOQ02OQ01OQ01
