import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-
# The Catalan Closed Form via Factorials

Open Question: combinations-formula-oq-02-oq-02

The parent entry (`combinations-formula-oq-02`) defines the Catalan number by the
ballot-style subtraction

  C_n = C(2n, n) - C(2n, n+1)

and establishes the closed form `C_n = C(2n,n)/(n+1)` **through** the multiplicative
identity `catalan_mul_succ : C_n * (n+1) = C(2n,n)`, which it proves from the pure
binomial absorption identity (`Nat.succ_mul_choose_eq`).

This entry answers the open question:

> "Prove the closed form C_n = C(2n,n)/(n+1) directly without going through
>  catalan_mul_succ."

We take a genuinely different route: **factorials**. The only external inputs are
`Nat.choose_mul_factorial_mul_factorial` (the factorial expansion of a single binomial
coefficient) and `Nat.choose_le_middle` (row-maximality of the central coefficient).
From these we prove, by cancelling a common factorial factor, the *cross identity*

  C(2n,n) * n = C(2n,n+1) * (n+1),

and everything else — the multiplicative identity, the requested division form
`C_n = C(2n,n)/(n+1)`, the divisibility `(n+1) ∣ C(2n,n)`, and the fully-factorial
closed form `C_n = (2n)! / ((n+1)! · n!)` — falls out as a consequence.

Main results:
- `choose_cross`        : C(2n,n) · n = C(2n,n+1) · (n+1)          [factorial cancellation]
- `catalan_mul_succ'`   : C_n · (n+1) = C(2n,n)                     [re-derived, not assumed]
- `catalan_eq_choose_div` : C_n = C(2n,n) / (n+1)                   [**the requested form**]
- `succ_dvd_centralBinom` : (n+1) ∣ C(2n,n)
- `catalan_mul_factorial_factorial` : C_n · ((n+1)! · n!) = (2n)!   [factorial closed form]
- `catalan_eq_factorial_div` : C_n = (2n)! / ((n+1)! · n!)

References:
- Stanley (2015), "Catalan Numbers", Cambridge Univ. Press (Eq. for C_n via factorials)
- Parent: CombinationsFormulaOQ02.lean
-/

open Nat

namespace CatalanClosedForm

/-- The n-th Catalan number, defined (as in the parent entry) by the ballot
    subtraction `C_n = C(2n, n) - C(2n, n+1)`. -/
def catalan (n : ℕ) : ℕ :=
  Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1)

/-
## Part I: The factorial cross identity (keystone)

The single fact from which every closed form below is derived. We prove it by
expanding both `C(2n,n)` and `C(2n,n+1)` into factorials and cancelling the common
factor `(n+1)! · n!` — this never touches the multiplicative Catalan identity.
-/

/-- **Cross identity**: `C(2n, n) · n = C(2n, n+1) · (n+1)`.

    Proof: both `C(2n,n) · n · (n+1)! · n!` and `C(2n,n+1) · (n+1) · (n+1)! · n!`
    equal `(2n)!` (via `Nat.choose_mul_factorial_mul_factorial`), so they are equal;
    cancel the positive factor `(n+1)! · n!`. -/
theorem choose_cross (n : ℕ) :
    Nat.choose (2 * n) n * n = Nat.choose (2 * n) (n + 1) * (n + 1) := by
  rcases n with _ | m
  · decide
  · -- n = m + 1
    have hAle : m + 1 ≤ 2 * (m + 1) := by omega
    have hBle : m + 2 ≤ 2 * (m + 1) := by omega
    -- C(2n, n) · (n)! · (n)! = (2n)!   with n = m+1
    have hA : Nat.choose (2 * (m + 1)) (m + 1) * (m + 1)! * (m + 1)! = (2 * (m + 1))! := by
      have h := Nat.choose_mul_factorial_mul_factorial hAle
      rwa [show 2 * (m + 1) - (m + 1) = m + 1 from by omega] at h
    -- C(2n, n+1) · (n+1)! · (n-1)! = (2n)!   with n = m+1, so n+1 = m+2, n-1 = m
    have hB : Nat.choose (2 * (m + 1)) (m + 2) * (m + 2)! * m ! = (2 * (m + 1))! := by
      have h := Nat.choose_mul_factorial_mul_factorial hBle
      rwa [show 2 * (m + 1) - (m + 2) = m from by omega] at h
    have hQ : 0 < (m + 1)! * m ! := by positivity
    apply Nat.eq_of_mul_eq_mul_right hQ
    calc Nat.choose (2 * (m + 1)) (m + 1) * (m + 1) * ((m + 1)! * m !)
        = Nat.choose (2 * (m + 1)) (m + 1) * (m + 1)! * (m + 1)! := by
          rw [Nat.factorial_succ m]; ring
      _ = (2 * (m + 1))! := hA
      _ = Nat.choose (2 * (m + 1)) (m + 2) * (m + 2)! * m ! := hB.symm
      _ = Nat.choose (2 * (m + 1)) (m + 2) * (m + 2) * ((m + 1)! * m !) := by
          rw [Nat.factorial_succ (m + 1)]; ring

/-
## Part II: The multiplicative identity, re-derived from the cross identity
-/

/-- `C(2n, n+1) ≤ C(2n, n)`: the entry just past the centre of an even row does not
    exceed the central (maximal) entry. Makes the ballot subtraction non-truncating. -/
theorem choose_succ_le_central (n : ℕ) :
    Nat.choose (2 * n) (n + 1) ≤ Nat.choose (2 * n) n := by
  have h := Nat.choose_le_middle (n + 1) (2 * n)
  rwa [show 2 * n / 2 = n from by omega] at h

/-- **Multiplicative identity, re-derived**: `C_n · (n+1) = C(2n, n)`.

    Unlike the parent's `catalan_mul_succ`, this is obtained purely from the factorial
    cross identity `choose_cross`. -/
theorem catalan_mul_succ' (n : ℕ) :
    catalan n * (n + 1) = Nat.choose (2 * n) n := by
  rcases n with _ | m
  · decide
  · have hle := choose_succ_le_central (m + 1)
    have hc := choose_cross (m + 1)
    -- hc : C(2n,n) · n = C(2n,n+1) · (n+1),  with n = m+1
    -- Abbreviate the two coefficients; `hc`, `hle` are the only facts needed.
    have key : (Nat.choose (2 * (m + 1)) (m + 1) - Nat.choose (2 * (m + 1)) (m + 2))
        * (m + 1 + 1) = Nat.choose (2 * (m + 1)) (m + 1) := by
      rw [Nat.sub_mul]
      -- C(2n,n)·(n+1) - C(2n,n+1)·(n+1); replace C(2n,n+1)·(n+1) by C(2n,n)·n via hc
      rw [← hc]
      -- goal: C(2n,n)·(m+2) - C(2n,n)·(m+1) = C(2n,n)
      have : Nat.choose (2 * (m + 1)) (m + 1) * (m + 1 + 1)
           = Nat.choose (2 * (m + 1)) (m + 1) * (m + 1)
             + Nat.choose (2 * (m + 1)) (m + 1) := by ring
      omega
    -- Fold the definition of `catalan (m+1)`.
    simpa [catalan, show 2 * (m + 1) = 2 * (m + 1) from rfl] using key

/-
## Part III: The closed forms
-/

/-- **The requested closed form**: `C_n = C(2n, n) / (n+1)` (natural-number division),
    established without invoking the parent's `catalan_mul_succ`. -/
theorem catalan_eq_choose_div (n : ℕ) :
    catalan n = Nat.choose (2 * n) n / (n + 1) := by
  have h : Nat.choose (2 * n) n = (n + 1) * catalan n := by
    rw [← catalan_mul_succ' n]; ring
  rw [h, Nat.mul_div_cancel_left _ (Nat.succ_pos n)]

/-- Divisibility corollary: `(n+1) ∣ C(2n, n)`. -/
theorem succ_dvd_centralBinom (n : ℕ) : (n + 1) ∣ Nat.choose (2 * n) n :=
  ⟨catalan n, by rw [← catalan_mul_succ' n]; ring⟩

/-- **Factorial closed form**: `C_n · ((n+1)! · n!) = (2n)!`.

    This is the most symmetric closed form; it follows from the multiplicative identity
    and the factorial expansion of the central coefficient. Valid for all `n` (no case
    split), since `(n+1)! = (n+1)·n!` and `C(2n,n)·n!·n! = (2n)!`. -/
theorem catalan_mul_factorial_factorial (n : ℕ) :
    catalan n * ((n + 1)! * n !) = (2 * n)! := by
  have hmul := catalan_mul_succ' n
  have hcf := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [show 2 * n - n = n from by omega] at hcf
  calc catalan n * ((n + 1)! * n !)
      = (catalan n * (n + 1)) * (n ! * n !) := by rw [Nat.factorial_succ n]; ring
    _ = Nat.choose (2 * n) n * (n ! * n !) := by rw [hmul]
    _ = Nat.choose (2 * n) n * n ! * n ! := by ring
    _ = (2 * n)! := hcf

/-- `C_n = (2n)! / ((n+1)! · n!)` (natural-number division). -/
theorem catalan_eq_factorial_div (n : ℕ) :
    catalan n = (2 * n)! / ((n + 1)! * n !) := by
  have h : (2 * n)! = ((n + 1)! * n !) * catalan n := by
    rw [← catalan_mul_factorial_factorial n]; ring
  have hpos : 0 < (n + 1)! * n ! := by positivity
  rw [h, Nat.mul_div_cancel_left _ hpos]

/-
## Part IV: Consistency checks
-/

/-- The closed forms reproduce the standard initial values. -/
theorem catalan_values :
    catalan 0 = 1 ∧ catalan 1 = 1 ∧ catalan 2 = 2 ∧
    catalan 3 = 5 ∧ catalan 4 = 14 ∧ catalan 5 = 42 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Our `catalan` agrees with Mathlib's `catalan`, confirming the definition and the
    derived closed forms describe the genuine Catalan sequence. -/
theorem catalan_eq_mathlib (n : ℕ) : catalan n = _root_.catalan n := by
  have hmul : catalan n * (n + 1) = Nat.centralBinom n := catalan_mul_succ' n
  rw [_root_.catalan_eq_centralBinom_div, ← hmul, Nat.mul_div_cancel _ (Nat.succ_pos n)]

end CatalanClosedForm
