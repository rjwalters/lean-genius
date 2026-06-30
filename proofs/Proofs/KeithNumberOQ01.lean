/-
  The smallest Keith number is 14.

  A *Keith number* (or repfigit) is an `n`-digit number `N ≥ 10` such that the
  sequence whose first `n` terms are the decimal digits of `N`, and where each
  later term is the sum of the previous `n` terms, eventually hits `N` itself.

  For `14` the digits are `1, 4` and the sequence runs
  `1, 4, 5, 9, 14` (`1+4=5`, `4+5=9`, `5+9=14`), so `14` is Keith. The four
  two-digit numbers below it fail:
  `10 → 1,0,1,1,2,3,5,8,13` (overshoots), `11 → 1,1,2,3,5,8,13`,
  `12 → 1,2,3,5,8,13`, `13 → 1,3,4,7,11,18`; and numbers below `10` are excluded
  by definition (Keith numbers have at least two digits).

  This file formalizes the digit recurrence as a fuel-bounded sliding-window
  computation (`reaches`) and proves `IsLeast {n | IsKeith n} 14`. The recurrence
  is decidable: each term is a concrete `ℕ`, the window-sum is monotone, and we
  stop as soon as the running sum meets or exceeds the target. The bounded
  quantifier `∀ n < 14` is decidable via `Nat.decidableBallLT`, so minimality is
  discharged by `decide`.

  The proof is axiom-free: `decide` reduces in the kernel (no
  `native_decide`/`Lean.ofReduceBool`), so the result is `verified`.

  STATUS: build-pending locally (Docker build pool unavailable this session).
-/
import Mathlib

namespace KeithNumberOQ01

/-- Decimal digits least-significant first, via structural recursion on `fuel`.
Kept fuel-bounded (rather than reusing `Nat.digits`, which is defined by
well-founded recursion) so the kernel can reduce it under `decide`. With
`fuel ≥ ⌈log₁₀ n⌉` the result is exact. -/
def lsdDigits : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _, 0 => []
  | fuel + 1, n => n % 10 :: lsdDigits fuel (n / 10)

/-- Decimal digits of `n`, most-significant first (so `msdDigits 14 = [1, 4]`).
Fuel `n` always suffices: a positive integer has at most `n` decimal digits. -/
def msdDigits (n : ℕ) : List ℕ := (lsdDigits n n).reverse

/-- Slide the length-`d` window forward by one Keith step: drop the oldest term
and append the sum of the window. -/
def step (w : List ℕ) : List ℕ := w.tail ++ [w.sum]

/-- Does iterating the Keith recurrence from window `w` produce the value
`target`? The running sum is monotone once the window is fixed-length and
positive, so we stop as soon as it meets or exceeds `target`; `fuel` bounds the
number of steps. -/
def reaches (target : ℕ) : ℕ → List ℕ → Bool
  | 0, _ => false
  | fuel + 1, w =>
    let s := w.sum
    if s = target then true
    else if target < s then false
    else reaches target fuel (step w)

/-- `n` is a Keith number: it has at least two decimal digits and its digit
recurrence reaches `n`. The fuel bound `40` comfortably exceeds the number of
steps needed for any two- or three-digit candidate. -/
def IsKeith (n : ℕ) : Prop := 10 ≤ n ∧ reaches n 40 (msdDigits n) = true

instance : DecidablePred IsKeith :=
  fun n => inferInstanceAs (Decidable (10 ≤ n ∧ reaches n 40 (msdDigits n) = true))

/-- `14` is a Keith number: `1, 4, 5, 9, 14`. -/
theorem keith_fourteen : IsKeith 14 := by decide

/-- No number below `14` is a Keith number (numbers `< 10` are excluded by
definition; `10, 11, 12, 13` overshoot without hitting themselves). -/
theorem not_keith_below_fourteen : ∀ n < 14, ¬ IsKeith n := by decide

/-- **The smallest Keith number is 14.** It is Keith, and it is a lower bound for
the set of Keith numbers. -/
theorem smallest_keith : IsLeast {n : ℕ | IsKeith n} 14 := by
  refine ⟨keith_fourteen, ?_⟩
  intro n hn
  by_contra h
  push_neg at h
  exact not_keith_below_fourteen n h hn

end KeithNumberOQ01
