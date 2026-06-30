/-
# Keith numbers in an arbitrary base

The parent entry `KeithNumberOQ01` defines a *Keith number* (repfigit) through a
fuel-bounded sliding-window recurrence over its **decimal** digits and proves the
smallest one is `14`. The base `10` is hard-wired into the digit extraction
(`n % 10`, `n / 10`).

This follow-up removes that hard-wiring. The Keith *recurrence* itself —
"drop the oldest window term, append the window sum, stop when you reach the
target" — never mentions a base; only the initial window (the digits of `n`)
does. So we keep the parent's base-independent `step`/`reaches` and generalize
only the digit extraction to an arbitrary base `b`:

* **`lsdDigitsB` / `msdDigitsB`** : base-`b` digits, generalizing `lsdDigits` /
  `msdDigits`.
* **`IsKeithBase b n`** : `n` has at least two base-`b` digits (`b ≤ n`) and its
  base-`b` digit recurrence reaches `n`.

The base-`10` predicate is recovered exactly:

* **`isKeithBase_ten`** : `IsKeithBase 10 n ↔ IsKeith n`, and hence
* **`smallest_keithBase10`** : `IsLeast {n | IsKeithBase 10 n} 14` — the parent's
  headline theorem re-derived through the general definition.

Other bases admit their own small Keith numbers, which the decision procedure
confirms directly:

* **`keithBase4_five`** : `5 = (11)_4` is Keith in base `4` (`1,1,2,3,5`), and
* **`smallest_keithBase4`** : `IsLeast {n | IsKeithBase 4 n} 5` — `5` is the
  smallest base-`4` Keith number, the base-`4` analogue of `14` in base `10`.

Like the parent, every result is axiom-free: the digit recurrence reduces in the
kernel under `decide` (no `native_decide` / `Lean.ofReduceBool`).

Reference: https://en.wikipedia.org/wiki/Keith_number
-/
import Mathlib
import Proofs.KeithNumberOQ01

namespace KeithNumberOQ01OQ02

open KeithNumberOQ01

/-- Base-`b` digits, least-significant first, via structural recursion on `fuel`
(generalizing `KeithNumberOQ01.lsdDigits`, which fixes `b = 10`). Kept
fuel-bounded so the kernel can reduce it under `decide`. With `fuel ≥ ⌈log_b n⌉`
the result is exact; fuel `n` always suffices. -/
def lsdDigitsB (b : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | _, 0 => []
  | fuel + 1, n => n % b :: lsdDigitsB b fuel (n / b)

/-- Base-`b` digits of `n`, most-significant first
(so `msdDigitsB 4 5 = [1, 1]`). -/
def msdDigitsB (b n : ℕ) : List ℕ := (lsdDigitsB b n n).reverse

/-- `n` is a Keith number **in base `b`**: it has at least two base-`b` digits
(`b ≤ n`) and its base-`b` digit recurrence reaches `n`. The window steps
(`KeithNumberOQ01.step` / `reaches`) are inherited unchanged from the parent —
only the initial window depends on the base. -/
def IsKeithBase (b n : ℕ) : Prop := b ≤ n ∧ reaches n 40 (msdDigitsB b n) = true

instance (b : ℕ) : DecidablePred (IsKeithBase b) :=
  fun n => inferInstanceAs (Decidable (b ≤ n ∧ reaches n 40 (msdDigitsB b n) = true))

/- ## Recovering the decimal predicate -/

/-- Base-`10` digit extraction agrees with the parent's decimal extraction. -/
theorem lsdDigitsB_ten (fuel n : ℕ) : lsdDigitsB 10 fuel n = lsdDigits fuel n := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    cases n with
    | zero => rfl
    | succ m => simp only [lsdDigitsB, lsdDigits, ih]

theorem msdDigitsB_ten (n : ℕ) : msdDigitsB 10 n = msdDigits n := by
  unfold msdDigitsB msdDigits
  rw [lsdDigitsB_ten]

/-- **Recovery of the decimal predicate.** Base-`10` Keith numbers are exactly the
Keith numbers of the parent file. -/
theorem isKeithBase_ten (n : ℕ) : IsKeithBase 10 n ↔ IsKeith n := by
  unfold IsKeithBase IsKeith
  rw [msdDigitsB_ten]

theorem keithBase10_setOf_eq : {n | IsKeithBase 10 n} = {n | IsKeith n} := by
  ext n; exact isKeithBase_ten n

/-- **The parent's headline, re-derived through the general definition.** The
smallest base-`10` Keith number is `14`. -/
theorem smallest_keithBase10 : IsLeast {n | IsKeithBase 10 n} 14 := by
  rw [keithBase10_setOf_eq]; exact smallest_keith

/- ## Small Keith numbers in other bases -/

/-- `5 = (11)_4` is a Keith number in base `4`: the window runs `1, 1, 2, 3, 5`. -/
theorem keithBase4_five : IsKeithBase 4 5 := by decide

/-- `13 = (11)_12` is a Keith number in base `12`: `1, 1, 2, 3, 5, 8, 13`. -/
theorem keithBase12_thirteen : IsKeithBase 12 13 := by decide

/-- No base-`4` number below `5` is Keith (`4 = (10)_4` overshoots without hitting
itself; `n < 4` has fewer than two base-`4` digits). -/
theorem not_keithBase4_below_five : ∀ n < 5, ¬ IsKeithBase 4 n := by decide

/-- **The smallest base-`4` Keith number is `5`** — the base-`4` analogue of the
parent's `14` in base `10`. -/
theorem smallest_keithBase4 : IsLeast {n : ℕ | IsKeithBase 4 n} 5 := by
  refine ⟨keithBase4_five, ?_⟩
  intro n hn
  by_contra h
  push_neg at h
  exact not_keithBase4_below_five n h hn

end KeithNumberOQ01OQ02
