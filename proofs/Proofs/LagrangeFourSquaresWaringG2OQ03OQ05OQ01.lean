import Mathlib
import Proofs.LagrangeFourSquaresWaringG2OQ03OQ05

/-!
# The non-three-square density error is one-sided and genuinely unbounded

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-05-oq-01`)**, a direct sequel to
`oq-03-oq-05` (*"the natural density of the non-three-square integers is `1/6`"*).

Recall the *excluded family* `E = { 4^a (8b+7) }` of integers that are **not** sums of three
squares (Legendre), and the counting function `excludedCount N = #{ n < N : n ∈ E }`.  The
`oq-03-oq-05` entry proved `excludedCount N / N → 1/6` together with a two-sided logarithmic
error bound `|6·excludedCount N − N| ≤ 6·(log₂ N + 1)`, and asked:

> *Is the oscillation `6·excludedCount N − N` actually `O(1)` along subsequences, or is it
> genuinely unbounded?  What is the true order?*

This file settles the dichotomy completely.

## What is new here

The whole analysis collapses onto a single residue computation.  Writing
`E(N) := 6·excludedCount N − N`, the `oq-03-oq-05` recursion
`excludedCount N = N/8 + excludedCount ⌈N/4⌉` telescopes to

  `E(N) = E(⌈N/4⌉) + δ(N)`,   where  `δ(N) = ⌊(N mod 8 + 3)/4⌋ − (N mod 8)`

depends **only on `N mod 8`**, taking the eight values `0, 0, −1, −2, −3, −3, −4, −5`.  Two
consequences follow.

* **One-sided sharpness** (`six_excludedCount_le`, `excludedCount_le_div_six`):
  because every `δ` value is `≤ 0`,
  `6·excludedCount N ≤ N`  for **all** `N`,  i.e.  `excludedCount N ≤ ⌊N/6⌋`.
  The density `1/6` is therefore approached **strictly from below** — never overshot.  This
  is strictly stronger than the two-sided bound, whose upper half was `+6(log₂N+1)`.

* **Genuine unboundedness** (`error_unbounded`), via an explicit extremal family.  Let
  `a 0 = 6`, `a (k+1) = 4·a k − 2` (closed form `a k = (4^{k+2}+2)/3`).  Every `a k ≡ 6
  (mod 8)`, the descent `⌈(a (k+1))/4⌉ = a k` stays on the family, and each step contributes
  `δ = −4`.  Hence

  `6·excludedCount (a k) = a k − (4k + 6)`   (`excludedCount_a`),

  so the error `N − 6·excludedCount N` is **unbounded above**: it equals `4k+6` along the
  family while `a k` grows like `4^k`.  Thus the oscillation is **not** `O(1)`; its true order
  is `Θ(log N)`, matching the `oq-03-oq-05` upper bound up to a constant.

Combining the two: `0 ≤ N − 6·excludedCount N` always, with the gap reaching every height.
All proofs are axiom-free and reuse the merged `oq-03-oq-05` recursion verbatim.
-/

open LagrangeFourSquaresWaringG2OQ03OQ05

namespace LagrangeFourSquaresWaringG2OQ03OQ05OQ01

/-! ## One-sided sharpness: `6·excludedCount N ≤ N` for all `N` -/

/-- **The density `1/6` is approached strictly from below.**  Since each descent step changes
`6·excludedCount − id` by `δ(N) = ⌊(N mod 8 + 3)/4⌋ − (N mod 8) ≤ 0`, the running total never
becomes positive: `6·excludedCount N ≤ N` for every `N`. -/
theorem six_excludedCount_le (N : ℕ) : 6 * excludedCount N ≤ N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases lt_or_ge N 8 with hN | hN
    · rw [excludedCount_zero_of_le (by omega)]; omega
    · set M := (N + 3) / 4 with hM
      have hMlt : M < N := by omega
      have hrec : excludedCount N = N / 8 + excludedCount M := excludedCount_rec N
      have ihM := ih M hMlt
      have e8 : 8 * (N / 8) + N % 8 = N := Nat.div_add_mod N 8
      have e8' : N % 8 < 8 := Nat.mod_lt N (by norm_num)
      have e4 : 4 * M + (N + 3) % 4 = N + 3 := by rw [hM]; exact Nat.div_add_mod (N + 3) 4
      have e4' : (N + 3) % 4 < 4 := Nat.mod_lt _ (by norm_num)
      rw [hrec]
      omega

/-- Equivalent floor form: `excludedCount N ≤ ⌊N/6⌋`. -/
theorem excludedCount_le_div_six (N : ℕ) : excludedCount N ≤ N / 6 := by
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  have := six_excludedCount_le N
  omega

/-! ## The extremal family `a k = (4^{k+2}+2)/3` -/

/-- The worst-case family for the descent: `a 0 = 6`, `a (k+1) = 4·a k − 2`.  Closed form
`a k = (4^{k+2}+2)/3`; every member is `≡ 6 (mod 8)` and each descent step costs `δ = −4`. -/
def a : ℕ → ℕ
  | 0 => 6
  | (k + 1) => 4 * a k - 2

/-- Every member of the family is `≡ 6 (mod 8)` — the residue with the largest negative `δ`
that admits an infinite descent (a residue `7` cannot chain to another `7`). -/
theorem a_mod8 (k : ℕ) : a k % 8 = 6 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : a (k + 1) = 4 * a k - 2 := rfl
    omega

/-- The family is bounded below by `6` (hence the `ℕ` subtraction in the recurrence is safe). -/
theorem a_ge (k : ℕ) : 6 ≤ a k := by have := a_mod8 k; omega

/-- **The descent stays on the family:** `⌈a (k+1) / 4⌉ = a k`, i.e. `(a (k+1) + 3) / 4 = a k`.
-/
theorem a_step (k : ℕ) : (a (k + 1) + 3) / 4 = a k := by
  have h : a (k + 1) = 4 * a k - 2 := rfl
  have hge := a_ge k
  omega

/-! ## The exact error along the family -/

/-- **The error is exactly `4k+6` along the extremal family:**
`6·excludedCount (a k) = a k − (4k + 6)`.  Proved by induction using the `oq-03-oq-05`
recursion and `a_step`; each step adds `δ = −4`. -/
theorem excludedCount_a (k : ℕ) :
    (6 : ℤ) * excludedCount (a k) = (a k : ℤ) - (4 * (k : ℤ) + 6) := by
  induction k with
  | zero =>
    have h6 : excludedCount (a 0) = 0 := excludedCount_zero_of_le (by decide)
    rw [h6]
    norm_num [a]
  | succ k ih =>
    have hrec : excludedCount (a (k + 1))
        = a (k + 1) / 8 + excludedCount ((a (k + 1) + 3) / 4) := excludedCount_rec (a (k + 1))
    rw [a_step k] at hrec
    have hmod : a k % 8 = 6 := a_mod8 k
    have hak1 : a (k + 1) = 4 * a k - 2 := rfl
    have hge := a_ge k
    have hdiv : 8 * (a (k + 1) / 8) + a (k + 1) % 8 = a (k + 1) := Nat.div_add_mod _ 8
    have hak1mod : a (k + 1) % 8 = 6 := a_mod8 (k + 1)
    -- the per-step value of the floor `a(k+1)/8`, in `ℤ`
    have hkeyZ : (6 : ℤ) * ((a (k + 1) / 8 : ℕ) : ℤ) = 3 * (a k : ℤ) - 6 := by omega
    have hak1Z : (a (k + 1) : ℤ) = 4 * (a k : ℤ) - 2 := by omega
    have hsum : (6 : ℤ) * excludedCount (a (k + 1))
        = 6 * ((a (k + 1) / 8 : ℕ) : ℤ) + 6 * excludedCount (a k) := by
      rw [hrec]; push_cast; ring
    rw [hsum, ih]
    push_cast
    linarith [hkeyZ, hak1Z]

/-- Restated: the error `N − 6·excludedCount N` equals `4k+6` at `N = a k`. -/
theorem error_eq (k : ℕ) :
    (a k : ℤ) - 6 * excludedCount (a k) = 4 * (k : ℤ) + 6 := by
  have := excludedCount_a k; linarith

/-! ## The dichotomy, settled -/

/-- **The oscillation is genuinely unbounded.**  For every target `C` there is an `N` with
`C ≤ N − 6·excludedCount N`.  Concretely `N = a ⌈C⌉` works, since the error there is `4·C+6`.
Together with `six_excludedCount_le` (which gives `0 ≤ N − 6·excludedCount N` always), this
shows the error is `≥ 0` everywhere and reaches every height — so it is **not** `O(1)`; its
order is `Θ(log N)`. -/
theorem error_unbounded (C : ℤ) :
    ∃ N : ℕ, C ≤ (N : ℤ) - 6 * excludedCount N := by
  refine ⟨a C.toNat, ?_⟩
  rw [error_eq]
  have h1 : C ≤ (C.toNat : ℤ) := by omega
  have h2 : (0 : ℤ) ≤ (C.toNat : ℤ) := Int.natCast_nonneg _
  linarith

/-- **The full picture in one statement:** `0 ≤ N − 6·excludedCount N` for all `N`, and the
quantity is unbounded above.  Hence the `oq-03-oq-05` oscillation is one-sided and `Θ(log N)`,
never `O(1)`. -/
theorem density_error_one_sided_and_unbounded :
    (∀ N : ℕ, 0 ≤ (N : ℤ) - 6 * excludedCount N) ∧
      (∀ C : ℤ, ∃ N : ℕ, C ≤ (N : ℤ) - 6 * excludedCount N) := by
  refine ⟨fun N => ?_, error_unbounded⟩
  have := six_excludedCount_le N
  have : (6 : ℤ) * excludedCount N ≤ N := by exact_mod_cast this
  linarith

end LagrangeFourSquaresWaringG2OQ03OQ05OQ01
