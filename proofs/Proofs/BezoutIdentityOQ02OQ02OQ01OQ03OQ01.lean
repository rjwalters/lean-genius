import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-
# Sharpening Lamé's Bound to the Golden-Ratio Constant

## Open Question Origin

From `bezout-identity-oq-02-oq-02-oq-01-oq-03`
("Lamé's Theorem: Θ(log) Complexity of the Extended Euclidean Algorithm"),
open question 1:

  "Sharpen to the exact golden-ratio constant ⌊log_φ b⌋ + O(1)."

## What the parent entry already proved

The parent counts division steps with `steps a b` and gives:

* an upper bound `steps a b ≤ 2 log₂ b + 2` (the `O(log)` direction), and
* a worst-case family `steps (fib (n+2)) (fib (n+1)) = n` showing the bound
  is attained (the `Ω(log)` direction).

Together these pin the step count to `Θ(log b)` — but only up to the constant
`2` in front of `log₂`, i.e. the *base* of the logarithm is not yet sharp.

## What this entry adds: the sharp constant

The genuinely sharp statement of Lamé's theorem is a *lower bound on the input*:
to force `n` division steps the smaller argument must be at least the
`(n+2)`-nd Fibonacci number.

* **`lame_fib_lower`** : `n + 1 ≤ steps a b → fib (n + 2) ≤ b`.

This is the converse direction missing from the parent (which only exhibited
*one* worst-case family). Because the Fibonacci numbers grow like `φⁿ`
(`φ = (1+√5)/2` the golden ratio), it converts directly into the exact
golden-ratio constant:

* **`golden_pow_le_fib`** : `φ ^ n ≤ fib (n + 2)`  (a clean real inequality), and
* **`steps_le_logb_golden`** : `steps a b ≤ log_φ b + 1`  for `b ≥ 1`.

The last line is exactly the `⌊log_φ b⌋ + O(1)` bound the open question asked
for: the number of Euclidean division steps never exceeds the base-`φ`
logarithm of the smaller input, plus one. Since the Fibonacci family attains
`steps (fib (n+2)) (fib (n+1)) = n` with `fib (n+1) ≤ φⁿ`, the constant `1`
in front of `log_φ` is optimal — no logarithm to a larger base can bound the
step count.

Zero axioms, zero sorries. The step counter `steps` and its one-step unfolding
lemmas are reproduced here (mirroring the parent entry) so this file verifies
standalone.
-/

namespace BezoutIdentityOQ02OQ02OQ01OQ03OQ01

open scoped goldenRatio

/-
## Part 0: The step counter (mirrored from the parent entry)

`steps a b` counts the division steps of the extended Euclidean algorithm,
whose recursion `(a, b+1) ↦ (b+1, a % (b+1))` it follows exactly.
-/

/-- Number of division steps the extended Euclidean algorithm performs on
    `(a, b)`. Identical to the parent entry's `steps`. -/
def steps : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, b + 1 =>
    have : a % (b + 1) < b + 1 := Nat.mod_lt a (Nat.succ_pos b)
    steps (b + 1) (a % (b + 1)) + 1

@[simp] theorem steps_zero (a : ℕ) : steps a 0 = 0 := by simp [steps]

theorem steps_succ (a b : ℕ) :
    steps a (b + 1) = steps (b + 1) (a % (b + 1)) + 1 := by
  simp [steps]

/-- One-step unfolding for any positive second argument. -/
theorem steps_pos (a b : ℕ) (hb : 0 < b) :
    steps a b = steps b (a % b) + 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact steps_succ a c

/-
## Part I: Lamé's input lower bound (the sharp form)

`steps a b ≥ n + 1` forces `b ≥ fib (n + 2)`. The proof is the natural
two-step induction matching the Fibonacci recurrence: peeling off two Euclidean
steps `a → b → (a % b) → (b % (a % b))` exposes two remainders bounded below by
`fib (n + 1)` and `fib n`, and `b` is at least their sum.
-/

/-- **Lamé's theorem, sharp form.** If the Euclidean algorithm on `(a, b)`
    performs at least `n + 1` division steps, then the smaller input satisfies
    `fib (n + 2) ≤ b`. Equivalently: the worst case (smallest `b` for a given
    step count) is exactly consecutive Fibonacci numbers, matching
    `steps_fib` from the parent entry. -/
theorem lame_fib_lower : ∀ n a b, n + 1 ≤ steps a b → Nat.fib (n + 2) ≤ b := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
    intro a b h
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; rw [steps_zero] at h; omega
    · have hf : Nat.fib (0 + 2) = 1 := by decide
      omega
  | one =>
    intro a b h
    rcases Nat.eq_zero_or_pos b with h0 | h0
    · subst h0; rw [steps_zero] at h; omega
    · rw [steps_pos a b h0] at h
      have hr : 0 < a % b := by
        rcases Nat.eq_zero_or_pos (a % b) with hr0 | hr0
        · rw [hr0, steps_zero] at h; omega
        · exact hr0
      have hlt : a % b < b := Nat.mod_lt a h0
      have hf : Nat.fib (1 + 2) = 2 := by decide
      omega
  | more n ih1 ih2 =>
    intro a b h
    have hb : 0 < b := by
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · subst h0; rw [steps_zero] at h; omega
      · exact h0
    rw [steps_pos a b hb] at h
    set r := a % b with hr_def
    have hrb : r < b := Nat.mod_lt a hb
    have hsteps_br : n + 2 ≤ steps b r := by omega
    have hfr : Nat.fib (n + 3) ≤ r := ih2 b r (by omega)
    have hr_pos : 0 < r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · rw [h0, steps_zero] at hsteps_br; omega
      · exact h0
    rw [steps_pos b r hr_pos] at hsteps_br
    set s := b % r with hs_def
    have hsteps_rs : n + 1 ≤ steps r s := by omega
    have hfs : Nat.fib (n + 2) ≤ s := ih1 r s (by omega)
    have hdm : r * (b / r) + b % r = b := Nat.div_add_mod b r
    have hdivpos : 1 ≤ b / r := (Nat.one_le_div_iff hr_pos).mpr (le_of_lt hrb)
    have hge : r ≤ r * (b / r) := le_mul_of_one_le_right (Nat.zero_le r) hdivpos
    have hfibsum : Nat.fib (n + 2 + 2) = Nat.fib (n + 2) + Nat.fib (n + 3) :=
      Nat.fib_add_two
    omega

/-
## Part II: Fibonacci numbers dominate powers of the golden ratio

`φ ^ n ≤ fib (n + 2)`. A two-step induction using the defining relations
`φ² = φ + 1` and `fib (n+4) = fib (n+2) + fib (n+3)`: the golden ratio and the
Fibonacci sequence satisfy the *same* second-order recurrence, and the base
cases `φ⁰ = 1 = fib 2`, `φ¹ = φ < 2 = fib 3` start the dominance.
-/

/-- **The golden ratio is the growth rate of Fibonacci.** For every `n`,
    `φ ^ n ≤ fib (n + 2)`. This is the bridge that turns the integer worst-case
    bound `lame_fib_lower` into an explicit base-`φ` logarithm. -/
theorem golden_pow_le_fib (n : ℕ) :
    Real.goldenRatio ^ n ≤ (Nat.fib (n + 2) : ℝ) := by
  induction n using Nat.twoStepInduction with
  | zero =>
    have hf : Nat.fib (0 + 2) = 1 := by decide
    rw [hf]; norm_num
  | one =>
    have hf : Nat.fib (1 + 2) = 2 := by decide
    rw [hf, pow_one]; push_cast; linarith [Real.goldenRatio_lt_two]
  | more n ih1 ih2 =>
    have hnat : Nat.fib (n + 2 + 2) = Nat.fib (n + 2) + Nat.fib (n + 3) :=
      Nat.fib_add_two
    have hfib : (Nat.fib (n + 2 + 2) : ℝ)
        = (Nat.fib (n + 2) : ℝ) + (Nat.fib (n + 3) : ℝ) := by exact_mod_cast hnat
    have hexp : Real.goldenRatio ^ (n + 2)
        = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by
      have h1 : Real.goldenRatio ^ (n + 2)
          = Real.goldenRatio ^ n * Real.goldenRatio ^ 2 := by rw [← pow_add]
      rw [h1, Real.goldenRatio_sq]; ring
    rw [hexp, hfib]
    linarith [ih1, ih2]

/-
## Part III: The exact golden-ratio bound (answering the open question)

Combining Parts I and II: `steps a b ≤ log_φ b + 1`. The number of Euclidean
division steps never exceeds the base-`φ` logarithm of the smaller input plus
one — the sharp `⌊log_φ b⌋ + O(1)` form Lamé's theorem is famous for.
-/

/-- **Lamé's theorem with the sharp golden-ratio constant.** For `b ≥ 1` the
    extended Euclidean algorithm performs at most `log_φ b + 1` division steps,
    where `φ = (1 + √5)/2`. Because `fib (n+1) ≤ φⁿ`, the worst-case Fibonacci
    family `steps (fib (n+2)) (fib (n+1)) = n` shows the base `φ` cannot be
    enlarged: this is the exact `⌊log_φ b⌋ + O(1)` characterization. -/
theorem steps_le_logb_golden (a b : ℕ) (hb : 1 ≤ b) :
    (steps a b : ℝ) ≤ Real.logb Real.goldenRatio b + 1 := by
  have hk1 : 1 ≤ steps a b := by
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    rw [steps_succ]; omega
  set k := steps a b with hk
  obtain ⟨n, hn⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hfib : Nat.fib (n + 2) ≤ b := lame_fib_lower n a b (by omega)
  have hgolden : Real.goldenRatio ^ n ≤ (b : ℝ) :=
    le_trans (golden_pow_le_fib n) (by exact_mod_cast hfib)
  have hxpos : (0 : ℝ) < Real.goldenRatio ^ n := pow_pos Real.goldenRatio_pos n
  have hmono : Real.logb Real.goldenRatio (Real.goldenRatio ^ n)
      ≤ Real.logb Real.goldenRatio b :=
    Real.logb_le_logb_of_le Real.one_lt_goldenRatio hxpos hgolden
  have hval : Real.logb Real.goldenRatio (Real.goldenRatio ^ n) = (n : ℝ) := by
    rw [Real.logb_pow, Real.logb_self_eq_one Real.one_lt_goldenRatio, mul_one]
  rw [hval] at hmono
  have hcast : (k : ℝ) = (n : ℝ) + 1 := by rw [hn]; push_cast; ring
  rw [hcast]; linarith [hmono]

end BezoutIdentityOQ02OQ02OQ01OQ03OQ01
