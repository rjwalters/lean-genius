/-
The signed shallow-diagonal sum of Pascal's triangle is 6-periodic (OQ-01-OQ-01-OQ-02)

Parent entry `combinations-formula-oq-01-oq-01` ("The Fibonacci Shallow-Diagonal Sum
of Pascal's Triangle") proves the *unsigned* shallow-diagonal identity

  `∑_{j} C(n−j, j) = F(n+1)`

and leaves open what happens to the **signed** (alternating) shallow diagonal.

This file answers it.  Putting an alternating sign on the same shallow diagonal of
Pascal's triangle collapses the Fibonacci growth into a *bounded, purely periodic*
sequence of period 6:

  `S n := ∑_{j} (-1)^j · C(n−j, j)`  takes the repeating values  `1, 1, 0, -1, -1, 0`.

Where the unsigned diagonal satisfies the Fibonacci recurrence `a(n) = a(n-1)+a(n-2)`
(roots `(1±√5)/2`, exponential growth), the sign flips the recurrence to

  `S(n+2) = S(n+1) − S(n)`,

whose characteristic roots are the primitive sixth roots of unity `e^{±iπ/3}` — hence
the antiperiod-3 relation `S(n+3) = −S(n)` and the period-6 relation `S(n+6) = S(n)`.

Main results:
* `S_rec`          — the sign-flipped Fibonacci recurrence `S(n+2) = S(n+1) − S(n)`.
* `S_antiperiod`   — `S(n+3) = −S(n)` (period doubles to an antiperiod of 3).
* `S_period`       — `S(n+6) = S(n)`.
* `S_periodic`     — packaged as `Function.Periodic S 6`.
* `S_closed_form`  — the explicit value of `S n` as a function of `n % 6`.

Everything is axiom-free.  Contrast with the parent's exponentially growing
unsigned diagonal; this is the bounded period-6 companion.
-/

import Mathlib

namespace CombinationsFormulaOQ01OQ01OQ02

open Finset

/-- **Signed shallow-diagonal sum.** `S n = ∑_{j} (-1)^j · C(n−j, j)`, summing the
shallow diagonal of Pascal's triangle with alternating signs.  (Terms with `j > n−j`
vanish since `C(n−j, j) = 0` there, so the `range (n+1)` upper bound is harmless.) -/
def S (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℤ) ^ j * (Nat.choose (n - j) j : ℤ)

/-! ## Base values -/

lemma S_zero : S 0 = 1 := by
  simp [S]

lemma S_one : S 1 = 1 := by
  simp [S, Finset.sum_range_succ]

lemma S_two : S 2 = 0 := by
  simp [S, Finset.sum_range_succ]

lemma S_three : S 3 = -1 := by
  norm_num [S, Finset.sum_range_succ]

lemma S_four : S 4 = -1 := by
  norm_num [S, Finset.sum_range_succ]

lemma S_five : S 5 = 0 := by
  norm_num [S, Finset.sum_range_succ]

/-! ## The sign-flipped Fibonacci recurrence -/

/-- **Recurrence.** Alternating the signs of the shallow diagonal turns the Fibonacci
recurrence into `S(n+2) = S(n+1) − S(n)`.  Proof by the Pascal rule
`C(m+1, k+1) = C(m, k) + C(m, k+1)` applied termwise, with the boundary terms
vanishing because the relevant binomial coefficients are zero. -/
lemma S_rec (n : ℕ) : S (n + 2) = S (n + 1) - S n := by
  -- Pointwise Pascal identity.  For `i ≤ n` it is the Pascal rule
  -- `C((n-i)+1, i+1) = C(n-i, i) + C(n-i, i+1)`; past the boundary both sides vanish.
  have P : ∀ i : ℕ, (Nat.choose (n + 1 - i) (i + 1) : ℤ)
              = (Nat.choose (n - i) i : ℤ) + (Nat.choose (n - i) (i + 1) : ℤ) := by
    intro i
    rcases le_or_gt i n with hi | hi
    · have e : n + 1 - i = (n - i) + 1 := by omega
      rw [e, Nat.choose_succ_succ']; push_cast; ring
    · have e1 : n + 1 - i = 0 := by omega
      have e2 : n - i = 0 := by omega
      have a1 : Nat.choose 0 (i + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      have a2 : Nat.choose 0 i = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [e1, e2, a1, a2]; simp
  -- Peel the `j = 0` term:  `S m = (∑_{i<m} (-1)^{i+1} C(m-1-i, i+1)) + 1`.
  have peel : ∀ m : ℕ,
      S m = (∑ i ∈ Finset.range m,
                (-1 : ℤ) ^ (i + 1) * (Nat.choose (m - 1 - i) (i + 1) : ℤ)) + 1 := by
    intro m
    rw [S, Finset.sum_range_succ' (fun j => (-1 : ℤ) ^ j * (Nat.choose (m - j) j : ℤ)) m]
    congr 1
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      dsimp only
      rw [show m - (i + 1) = m - 1 - i from by omega]
    · simp
  rw [peel (n + 2)]
  -- Apply Pascal termwise and split into two sums.
  have split :
      (∑ i ∈ Finset.range (n + 2),
          (-1 : ℤ) ^ (i + 1) * (Nat.choose (n + 2 - 1 - i) (i + 1) : ℤ))
        = (-(∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i * (Nat.choose (n - i) i : ℤ)))
          + (∑ i ∈ Finset.range (n + 2),
              (-1 : ℤ) ^ (i + 1) * (Nat.choose (n - i) (i + 1) : ℤ)) := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show n + 2 - 1 - i = n + 1 - i from by omega, P i, pow_succ]
    ring
  rw [split]
  -- The first sum is `S n` (its top term vanishes); the second is `S (n+1) - 1`.
  have A : (∑ i ∈ Finset.range (n + 2), (-1 : ℤ) ^ i * (Nat.choose (n - i) i : ℤ)) = S n := by
    rw [Finset.sum_range_succ]
    have hz : (Nat.choose (n - (n + 1)) (n + 1) : ℤ) = 0 := by
      rw [show n - (n + 1) = 0 from by omega, Nat.choose_eq_zero_of_lt (by omega : 0 < n + 1)]
      simp
    rw [hz, S]; simp
  have B : (∑ i ∈ Finset.range (n + 2),
              (-1 : ℤ) ^ (i + 1) * (Nat.choose (n - i) (i + 1) : ℤ)) = S (n + 1) - 1 := by
    rw [Finset.sum_range_succ]
    have hz : (Nat.choose (n - (n + 1)) (n + 1 + 1) : ℤ) = 0 := by
      rw [show n - (n + 1) = 0 from by omega,
          Nat.choose_eq_zero_of_lt (by omega : 0 < n + 1 + 1)]
      simp
    simp only [hz, mul_zero, add_zero]
    rw [peel (n + 1), add_sub_cancel_right]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [show n + 1 - 1 - i = n - i from by omega]
  rw [A, B]; ring

/-! ## Periodicity -/

/-- **Antiperiod 3.** `S(n+3) = −S(n)`, obtained by applying the recurrence twice. -/
lemma S_antiperiod (n : ℕ) : S (n + 3) = - S n := by
  have h1 : S (n + 2) = S (n + 1) - S n := S_rec n
  have h2 : S (n + 3) = S (n + 2) - S (n + 1) := S_rec (n + 1)
  linarith

/-- **Period 6.** `S(n+6) = S(n)`, from the antiperiod relation applied twice. -/
lemma S_period (n : ℕ) : S (n + 6) = S n := by
  have h1 : S (n + 6) = - S (n + 3) := S_antiperiod (n + 3)
  have h2 : S (n + 3) = - S n := S_antiperiod n
  rw [h1, h2, neg_neg]

/-- **Periodicity, packaged.** `S` is periodic with period `6`. -/
theorem S_periodic : Function.Periodic S 6 := fun n => S_period n

/-- Helper: shifting the argument by any multiple of `6` leaves `S` unchanged. -/
lemma S_add_mul_six (a k : ℕ) : S (a + 6 * k) = S a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a + 6 * (k + 1) = (a + 6 * k) + 6 := by ring
    rw [e, S_period, ih]

/-- `S n` depends only on `n % 6`. -/
theorem S_eq_mod (n : ℕ) : S n = S (n % 6) := by
  conv_lhs => rw [← Nat.mod_add_div n 6]
  rw [S_add_mul_six]

/-- **Closed form.** The signed shallow diagonal cycles through `1, 1, 0, -1, -1, 0`
according to `n % 6`. -/
theorem S_closed_form (n : ℕ) :
    S n = if n % 6 = 0 then 1
          else if n % 6 = 1 then 1
          else if n % 6 = 2 then 0
          else if n % 6 = 3 then -1
          else if n % 6 = 4 then -1
          else 0 := by
  rw [S_eq_mod]
  have h : n % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases (n % 6) <;>
    simp [S_zero, S_one, S_two, S_three, S_four, S_five]

end CombinationsFormulaOQ01OQ01OQ02
