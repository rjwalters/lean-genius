/-
# The General Falling-Factorial Moment of the Binomial Coefficients (OQ-03-OQ-01-OQ-01)

Research Question (follow-up to OQ-03-OQ-01 "Combinatorial Moments of the
Binomial Coefficients").  The parent computed the first three *unweighted*
moments one at a time,

    Σ k·C(n,k)      = n·2ⁿ⁻¹,
    Σ k(k-1)·C(n,k) = n(n-1)·2ⁿ⁻²,
    Σ k²·C(n,k)     = n(n+1)·2ⁿ⁻²,

each via the absorption identity `(k+1)·C(n+1,k+1) = (n+1)·C(n,k)`.  Is there a
*single* closed form that subsumes all of the factorial moments at once?

Answer.  Yes.  Writing `k^(r) = k(k-1)⋯(k-r+1) = Nat.descFactorial k r` for the
falling factorial, the general identity is

    Σ_{k=0}^{n} k^(r) · C(n,k) = n^(r) · 2ⁿ⁻ʳ            (for all n, r : ℕ)

— the **r-th falling-factorial moment** of the binomial coefficients.  It is the
combinatorial shadow of differentiating `(1+x)ⁿ = Σ C(n,k)xᵏ` exactly `r` times
and setting `x = 1`: the r-th derivative of `(1+x)ⁿ` is `n^(r)(1+x)ⁿ⁻ʳ`, worth
`n^(r)·2ⁿ⁻ʳ` at `x = 1`, while term-by-term it produces `Σ k^(r)·C(n,k)·xᵏ⁻ʳ`.
Specialising `r = 0, 1, 2` recovers `Σ C = 2ⁿ` (Mathlib's `Nat.sum_range_choose`)
and the parent's first two factorial moments; none of the positive-order cases is
in Mathlib.

The proof is a clean induction on `r`.  The single absorption step lifts to the
recurrence

    S(m+1, r+1) = (m+1) · S(m, r),     S(n, 0) = 2ⁿ,

via `Nat.succ_descFactorial_succ : (k+1)^(r+1) = (k+1)·k^(r)` together with the
parent's `absorption`.  Iterating the recurrence is exactly the unfolding of
`n^(r) = n·(n-1)⋯` through `descFactorial`, so the falling factorial appears on
the right with no extra bookkeeping.  Everything stays inside ℕ; the truncated
subtraction in `2ⁿ⁻ʳ` is harmless because `n^(r) = 0` whenever `r > n`, killing
the right-hand side exactly where the left-hand side vanishes too.

Tags: combinatorics, binomial-coefficients, moments, falling-factorial,
absorption, generating-functions
-/

import Mathlib
import Proofs.BinomialTheoremOQ03

open Finset BigOperators

namespace BinomialTheoremOQ03OQ01OQ01

/-! ## Part I: The absorption step lifted to falling-factorial sums -/

/-- **Falling-factorial absorption step.**  Peeling the vanishing `k = 0` term,
reindexing `k ↦ k+1`, and applying the single absorption identity
`(k+1)·C(m+1,k+1) = (m+1)·C(m,k)` term-by-term turns the `(r+1)`-th
falling-factorial sum over `range (m+2)` into `(m+1)` times the `r`-th
falling-factorial sum over `range (m+1)`.  This is the engine of the induction:
each differentiation of the generating function drops the upper index by one and
pulls out a leading factor of `m+1`. -/
theorem sum_descFactorial_mul_choose_step (m r : ℕ) :
    ∑ k ∈ range (m + 2), k.descFactorial (r + 1) * (m + 1).choose k
      = (m + 1) * ∑ k ∈ range (m + 1), k.descFactorial r * m.choose k := by
  rw [Finset.sum_range_succ']
  -- the peeled `k = 0` term is `0^(r+1) · C(m+1,0) = 0`
  rw [Nat.zero_descFactorial_succ, Nat.zero_mul, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  -- (k+1)^(r+1) · C(m+1, k+1) = (m+1) · (k^(r) · C(m,k))
  rw [Nat.succ_descFactorial_succ]
  have h := BinomialTheoremOQ03.absorption m k
  calc (k + 1) * k.descFactorial r * (m + 1).choose (k + 1)
      = k.descFactorial r * ((k + 1) * (m + 1).choose (k + 1)) := by ring
    _ = k.descFactorial r * ((m + 1) * m.choose k) := by rw [h]
    _ = (m + 1) * (k.descFactorial r * m.choose k) := by ring

/-! ## Part II: The general falling-factorial moment -/

/-- **General falling-factorial moment.**  For every `n r : ℕ`,
`Σ_{k=0}^{n} k^(r) · C(n,k) = n^(r) · 2ⁿ⁻ʳ`, where `k^(r) = Nat.descFactorial k r`
is the falling factorial.  Proved by induction on `r`: the base case `r = 0` is
the zeroth moment `Σ C(n,k) = 2ⁿ`, and the step is the recurrence
`sum_descFactorial_mul_choose_step` combined with
`Nat.succ_descFactorial_succ`.  Holds unconditionally — when `r > n` both sides
are `0`. -/
theorem sum_descFactorial_mul_choose (n r : ℕ) :
    ∑ k ∈ range (n + 1), k.descFactorial r * n.choose k
      = n.descFactorial r * 2 ^ (n - r) := by
  induction r generalizing n with
  | zero =>
    simp only [Nat.descFactorial_zero, one_mul, Nat.sub_zero]
    exact Nat.sum_range_choose n
  | succ r ih =>
    cases n with
    | zero => simp
    | succ m =>
      rw [sum_descFactorial_mul_choose_step m r, ih m,
        Nat.succ_descFactorial_succ, Nat.succ_sub_succ]
      ring

/-! ## Part III: The parent's moments as special cases (subsumption) -/

/-- **r = 1 (first moment).**  `Σ_{k=0}^{n} k · C(n,k) = n · 2ⁿ⁻¹`.  The parent's
`sum_id_mul_choose`, now a one-line specialisation of the general formula at
`r = 1` (using `Nat.descFactorial_one : k^(1) = k`). -/
theorem sum_id_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * n.choose k = n * 2 ^ (n - 1) := by
  have h := sum_descFactorial_mul_choose n 1
  simpa [Nat.descFactorial_one] using h

/-- `descFactorial k 2 = k·(k-1)` — the order-2 falling factorial written out. -/
theorem descFactorial_two (k : ℕ) : k.descFactorial 2 = k * (k - 1) := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_one]
  ring

/-- **r = 2 (second factorial moment).**  `Σ_{k=0}^{n} k(k-1) · C(n,k) =
n(n-1) · 2ⁿ⁻²`.  The parent's `sum_descFactorial_mul_choose`, recovered from the
general formula at `r = 2`. -/
theorem sum_descFactorial2_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * (k - 1) * n.choose k = n * (n - 1) * 2 ^ (n - 2) := by
  have hgen := sum_descFactorial_mul_choose n 2
  rw [descFactorial_two n] at hgen
  rw [← hgen]
  apply Finset.sum_congr rfl
  intro k _
  rw [descFactorial_two k]

/-! ## Part IV: A genuinely new case — the third factorial moment -/

/-- `descFactorial k 3 = k·(k-1)·(k-2)` — the order-3 falling factorial. -/
theorem descFactorial_three (k : ℕ) : k.descFactorial 3 = k * (k - 1) * (k - 2) := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_succ,
    Nat.descFactorial_one]
  ring

/-- **r = 3 (third factorial moment).**  `Σ_{k=0}^{n} k(k-1)(k-2) · C(n,k) =
n(n-1)(n-2) · 2ⁿ⁻³`.  This case is **beyond** what the parent proved and is a
free instance of the general formula at `r = 3`, illustrating that one single
result delivers every factorial moment at once. -/
theorem sum_descFactorial3_mul_choose (n : ℕ) :
    ∑ k ∈ range (n + 1), k * (k - 1) * (k - 2) * n.choose k
      = n * (n - 1) * (n - 2) * 2 ^ (n - 3) := by
  have hgen := sum_descFactorial_mul_choose n 3
  rw [descFactorial_three n] at hgen
  rw [← hgen]
  apply Finset.sum_congr rfl
  intro k _
  rw [descFactorial_three k]

/-! ## Part V: Sanity checks -/

-- General formula at small parameters (note `descFactorial` is computable).
example : ∑ k ∈ range 5, k.descFactorial 1 * (4).choose k = (4).descFactorial 1 * 2 ^ 3 := by
  decide
example : ∑ k ∈ range 6, k.descFactorial 2 * (5).choose k = (5).descFactorial 2 * 2 ^ 3 := by
  decide
example : ∑ k ∈ range 8, k.descFactorial 3 * (7).choose k = (7).descFactorial 3 * 2 ^ 4 := by
  decide
-- The `r > n` degenerate case: both sides vanish.
example : ∑ k ∈ range 4, k.descFactorial 5 * (3).choose k = (3).descFactorial 5 * 2 ^ (3 - 5) := by
  decide

end BinomialTheoremOQ03OQ01OQ01
