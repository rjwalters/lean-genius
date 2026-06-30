/-
# Geometric series, open question oq-07-oq-01-oq-01:
# The Eulerian polynomial and Frobenius' identity for the geometric moments

The sibling entry `geometric-series-oq-07-oq-01` proves the all-orders moment

  ∑_{n} nᵐ · rⁿ = ∑_{k=0}^{m} S(m,k) · k! · rᵏ / (1 - r)^{k+1}      (|r| < 1)

where `S(m,k) = Nat.stirlingSecond m k`. Clearing the denominator `(1 - r)^{m+1}`
turns the right-hand side into a single polynomial in `r`,

  Nₘ(X) := ∑_{k=0}^{m} S(m,k) · k! · Xᵏ · (1 - X)^{m-k},

the **Eulerian polynomial** in the "geometric" normalisation
`∑_{n≥0} nᵐ Xⁿ = Nₘ(X) / (1 - X)^{m+1}`.  The first few are

  N₀ = 1,   N₁ = X,   N₂ = X + X²,   N₃ = X + 4X² + X³,

whose integer coefficients are the Eulerian numbers `⟨m,k⟩`.

This entry answers the headline open question recorded on `oq-07`, `oq-10` and
`oq-07-oq-01`: *identify the numerator with the Eulerian polynomial.*  We do this
purely algebraically over an arbitrary commutative ring, with **no** appeal to the
analytic moment formula:

* `eulerPoly` is the Eulerian polynomial defined by its classical first-order
  differential recurrence
      `E₀ = 1`,   `E_{m+1} = X(1-X)·E'ₘ + (m+1)·X·Eₘ`.
* `stirlingForm` is the Stirling closed form `Nₘ` above.
* `eulerPoly_eq_stirlingForm` (Frobenius' identity) proves the two agree:
  the differential recurrence and the Stirling sum define the *same* polynomial,
  via the Stirling recurrence `S(m+1,k) = k·S(m,k) + S(m,k-1)`.
* `eval_eulerPoly_one` gives the row sum `Eₘ(1) = m!` (sum of the Eulerian
  numbers of order `m`).

Finally, combining Frobenius with the imported analytic moment closed form
(`GeometricSeriesOQ07OQ01.hasSum_pow_mul_geometric`) yields the compact
generating identity

  ∑_{n} nᵐ · rⁿ = Eₘ(r) / (1 - r)^{m+1}        (|r| < 1)      (`hasSum_pow_mul_geometric_eulerPoly`).

Everything is `0`-axiom (`propext` / `Classical.choice` / `Quot.sound` only) and
`sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01

namespace GeometricSeriesOQ07OQ01OQ01

open Polynomial Finset Nat

variable {R : Type*} [CommRing R]

/-! ## Part 1: the two definitions of the Eulerian polynomial -/

/-- The Eulerian polynomial, defined by its classical first-order differential
recurrence (in the "geometric" normalisation):
`E₀ = 1` and `E_{m+1} = X·(1-X)·E'ₘ + (m+1)·X·Eₘ`. -/
noncomputable def eulerPoly : ℕ → R[X]
  | 0 => 1
  | (m + 1) => X * (1 - X) * derivative (eulerPoly m) + (m + 1 : R[X]) * X * eulerPoly m

@[simp] theorem eulerPoly_zero : (eulerPoly 0 : R[X]) = 1 := rfl

theorem eulerPoly_succ (m : ℕ) :
    (eulerPoly (m + 1) : R[X])
      = X * (1 - X) * derivative (eulerPoly m) + (m + 1 : R[X]) * X * eulerPoly m := rfl

/-- The Stirling closed form `Nₘ(X) = ∑_{k≤m} S(m,k)·k!·Xᵏ·(1-X)^{m-k}` (Frobenius'
right-hand side). -/
noncomputable def stirlingForm (m : ℕ) : R[X] :=
  ∑ k ∈ range (m + 1),
    (C ((stirlingSecond m k * k ! : ℕ) : R)) * X ^ k * (1 - X) ^ (m - k)

/-! ## Part 2: Frobenius' identity `eulerPoly = stirlingForm` -/

/-- The key per-term computation: multiplying the derivative of a single
Stirling-form summand `C a · Xᵏ · (1-X)ᵖ` by `X·(1-X)` produces clean powers
`Xᵏ` and `X^{k+1}` (no `X^{k-1}` boundary term), valid for all `k, p`. -/
theorem key_term (a : R) (k p : ℕ) :
    X * (1 - X) * derivative (C a * X ^ k * (1 - X) ^ p)
      = C a * C ((k : ℕ) : R) * X ^ k * (1 - X) ^ (p + 1)
        - C a * C ((p : ℕ) : R) * X ^ (k + 1) * (1 - X) ^ p := by
  have hd : derivative ((1 - X : R[X]) ^ p) = - (C ((p : ℕ) : R) * (1 - X) ^ (p - 1)) := by
    have h1 : (1 - X : R[X]) = -(X - C 1) := by rw [C_1]; ring
    rw [h1, derivative_pow, derivative_neg, derivative_X_sub_C, ← h1]
    ring
  rw [derivative_mul, derivative_mul, derivative_C, hd, derivative_X_pow]
  cases k with
  | zero =>
    cases p with
    | zero => simp
    | succ q => simp only [Nat.succ_sub_one, Nat.cast_zero, map_zero]; ring
  | succ j =>
    cases p with
    | zero => simp only [Nat.succ_sub_one, Nat.cast_zero, map_zero]; ring
    | succ q => simp only [Nat.succ_sub_one]; ring

/-- The Stirling closed form satisfies the same differential recurrence as the
Eulerian polynomial.  This is the algebraic heart of Frobenius' identity, proved
from the Stirling recurrence `S(m+1,k+1) = (k+1)·S(m,k+1) + S(m,k)` together with
the vanishing boundary values `S(m,m+1) = 0` and `S(m+1,0) = 0`. -/
theorem stirlingForm_succ (m : ℕ) :
    (stirlingForm (m + 1) : R[X])
      = X * (1 - X) * derivative (stirlingForm m) + (m + 1 : R[X]) * X * stirlingForm m := by
  -- `Qterm`, `Rterm`: the two halves of the canonical paired summand.
  set Qterm : ℕ → R[X] := fun k =>
    C ((stirlingSecond m k * k ! : ℕ) : R) * C ((k : ℕ) : R) * X ^ k * (1 - X) ^ (m + 1 - k)
    with hQ
  set Rterm : ℕ → R[X] := fun k =>
    C ((stirlingSecond m k * k ! : ℕ) : R) * C (((k + 1 : ℕ)) : R) * X ^ (k + 1) * (1 - X) ^ (m - k)
    with hR
  set uterm : ℕ → R[X] := fun k =>
    C (((k + 1) * stirlingSecond m (k + 1) * (k + 1)! : ℕ) : R) * X ^ (k + 1) * (1 - X) ^ (m - k)
    with hu
  -- STEP 1 : the right-hand side equals `∑ (Qterm k + Rterm k)`.
  have hRHS :
      X * (1 - X) * derivative (stirlingForm m) + (m + 1 : R[X]) * X * stirlingForm m
        = ∑ k ∈ range (m + 1), (Qterm k + Rterm k) := by
    rw [stirlingForm, derivative_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
    rw [key_term]
    have e1 : (m - k) + 1 = m + 1 - k := by omega
    -- `↑(m+1) = ↑(m-k) + ↑(k+1)` as polynomials, so `↑(m+1) - ↑(m-k) = ↑(k+1)`
    have hsplit : ((m : R[X]) + 1) = C (((m - k : ℕ)) : R) + C (((k + 1 : ℕ)) : R) := by
      rw [← map_add, ← Nat.cast_add, show m - k + (k + 1) = m + 1 from by omega, map_natCast]
      push_cast
      ring
    simp only [hQ, hR]
    rw [e1, hsplit]
    ring
  -- STEP 2 : `stirlingForm (m+1)` equals the same paired sum.
  have hf0 : (C ((stirlingSecond (m + 1) 0 * 0 ! : ℕ) : R) * X ^ 0 * (1 - X) ^ (m + 1 - 0))
      = 0 := by simp [stirlingSecond_succ_zero]
  have hsplitf : ∀ k ∈ range (m + 1),
      C ((stirlingSecond (m + 1) (k + 1) * (k + 1)! : ℕ) : R) * X ^ (k + 1)
          * (1 - X) ^ (m + 1 - (k + 1))
        = uterm k + Rterm k := by
    intro k _
    have e2 : m + 1 - (k + 1) = m - k := by omega
    have hrec : stirlingSecond (m + 1) (k + 1)
        = (k + 1) * stirlingSecond m (k + 1) + stirlingSecond m k := stirlingSecond_succ_succ m k
    simp only [hu, hR]
    rw [e2, hrec]
    simp only [map_natCast]
    push_cast [Nat.factorial_succ]
    ring
  have hLHS : (stirlingForm (m + 1) : R[X])
      = (∑ k ∈ range (m + 1), uterm k) + ∑ k ∈ range (m + 1), Rterm k := by
    rw [stirlingForm, Finset.sum_range_succ', hf0, add_zero]
    rw [Finset.sum_congr rfl hsplitf, Finset.sum_add_distrib]
  -- STEP 3 : `∑ uterm = ∑ Qterm`, via reindexing and the vanishing top term.
  have hum : uterm m = 0 := by
    simp only [hu]
    rw [stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m)]
    simp
  have hQ0 : Qterm 0 = 0 := by simp [hQ]
  have huQ : (∑ k ∈ range (m + 1), uterm k) = ∑ k ∈ range (m + 1), Qterm k := by
    rw [Finset.sum_range_succ, hum, add_zero]
    rw [Finset.sum_range_succ', hQ0, add_zero]
    apply Finset.sum_congr rfl
    intro k _
    have e3 : m + 1 - (k + 1) = m - k := by omega
    simp only [hu, hQ]
    rw [e3]
    simp only [map_natCast]
    push_cast
    ring
  -- assemble
  rw [hLHS, huQ, ← Finset.sum_add_distrib, hRHS]

/-- **Frobenius' identity.**  The Eulerian polynomial (differential recurrence)
equals the Stirling closed form. -/
theorem eulerPoly_eq_stirlingForm (m : ℕ) :
    (eulerPoly m : R[X]) = stirlingForm m := by
  induction m with
  | zero => simp [stirlingForm, stirlingSecond_zero]
  | succ n ih =>
      rw [eulerPoly_succ, ih, stirlingForm_succ]

/-! ## Part 3: low-order values and the row sum -/

theorem eulerPoly_one : (eulerPoly 1 : R[X]) = X := by
  rw [eulerPoly_succ]; simp

theorem eulerPoly_two : (eulerPoly 2 : R[X]) = X + X ^ 2 := by
  rw [eulerPoly_succ, eulerPoly_one]
  simp only [derivative_X]
  push_cast
  ring

theorem eulerPoly_three : (eulerPoly 3 : R[X]) = X + 4 * X ^ 2 + X ^ 3 := by
  rw [eulerPoly_succ, eulerPoly_two]
  simp only [derivative_add, derivative_X, derivative_X_pow, map_natCast]
  push_cast
  ring

/-- The row sum of the Eulerian numbers of order `m` is `m!`: `Eₘ(1) = m!`. -/
theorem eval_eulerPoly_one (m : ℕ) : (eulerPoly m : R[X]).eval 1 = (m ! : R) := by
  rw [eulerPoly_eq_stirlingForm, stirlingForm, eval_finset_sum]
  rw [Finset.sum_eq_single m]
  · simp [stirlingSecond_self]
  · intro k hk hkm
    have hkm' : k < m := by
      have : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
      omega
    have : (1 : R) - 1 = 0 := by ring
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_one, this]
    rw [zero_pow (by omega : m - k ≠ 0)]
    ring
  · intro hm
    simp at hm

/-! ## Part 4: the moment generating identity over `ℝ` -/

/-- **The geometric moment closed form via the Eulerian polynomial.**  Combining
Frobenius' identity with the analytic moment formula
`GeometricSeriesOQ07OQ01.hasSum_pow_mul_geometric` gives the compact statement

  ∑_{n} nᵐ · rⁿ = Eₘ(r) / (1 - r)^{m+1}      (|r| < 1). -/
theorem hasSum_pow_mul_geometric_eulerPoly (m : ℕ) {r : ℝ} (hr : |r| < 1) :
    HasSum (fun n : ℕ => (n : ℝ) ^ m * r ^ n)
      ((eulerPoly m : ℝ[X]).eval r / (1 - r) ^ (m + 1)) := by
  have hr1 : (1 : ℝ) - r ≠ 0 := by
    have : r < 1 := (abs_lt.mp hr).2
    linarith
  have hbase := GeometricSeriesOQ07OQ01.hasSum_pow_mul_geometric m hr
  -- rewrite the imported sum value to `Eₘ(r)/(1-r)^{m+1}`
  have hval :
      (∑ k ∈ range (m + 1),
          (stirlingSecond m k : ℝ) * k.factorial * r ^ k / (1 - r) ^ (k + 1))
        = (eulerPoly m : ℝ[X]).eval r / (1 - r) ^ (m + 1) := by
    rw [eulerPoly_eq_stirlingForm, stirlingForm, eval_finset_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hkm : k ≤ m := by simpa [Nat.lt_succ_iff] using hk
    rw [eval_mul, eval_mul, eval_pow, eval_pow, eval_C, eval_X, eval_sub, eval_X, eval_one]
    push_cast
    rw [div_eq_div_iff (by positivity) (by positivity)]
    rw [show m + 1 = (k + 1) + (m - k) by omega, pow_add]
    ring
  rw [← hval]
  exact hbase

end GeometricSeriesOQ07OQ01OQ01
