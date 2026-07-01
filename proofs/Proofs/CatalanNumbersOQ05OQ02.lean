import Mathlib

/-!
# The Catalan triangle: the reflection principle behind `Cₙ = C(2n,n) − C(2n,n+1)`

The parent entry (`CatalanNumbersOQ05`) proves the *subtractive* Catalan identity

  `catalan n = C(2n, n) − C(2n, n + 1)`

by manipulating Mathlib's quotient API for `catalan`. That single identity is only
the **diagonal** of a two-parameter family — the *ballot numbers*, or entries of
*Catalan's triangle* (OEIS A009766):

  `T(n, k) = C(n + k, k) − C(n + k, n + 1)`,      for `0 ≤ k ≤ n`.

Combinatorially `T(n, k)` counts monotone lattice paths from `(0,0)` to `(n, k)`
using unit right/up steps that never rise above the main diagonal `y = x`. André's
**reflection principle** evaluates this count: of the `C(n+k, k)` unrestricted paths,
the *bad* ones (those touching the line `y = x + 1`) are in bijection — reflect the
path across that line up to its first touch — with the *unrestricted* paths to the
reflected endpoint `(k − 1, n + 1)`, of which there are `C(n+k, k−1) = C(n+k, n+1)`.
Hence

  `T(n, k) = C(n + k, k) − C(n + k, n + 1)`.

Writing the second (reflected) term as `C(n+k, n+1)` rather than `C(n+k, k−1)` keeps
every binomial index a genuine natural number, so the whole development stays inside
`ℕ` with no truncated subtraction inside a `choose`.

## What this entry adds over the parent

* The **whole triangle**, not just its diagonal: `ballotNumber`.
* The reflection principle's *workhorse* relation `ballot_choose_eq`, pinning the
  reflected term `C(n+k, n+1)` to `k · C(n+k, k) / (n+1)`.
* The **closed form** `(n+1)·T(n,k) = (n+1−k)·C(n+k, k)` (`ballotNumber_scaled`),
  the exact-arithmetic version of `T(n,k) = (n−k+1)/(n+1) · C(n+k, k)`.
* Monotonicity `C(n+k, n+1) ≤ C(n+k, k)` making the subtraction well-posed.
* The **path recurrence** `T(n+1, k+1) = T(n+1, k) + T(n, k+1)` — the additive
  lattice-path law (a path to `(n+1, k+1)` ends with an up- or a right-step),
  which is precisely the "reflection principle expressed as a recurrence".
* The diagonal `T(n, n) = catalan n`, recovering the parent identity as one corner.
* Boundary values `T(n, 0) = 1`, `T(n, 1) = n`.

Everything is a fully machine-checked `ℕ` identity: no axioms, no `native_decide`.
-/

namespace CatalanNumbersOQ05OQ02

open Nat

/-- **Catalan's triangle / ballot number.** `ballotNumber n k` is the number of
monotone lattice paths from `(0,0)` to `(n, k)` that stay weakly below the diagonal,
expressed via André's reflection principle as a difference of binomial coefficients.
The second term `C(n+k, n+1)` is the reflected ("bad path") count. -/
def ballotNumber (n k : ℕ) : ℕ :=
  (n + k).choose k - (n + k).choose (n + 1)

/-- **Reflection workhorse.** The reflected term is exactly `k · C(n+k, k) / (n+1)`,
stated multiplicatively to stay in `ℕ`:
`(n + 1) · C(n + k, n + 1) = k · C(n + k, k)`.

This is the reflection principle's quantitative core: it relates the count of "bad"
paths (reflected to endpoint `(k−1, n+1)`) to the total count. -/
theorem ballot_choose_eq (n k : ℕ) :
    (n + 1) * (n + k).choose (n + 1) = k * (n + k).choose k := by
  -- `C(n+k, n+1) · (n+1) = C(n+k, n) · ((n+k) − n)`  from Pascal's factorial law.
  have h := Nat.choose_succ_right_eq (n + k) n
  have e1 : (n + k) - n = k := by omega
  rw [e1] at h
  -- rewrite `C(n+k, n)` as `C(n+k, k)` by symmetry.
  have e2 : (n + k).choose n = (n + k).choose k := by
    have hs := Nat.choose_symm (show k ≤ n + k by omega)
    rwa [show (n + k) - k = n by omega] at hs
  rw [e2] at h
  -- `h : C(n+k, n+1) · (n+1) = C(n+k, k) · k`; commute into the stated shape.
  calc (n + 1) * (n + k).choose (n + 1)
      = (n + k).choose (n + 1) * (n + 1) := by ring
    _ = (n + k).choose k * k := h
    _ = k * (n + k).choose k := by ring

/-- The reflected term never exceeds the central term, so the defining subtraction
is well-posed: `C(n + k, n + 1) ≤ C(n + k, k)` whenever `k ≤ n`. -/
theorem ballotNumber_le (n k : ℕ) (hk : k ≤ n) :
    (n + k).choose (n + 1) ≤ (n + k).choose k := by
  have hw := ballot_choose_eq n k
  have h : (n + 1) * (n + k).choose (n + 1) ≤ (n + 1) * (n + k).choose k := by
    rw [hw]; gcongr; omega
  exact Nat.le_of_mul_le_mul_left h (by omega)

/-- **Closed form of the Catalan triangle.**
`(n + 1) · T(n, k) = (n + 1 − k) · C(n + k, k)` for `k ≤ n`.
This is the exact-`ℕ` form of `T(n,k) = ((n − k + 1)/(n + 1)) · C(n + k, k)`. -/
theorem ballotNumber_scaled (n k : ℕ) (hk : k ≤ n) :
    (n + 1) * ballotNumber n k = (n + 1 - k) * (n + k).choose k := by
  have hle := ballotNumber_le n k hk
  have hw := ballot_choose_eq n k
  -- `(n+1)·C(n+k,k) = (n+1)·T + (n+1)·C(n+k,n+1)`  (split the central term).
  have h1 : (n + 1) * ((n + k).choose k)
          = (n + 1) * ballotNumber n k + (n + 1) * ((n + k).choose (n + 1)) := by
    rw [← Nat.mul_add]
    congr 1
    simp only [ballotNumber]
    exact (Nat.sub_add_cancel hle).symm
  -- `(n+1)·C(n+k,k) = (n+1−k)·C(n+k,k) + k·C(n+k,k)`  (split the coefficient).
  have h2 : (n + 1) * ((n + k).choose k)
          = (n + 1 - k) * ((n + k).choose k) + k * ((n + k).choose k) := by
    rw [← Nat.add_mul]
    congr 1
    omega
  rw [hw] at h1
  omega

/-- **Diagonal = Catalan number.** `T(n, n) = catalan n`, recovering the parent
identity `catalan n = C(2n, n) − C(2n, n + 1)` as the diagonal of the triangle. -/
theorem ballotNumber_diag (n : ℕ) : ballotNumber n n = catalan n := by
  have h := ballotNumber_scaled n n le_rfl
  rw [show n + 1 - n = 1 by omega, one_mul] at h
  -- `h : (n+1) · T(n,n) = C(2n, n)`.  Also `(n+1) · catalan n = C(2n, n)`.
  have hc : (n + 1) * catalan n = (n + n).choose n := by
    have hcb := succ_mul_catalan_eq_centralBinom n
    rw [Nat.centralBinom_eq_two_mul_choose] at hcb
    rw [hcb, show 2 * n = n + n by omega]
  have : (n + 1) * ballotNumber n n = (n + 1) * catalan n := by rw [h, hc]
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

/-- **Reflection principle as a recurrence.** For interior points `k + 1 ≤ n`,
`T(n + 1, k + 1) = T(n + 1, k) + T(n, k + 1)`: a monotone path to `(n+1, k+1)`
ends in either an up-step (from `(n+1, k)`) or a right-step (from `(n, k+1)`).
The proof is pure Pascal arithmetic on the difference form. -/
theorem ballotNumber_succ_succ (n k : ℕ) (hk : k + 1 ≤ n) :
    ballotNumber (n + 1) (k + 1)
      = ballotNumber (n + 1) k + ballotNumber n (k + 1) := by
  simp only [ballotNumber]
  -- Canonicalise every binomial index into `n + k + _` normal form.
  rw [show n + 1 + (k + 1) = n + k + 2 by ring,
      show n + 1 + k = n + k + 1 by ring,
      show n + (k + 1) = n + k + 1 by ring,
      show n + 1 + 1 = n + 2 by ring]
  -- Two Pascal splits on the top row `n + k + 2`.
  have pa1 : (n + k + 2).choose (k + 1)
           = (n + k + 1).choose k + (n + k + 1).choose (k + 1) := by
    rw [show n + k + 2 = (n + k + 1) + 1 by ring, Nat.choose_succ_succ]
  have pa2 : (n + k + 2).choose (n + 2)
           = (n + k + 1).choose (n + 1) + (n + k + 1).choose (n + 2) := by
    rw [show n + k + 2 = (n + k + 1) + 1 by ring,
        show n + 2 = (n + 1) + 1 by ring, Nat.choose_succ_succ]
  -- Both subtractions on the bottom row `n + k + 1` are well-posed.
  have hb : (n + k + 1).choose (n + 2) ≤ (n + k + 1).choose k := by
    have h := ballotNumber_le (n + 1) k (by omega)
    rw [show n + 1 + k = n + k + 1 by ring, show n + 1 + 1 = n + 2 by ring] at h
    exact h
  have hc : (n + k + 1).choose (n + 1) ≤ (n + k + 1).choose (k + 1) := by
    have h := ballotNumber_le n (k + 1) (by omega)
    rw [show n + (k + 1) = n + k + 1 by ring] at h
    exact h
  omega

/-- Boundary value: `T(n, 0) = 1` (the single path along the bottom edge). -/
theorem ballotNumber_zero (n : ℕ) : ballotNumber n 0 = 1 := by
  simp only [ballotNumber, Nat.add_zero, Nat.choose_zero_right,
    Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), Nat.sub_zero]

/-- Boundary value: `T(n, 1) = n`. -/
theorem ballotNumber_one (n : ℕ) : ballotNumber n 1 = n := by
  simp only [ballotNumber, Nat.choose_one_right, Nat.choose_self]
  omega

/-- The difference identity spelled through `Nat.centralBinom`, matching Mathlib's
preferred name for the diagonal central coefficient. -/
theorem catalan_eq_centralBinom_sub (n : ℕ) :
    catalan n = Nat.centralBinom n - (2 * n).choose (n + 1) := by
  have h := ballotNumber_diag n
  simp only [ballotNumber] at h
  rw [Nat.centralBinom_eq_two_mul_choose, show 2 * n = n + n by ring, ← h]

/-- Sanity checks: the diagonal reproduces the Catalan numbers `1, 1, 2, 5, 14`. -/
example : ballotNumber 0 0 = 1 := ballotNumber_diag 0
example : ballotNumber 1 1 = 1 := ballotNumber_diag 1
example : ballotNumber 2 2 = 2 := ballotNumber_diag 2
example : ballotNumber 3 3 = 5 := ballotNumber_diag 3
example : ballotNumber 4 4 = 14 := ballotNumber_diag 4

/-- Sanity checks: the fourth Catalan-triangle row is `1, 4, 9, 14`. -/
example : ballotNumber 4 0 = 1 := ballotNumber_zero 4
example : ballotNumber 4 1 = 4 := ballotNumber_one 4
example : ballotNumber 3 2 = 5 := by decide
example : ballotNumber 4 2 = 9 := by decide
example : ballotNumber 4 3 = 14 := by decide

end CatalanNumbersOQ05OQ02
