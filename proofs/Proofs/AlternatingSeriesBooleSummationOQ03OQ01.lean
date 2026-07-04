import Mathlib
import Proofs.AlternatingSeriesBooleSummation

/-
# The Finite Boole Weights are Geometric — Exact Rational Closed Forms for Alternating Power Sums

The parent entry (`AlternatingSeriesBooleSummation`) proves the exact finite Boole summation
formula `boole_general`, which peels off the leading Boole weights

`w_k = (-1)^k / 2^{k+1}`   (`k = 0, 1, 2, …`)

from an alternating sum `∑_{j=n}^{m-1} (-1)^j a_j`. A natural open question (parent `oq-03`) asks
for the *exact rational identity* satisfied by these weights, framed there as a suspected
coincidence with the Euler numbers / Euler-polynomial values `E_k(0)` via the exponential
generating function `1/(1+e^t)`.

**That coincidence is false, and we record the honest facts instead.** The weights of this
first-order *iterate* scheme are purely **geometric**: `w_{k+1} = -(1/2)·w_k`, `w_0 = 1/2`. Their
*ordinary* generating function is therefore the elementary rational function

`∑_{k=0}^{K-1} w_k x^k = (1 - (-x/2)^K)/(x + 2)`,   converging to `1/(x+2)` as `K → ∞`,

which is *not* the Euler exponential generating function `1/(1+e^t)`, and `w_k ≠ E_k(0)`
(e.g. `w_2 = 1/8` while `E_2(0) = 0`). Mathlib has Bernoulli numbers and Bernoulli polynomials but
no Euler polynomials; the genuine classical Boole–Euler link runs through the *alternating power
sums* `∑ (-1)^j j^p` (whose closed forms are Euler polynomials), not through the iterate weights.

This file therefore answers the *tractable, true* core of the question:

* `booleWeight_zero`, `booleWeight_succ` — the weights are geometric with ratio `-1/2`;
* `sum_booleWeight_geom` — the **exact finite rational identity** for the partial generating
  function `∑_{k<K} w_k x^k = (1 - (-x/2)^K)/(x+2)` (valid for `x ≠ -2`), the honest replacement
  for the (false) Euler-EGF claim;
* `altSum_sq` — the resulting **exact rational closed form** for the alternating sum of `j^2`,
  obtained from the parent's polynomial-exactness theorem `boole_exact_of_iterate_fdiff_zero`
  (since `Δ^3(j^2) ≡ 0`). This extends the parent's `altSum_affine` (degree `1`) to degree `2`
  and is a concrete finite instance of the genuine Boole/Euler evaluation of alternating monomial
  sums. (The degree-`3` cube case is the natural next rung, left for follow-up.)

All results are over `ℝ`, elementary, and axiom-free.
-/

namespace AlternatingSeriesBooleSummationOQ03

open Finset AlternatingSeriesBooleSummation

/-- The finite Boole/Euler-summation weight `w_k = (-1)^k / 2^{k+1}` appearing in
`boole_general`. It is the coefficient with which the `k`-th endpoint difference enters the exact
finite Boole formula. -/
noncomputable def booleWeight (k : ℕ) : ℝ := (-1 : ℝ) ^ k / 2 ^ (k + 1)

/-- The weight `booleWeight k` is definitionally the coefficient used in `boole_general`. -/
theorem booleWeight_eq (k : ℕ) : booleWeight k = (-1 : ℝ) ^ k / 2 ^ (k + 1) := rfl

/-- The leading weight is `1/2` — "half the first term". -/
theorem booleWeight_zero : booleWeight 0 = 1 / 2 := by norm_num [booleWeight]

/-- **The Boole weights are geometric.** Each weight is `-1/2` times the previous one, so the
sequence is the geometric progression `1/2, -1/4, 1/8, -1/16, …`. This is the precise sense in
which the weights are elementary; they are *not* the Euler numbers, whose recurrence is not
geometric. -/
theorem booleWeight_succ (k : ℕ) : booleWeight (k + 1) = -(1 / 2) * booleWeight k := by
  simp only [booleWeight, pow_succ]
  ring

/-- **Exact finite rational generating function of the Boole weights.** For every `x ≠ -2`,

`∑_{k=0}^{K-1} w_k x^k = (1 - (-x/2)^K) / (x + 2)`.

This is the honest finite exact rational identity satisfied by the Boole weights: their partial
*ordinary* generating function is an elementary geometric sum, converging to `1/(x+2)` as
`K → ∞`. In particular the weights do **not** arise from the Euler exponential generating function
`1/(1 + e^t)`. -/
theorem sum_booleWeight_geom (x : ℝ) (hx : x ≠ -2) (K : ℕ) :
    ∑ k ∈ Finset.range K, booleWeight k * x ^ k = (1 - (-x / 2) ^ K) / (x + 2) := by
  have hr : (-x / 2 : ℝ) ≠ 1 := by
    intro h; apply hx; field_simp at h; linarith
  have h1 : (-x / 2 : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hr
  have hxne : (x + 2 : ℝ) ≠ 0 := by intro h; apply hx; linarith
  have step : ∀ k, booleWeight k * x ^ k = (1 / 2) * (-x / 2) ^ k := by
    intro k
    have hpow : (-x / 2 : ℝ) ^ k = (-1) ^ k * x ^ k / 2 ^ k := by
      rw [neg_div, neg_pow, div_pow]; ring
    rw [booleWeight, hpow, pow_succ]; ring
  rw [Finset.sum_congr rfl (fun k _ => step k), ← Finset.mul_sum, geom_sum_eq hr K]
  -- Freeze the K-th power as an atom so field_simp cannot expand (-x/2)^K into
  -- (-x)^K / 2^K, and expose the (x+2) denominator on the left to match the right.
  set A := (-x / 2 : ℝ) ^ K with hA
  rw [show (-x / 2 : ℝ) - 1 = -(x + 2) / 2 by ring]
  field_simp
  ring

/-! ### Exact rational closed forms for alternating power sums

Since the `(p+1)`-th forward difference of `j ↦ j^p` vanishes identically, the parent's
`boole_exact_of_iterate_fdiff_zero` terminates and evaluates the alternating sum to a pure
endpoint expression. We record the closed forms for `p = 2, 3`, extending the parent's
`altSum_affine` (the `p ≤ 1` case). -/

/-- First forward difference of `j ↦ j^2` is `2j + 1` (discrete analogue of `(x^2)' = 2x`). -/
theorem fdiff_sq : fdiff (fun j : ℕ => (j : ℝ) ^ 2) = fun j : ℕ => 2 * (j : ℝ) + 1 := by
  funext j; simp only [fdiff]; push_cast; ring

/-- Second forward difference of `j ↦ j^2` is the constant `2`. -/
theorem fdiff_two_sq : fdiff^[2] (fun j : ℕ => (j : ℝ) ^ 2) = fun _ => (2 : ℝ) := by
  have h1 : fdiff^[2] (fun j : ℕ => (j : ℝ) ^ 2) = fdiff (fdiff^[1] (fun j : ℕ => (j : ℝ) ^ 2)) :=
    congrFun (Function.iterate_succ' fdiff 1) _
  rw [h1, Function.iterate_one, fdiff_sq]
  funext j; simp only [fdiff]; push_cast; ring

/-- Third forward difference of `j ↦ j^2` vanishes identically. -/
theorem fdiff_three_sq : ∀ j, fdiff^[3] (fun j : ℕ => (j : ℝ) ^ 2) j = 0 := by
  have step : fdiff^[3] (fun j : ℕ => (j : ℝ) ^ 2) = fdiff (fun _ => (2 : ℝ)) := by
    have h1 : fdiff^[3] (fun j : ℕ => (j : ℝ) ^ 2) = fdiff (fdiff^[2] (fun j : ℕ => (j : ℝ) ^ 2)) :=
      congrFun (Function.iterate_succ' fdiff 2) _
    rw [h1, fdiff_two_sq]
  intro j; rw [step]; simp only [fdiff]; ring

/-- **Exact rational closed form for the alternating sum of squares.** Since `Δ^3(j^2) ≡ 0` the
order-`3` Boole formula terminates:

`∑_{j=n}^{m-1} (-1)^j j^2`
`  = ½((-1)^n n^2 - (-1)^m m^2) - ¼((-1)^n(2n+1) - (-1)^m(2m+1)) + ⅛((-1)^n·2 - (-1)^m·2)`.

The three coefficients `½, -¼, ⅛` are the leading Boole weights `booleWeight 0, 1, 2`. -/
theorem altSum_sq (n m : ℕ) (h : n ≤ m) :
    altSum (fun j : ℕ => (j : ℝ) ^ 2) n m
      = (1 / 2) * ((-1 : ℝ) ^ n * (n : ℝ) ^ 2 - (-1 : ℝ) ^ m * (m : ℝ) ^ 2)
        - (1 / 4) * ((-1 : ℝ) ^ n * (2 * (n : ℝ) + 1) - (-1 : ℝ) ^ m * (2 * (m : ℝ) + 1))
        + (1 / 8) * ((-1 : ℝ) ^ n * 2 - (-1 : ℝ) ^ m * 2) := by
  rw [boole_exact_of_iterate_fdiff_zero (fun j : ℕ => (j : ℝ) ^ 2) n m h 3 fdiff_three_sq,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Function.iterate_zero, id_eq, Function.iterate_one, fdiff_sq]
  rw [show fdiff^[2] (fun j : ℕ => (j : ℝ) ^ 2) = fun _ => (2 : ℝ) from fdiff_two_sq]
  norm_num
  ring

/-- **Sanity check.** The constant case of the machinery agrees with the parent's `altSum_const`
on a concrete window: `∑_{j=0}^{3} (-1)^j = 1 - 1 + 1 - 1 = 0`. -/
example : altSum (fun _ => (1 : ℝ)) 0 4 = 0 := by
  rw [altSum_const 1 0 4 (by norm_num)]; norm_num

end AlternatingSeriesBooleSummationOQ03
