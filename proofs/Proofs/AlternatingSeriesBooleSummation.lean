import Mathlib

/-
# A Finite Boole Summation Formula for Alternating Sums

When an alternating series `∑ (-1)^j a_j` is truncated, the leftover (the *remainder*) is,
to leading order, **half the first omitted term**, with a full asymptotic correction in the
discrete derivatives of `a`:

`R_n ~ ((-1)^n / 2) · [ a_n - (1/4) a_n'' + ⋯ ]`   (Boole / Euler–Maclaurin expansion).

The honest, fully rigorous engine behind this heuristic is an **exact finite identity**, with
no appeal to convergence. Writing `Δa_j = a_{j+1} - a_j` for the forward difference and

`altSum a n m = ∑_{j=n}^{m-1} (-1)^j a_j`,

the *first-order Boole summation formula* states

`altSum a n m = (1/2)·((-1)^n a_n - (-1)^m a_m) - (1/2)·altSum (Δa) n m`.

The leading term `(1/2)·(-1)^n a_n` is exactly "half the first term"; the residual is a *new*
alternating sum, now of the differences `Δa`, which is one order smaller. Iterating once gives
the second-order formula involving `Δ²a`, the discrete analogue of the `a''` correction above.

This file proves:

* `boole_first`  — the exact first-order formula (by induction / discrete summation by parts);
* `boole_second` — its one-step iterate, exposing the `Δ²a` (second-difference) term;
* `altSum_sub_half_endpoints_abs_le` — a rigorous error bound: the alternating sum differs from
  the half-endpoint model by at most half the total variation `∑ |Δa_j|`;
* `sum_abs_fdiff_antitone` / `altSum_sub_half_first_le_antitone` — for a decreasing `a` the bound
  telescopes to `(1/2)(a_n - a_m)`, so the half-first-term model is accurate to within half the
  drop of `a` across the window — the precise finite form of "remainder ≈ half the first term".

All results are over `ℝ`, elementary, and axiom-free. Mathlib has the alternating series test and
its bracketing/remainder bounds, but not the Boole summation identity itself.
-/

namespace AlternatingSeriesBooleSummation

open Finset

/-- The forward difference `Δa_j = a_{j+1} - a_j`. -/
def fdiff (a : ℕ → ℝ) (j : ℕ) : ℝ := a (j + 1) - a j

/-- The alternating partial sum `∑_{j=n}^{m-1} (-1)^j a_j`. -/
def altSum (a : ℕ → ℝ) (n m : ℕ) : ℝ := ∑ j ∈ Finset.Ico n m, (-1 : ℝ) ^ j * a j

/-- One-step recurrence: appending the top index multiplies by the alternating sign. -/
theorem altSum_succ (a : ℕ → ℝ) {n m : ℕ} (h : n ≤ m) :
    altSum a n (m + 1) = altSum a n m + (-1 : ℝ) ^ m * a m := by
  simp only [altSum]
  rw [Finset.sum_Ico_succ_top h]

/-- **First-order Boole summation formula.**
`∑_{j=n}^{m-1} (-1)^j a_j = ½·((-1)^n a_n - (-1)^m a_m) - ½·∑_{j=n}^{m-1} (-1)^j Δa_j`.
The leading endpoint term `½·(-1)^n a_n` is "half the first term"; the residual is the same
kind of alternating sum applied to the forward differences `Δa`. -/
theorem boole_first (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum a n m
      = (1 / 2) * ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m)
        - (1 / 2) * altSum (fdiff a) n m := by
  induction m, h using Nat.le_induction with
  | base => simp only [altSum, Finset.Ico_self, Finset.sum_empty]; ring
  | succ k hk ih =>
    rw [altSum_succ a hk, altSum_succ (fdiff a) hk, ih, fdiff, pow_succ]
    ring

/-- **Second-order Boole summation formula.** Iterating `boole_first` once on the differences
exposes the discrete second-difference (`Δ²a`) correction with coefficient `1/4`, matching the
`a''` term of the asymptotic expansion. -/
theorem boole_second (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum a n m
      = (1 / 2) * ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m)
        - (1 / 4) * ((-1 : ℝ) ^ n * fdiff a n - (-1 : ℝ) ^ m * fdiff a m)
        + (1 / 4) * altSum (fdiff (fdiff a)) n m := by
  rw [boole_first a n m h, boole_first (fdiff a) n m h]
  ring

/-- **Exact error identity.** The alternating sum minus its half-endpoint model equals minus
half the alternating sum of the forward differences. -/
theorem altSum_sub_half_endpoints (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum a n m - (1 / 2) * ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m)
      = -(1 / 2) * altSum (fdiff a) n m := by
  rw [boole_first a n m h]; ring

/-- The absolute value of an alternating sum is bounded by the sum of absolute values, since the
signs `(-1)^j` have modulus `1`. -/
theorem abs_altSum_le (a : ℕ → ℝ) (n m : ℕ) :
    |altSum a n m| ≤ ∑ j ∈ Finset.Ico n m, |a j| := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [abs_mul, abs_pow]
  simp

/-- **Total-variation remainder bound.** The alternating sum differs from its half-endpoint model
by at most half the total variation `∑ |Δa_j|` over the window. As the window's upper terms
vanish this is the rigorous form of "the remainder is approximately half the first omitted term". -/
theorem altSum_sub_half_endpoints_abs_le (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) :
    |altSum a n m - (1 / 2) * ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m)|
      ≤ (1 / 2) * ∑ j ∈ Finset.Ico n m, |fdiff a j| := by
  rw [altSum_sub_half_endpoints a n m h, neg_mul, abs_neg, abs_mul]
  have h12 : |(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [h12]
  exact mul_le_mul_of_nonneg_left (abs_altSum_le (fdiff a) n m) (by norm_num)

/-- For an antitone (decreasing) sequence the total variation telescopes to `a_n - a_m`. -/
theorem sum_abs_fdiff_antitone {a : ℕ → ℝ} (ha : Antitone a) (n m : ℕ) (h : n ≤ m) :
    ∑ j ∈ Finset.Ico n m, |fdiff a j| = a n - a m := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih, fdiff, abs_of_nonpos]
    · ring
    · have : a (k + 1) ≤ a k := ha (Nat.le_succ k)
      linarith

/-- **Half-first-term remainder estimate for a decreasing sequence.** The alternating sum lies
within `(1/2)(a_n - a_m)` of the half-endpoint model `½·((-1)^n a_n - (-1)^m a_m)`. Letting the
upper endpoint terms tend to `0` (as for a convergent alternating series with `a → 0`) leaves the
leading model `½·(-1)^n a_n`: half the first omitted term, accurate to half the drop of `a`. -/
theorem altSum_sub_half_first_le_antitone {a : ℕ → ℝ} (ha : Antitone a) (n m : ℕ) (h : n ≤ m) :
    |altSum a n m - (1 / 2) * ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m)|
      ≤ (1 / 2) * (a n - a m) := by
  rw [← sum_abs_fdiff_antitone ha n m h]
  exact altSum_sub_half_endpoints_abs_le a n m h

end AlternatingSeriesBooleSummation
