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
* `boole_general` — the exact order-`K` formula for every `K`: peeling off the first `K` Boole
  weights `(-1)^k/2^{k+1}` leaves an exact remainder which is an alternating sum of `Δᴷa`
  (proved by induction on `K`, with `K = 1, 2` recovering the two formulas above);
* `altSum_sub_booleModel_abs_le` — the order-`K` error bound `(1/2^K)·∑ |Δᴷa_j|`, generalizing
  the total-variation bound below (its `K = 1` case);
* `altSum_sub_half_endpoints_abs_le` — a rigorous error bound: the alternating sum differs from
  the half-endpoint model by at most half the total variation `∑ |Δa_j|`;
* `sum_abs_fdiff_antitone` / `altSum_sub_half_first_le_antitone` — for a decreasing `a` the bound
  telescopes to `(1/2)(a_n - a_m)`, so the half-first-term model is accurate to within half the
  drop of `a` across the window — the precise finite form of "remainder ≈ half the first term";
* `altSum_sub_booleModel_le_of_iterate_monotone` — the order-`K` telescoping: when the `K`-th
  difference `Δᴷa` is monotone (either direction) the order-`(K+1)` error collapses to
  `(1/2^{K+1})·|(Δᴷa)_m - (Δᴷa)_n|`, generalizing the antitone half-first-term estimate to every
  order (e.g. a convex decreasing `a` gets the order-`2` bound `(1/4)|Δa_m - Δa_n|`);
* `boole_exact_of_iterate_fdiff_zero` — **exactness on polynomial sequences**: when `Δᴷa ≡ 0`
  the order-`K` remainder is exactly zero, so the alternating sum equals its finite Boole endpoint
  model with no residual (the remainder is precisely the obstruction to polynomiality);
* `altSum_affine` / `altSum_const` — the resulting exact closed forms: the alternating sum of an
  arithmetic progression `α + βj` is the pure endpoint expression
  `½·((-1)^n(α+βn) - (-1)^m(α+βm)) - ¼β·((-1)^n - (-1)^m)`.

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

/-- **General order-`K` finite Boole summation formula.** Iterating `boole_first` exactly `K`
times peels off the leading `K` terms of the discrete Euler–Boole expansion and leaves an exact
remainder which is itself an alternating sum, now of the `K`-th forward difference `Δᴷa`:

`∑_{j=n}^{m-1} (-1)^j a_j`
`  = ∑_{k=0}^{K-1} ((-1)^k / 2^{k+1}) · ((-1)^n (Δᵏa)_n - (-1)^m (Δᵏa)_m)`
`    + ((-1)^K / 2^K) · ∑_{j=n}^{m-1} (-1)^j (Δᴷa)_j`.

`K = 0` is trivial, `K = 1` is `boole_first`, `K = 2` is `boole_second`. The coefficients
`(-1)^k / 2^{k+1}` are the finite Boole/Euler-summation weights, and the remainder is one order
smaller per step, so the formula is the exact finite engine behind the full Boole asymptotic
expansion (no convergence is assumed; the identity holds on every window `n ≤ m`). -/
theorem boole_general (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) (K : ℕ) :
    altSum a n m
      = (∑ k ∈ Finset.range K,
          ((-1 : ℝ) ^ k / 2 ^ (k + 1))
            * ((-1 : ℝ) ^ n * (fdiff^[k] a) n - (-1 : ℝ) ^ m * (fdiff^[k] a) m))
        + ((-1 : ℝ) ^ K / 2 ^ K) * altSum (fdiff^[K] a) n m := by
  induction K with
  | zero => simp
  | succ K ih =>
    -- peel the new top term off the sum and unfold the order-`K` formula
    rw [Finset.sum_range_succ, ih]
    -- split the order-`K` remainder by one more step of `boole_first` on `Δᴷa`
    rw [boole_first (fdiff^[K] a) n m h]
    -- align both sides on the single atom `fdiff (fdiff^[K] a) = Δ^{K+1} a`
    rw [show (fdiff^[K + 1] a) = fdiff (fdiff^[K] a) from congrFun (Function.iterate_succ' fdiff K) a]
    rw [pow_succ, pow_succ]
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

/-- For a monotone (increasing) sequence the total variation telescopes to `a_m - a_n`. -/
theorem sum_abs_fdiff_monotone {a : ℕ → ℝ} (ha : Monotone a) (n m : ℕ) (h : n ≤ m) :
    ∑ j ∈ Finset.Ico n m, |fdiff a j| = a m - a n := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih, fdiff, abs_of_nonneg]
    · ring
    · have : a k ≤ a (k + 1) := ha (Nat.le_succ k)
      linarith

/-- Either way — increasing or decreasing — the total variation of a monotone sequence over a
window is the absolute endpoint difference `|a_m - a_n|`. -/
theorem sum_abs_fdiff_of_monotone_or_antitone {a : ℕ → ℝ} (n m : ℕ) (h : n ≤ m)
    (ha : Monotone a ∨ Antitone a) :
    ∑ j ∈ Finset.Ico n m, |fdiff a j| = |a m - a n| := by
  rcases ha with ha | ha
  · rw [sum_abs_fdiff_monotone ha n m h, abs_of_nonneg (sub_nonneg.mpr (ha h))]
  · rw [sum_abs_fdiff_antitone ha n m h, abs_of_nonpos (by have := ha h; linarith)]
    ring

/-- **Half-first-term remainder estimate for a decreasing sequence.** The alternating sum lies
within `(1/2)(a_n - a_m)` of the half-endpoint model `½·((-1)^n a_n - (-1)^m a_m)`. Letting the
upper endpoint terms tend to `0` (as for a convergent alternating series with `a → 0`) leaves the
leading model `½·(-1)^n a_n`: half the first omitted term, accurate to half the drop of `a`. -/
theorem altSum_sub_half_first_le_antitone {a : ℕ → ℝ} (ha : Antitone a) (n m : ℕ) (h : n ≤ m) :
    |altSum a n m - (1 / 2) * ((-1 : ℝ) ^ n * a n - (-1 : ℝ) ^ m * a m)|
      ≤ (1 / 2) * (a n - a m) := by
  rw [← sum_abs_fdiff_antitone ha n m h]
  exact altSum_sub_half_endpoints_abs_le a n m h

/-- **Order-`K` remainder bound.** The alternating sum differs from its order-`K` Boole model
(the first `K` terms of `boole_general`) by at most `(1/2^K)·∑|Δᴷa_j|`. This generalizes the
total-variation bound `altSum_sub_half_endpoints_abs_le` (its `K = 1` case): each extra order of
the expansion shrinks the error prefactor by another factor of `1/2` while replacing the window
total variation of `a` with that of its `K`-th difference. -/
theorem altSum_sub_booleModel_abs_le (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) (K : ℕ) :
    |altSum a n m
        - (∑ k ∈ Finset.range K,
            ((-1 : ℝ) ^ k / 2 ^ (k + 1))
              * ((-1 : ℝ) ^ n * (fdiff^[k] a) n - (-1 : ℝ) ^ m * (fdiff^[k] a) m))|
      ≤ (1 / 2 ^ K) * ∑ j ∈ Finset.Ico n m, |(fdiff^[K] a) j| := by
  rw [boole_general a n m h K, add_sub_cancel_left, abs_mul]
  have hpow : |((-1 : ℝ) ^ K / 2 ^ K)| = 1 / 2 ^ K := by
    rw [abs_div, abs_pow, abs_pow]; norm_num
  rw [hpow]
  exact mul_le_mul_of_nonneg_left (abs_altSum_le (fdiff^[K] a) n m) (by positivity)

/-- **Higher-order monotone telescoping of the Boole remainder.** If the `K`-th forward
difference `Δᴷa` is monotone (in *either* direction), the order-`(K+1)` remainder bound
`altSum_sub_booleModel_abs_le` telescopes — the window total variation of `Δ^{K+1}a` collapses to a
single absolute endpoint difference of `Δᴷa`:

`|∑_{j=n}^{m-1} (-1)^j a_j - (order-(K+1) Boole model)| ≤ (1/2^{K+1})·|(Δᴷa)_m - (Δᴷa)_n|`.

This is the exact finite "remainder ≈ leading Boole term" statement at every order. `K = 0` with
`a` antitone recovers `altSum_sub_half_first_le_antitone` (and now covers the increasing case too);
higher `K` is the natural refinement for sequences with monotone higher differences — e.g. a
convex decreasing `a` (so `Δa` is monotone) gets the order-`2` estimate
`(1/4)·|Δa_m - Δa_n|`. -/
theorem altSum_sub_booleModel_le_of_iterate_monotone (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) (K : ℕ)
    (hg : Monotone (fdiff^[K] a) ∨ Antitone (fdiff^[K] a)) :
    |altSum a n m
        - (∑ k ∈ Finset.range (K + 1),
            ((-1 : ℝ) ^ k / 2 ^ (k + 1))
              * ((-1 : ℝ) ^ n * (fdiff^[k] a) n - (-1 : ℝ) ^ m * (fdiff^[k] a) m))|
      ≤ (1 / 2 ^ (K + 1)) * |(fdiff^[K] a) m - (fdiff^[K] a) n| := by
  have hbound := altSum_sub_booleModel_abs_le a n m h (K + 1)
  rw [show (fdiff^[K + 1] a) = fdiff (fdiff^[K] a) from
        congrFun (Function.iterate_succ' fdiff K) a,
      sum_abs_fdiff_of_monotone_or_antitone n m h hg] at hbound
  exact hbound

/-- An alternating sum of the identically-zero sequence vanishes: every summand `(-1)^j·0 = 0`. -/
theorem altSum_eq_zero_of_forall_eq_zero (a : ℕ → ℝ) (n m : ℕ) (ha : ∀ j, a j = 0) :
    altSum a n m = 0 := by
  simp only [altSum]
  exact Finset.sum_eq_zero fun j _ => by rw [ha j, mul_zero]

/-- **Exactness of the finite Boole formula on polynomial sequences.** If the `K`-th forward
difference `Δᴷa` vanishes identically — equivalently `a` agrees with a polynomial of degree `< K`
in `j` on the relevant range — then the order-`K` Boole remainder is exactly zero, so the
alternating sum *equals* its finite Boole endpoint model with no residual:

`∑_{j=n}^{m-1} (-1)^j a_j = ∑_{k=0}^{K-1} ((-1)^k/2^{k+1})·((-1)^n (Δᵏa)_n - (-1)^m (Δᵏa)_m)`.

This is the sharp qualitative boundary of the expansion: the alternating sum of a sequence is a
*finite* combination of endpoint difference-data precisely when the sequence is (eventually)
polynomial, and the order-`K` Boole remainder `((-1)^K/2^K)·altSum(Δᴷa)` is exactly the
obstruction to `Δᴷa ≡ 0`. -/
theorem boole_exact_of_iterate_fdiff_zero (a : ℕ → ℝ) (n m : ℕ) (h : n ≤ m) (K : ℕ)
    (hK : ∀ j, (fdiff^[K] a) j = 0) :
    altSum a n m
      = ∑ k ∈ Finset.range K,
          ((-1 : ℝ) ^ k / 2 ^ (k + 1))
            * ((-1 : ℝ) ^ n * (fdiff^[k] a) n - (-1 : ℝ) ^ m * (fdiff^[k] a) m) := by
  rw [boole_general a n m h K, altSum_eq_zero_of_forall_eq_zero (fdiff^[K] a) n m hK,
    mul_zero, add_zero]

/-- The forward difference of an affine sequence `a_j = α + β·j` is the constant `β`: this is the
discrete analogue of `(α + βx)' = β`, and shows `Δa` is constant so `Δ²a ≡ 0`. -/
theorem fdiff_affine (α β : ℝ) : fdiff (fun j => α + β * (j : ℝ)) = fun _ => β := by
  funext j; simp only [fdiff]; push_cast; ring

/-- The second forward difference of an affine sequence vanishes identically. -/
theorem iterate_fdiff_two_affine (α β : ℝ) :
    ∀ j, (fdiff^[2] (fun j => α + β * (j : ℝ))) j = 0 := by
  have step : fdiff^[2] (fun j => α + β * (j : ℝ)) = fdiff (fun _ => β) := by
    have h1 : fdiff^[2] (fun j => α + β * (j : ℝ))
        = fdiff (fdiff^[1] (fun j => α + β * (j : ℝ))) :=
      congrFun (Function.iterate_succ' fdiff 1) _
    rw [h1, Function.iterate_one, fdiff_affine]
  intro j; rw [step]; simp only [fdiff]; ring

/-- **Exact closed form for the alternating sum of an affine sequence.** Since `Δ²(α + β·j) ≡ 0`,
the order-`2` Boole formula terminates and evaluates completely: the alternating sum of an
arithmetic progression is a pure endpoint expression, with no remainder.

`∑_{j=n}^{m-1} (-1)^j (α + βj)`
`  = ½·((-1)^n (α+βn) - (-1)^m (α+βm)) - ¼·β·((-1)^n - (-1)^m)`.

This is the exact discrete Boole/Euler evaluation of an alternating polynomial sum of degree `1`;
the constant case `β = 0` recovers `∑ (-1)^j α = ½α·((-1)^n - (-1)^m)`. -/
theorem altSum_affine (α β : ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum (fun j => α + β * (j : ℝ)) n m
      = (1 / 2) * ((-1 : ℝ) ^ n * (α + β * n) - (-1 : ℝ) ^ m * (α + β * m))
        - (1 / 4) * β * ((-1 : ℝ) ^ n - (-1 : ℝ) ^ m) := by
  rw [boole_exact_of_iterate_fdiff_zero (fun j => α + β * (j : ℝ)) n m h 2
      (iterate_fdiff_two_affine α β), Finset.sum_range_succ, Finset.sum_range_one]
  simp only [Function.iterate_zero, id_eq, pow_zero, pow_one, Function.iterate_one, fdiff_affine]
  ring

/-- **Closed form for a pure alternating sum of a constant.** The `β = 0` specialization of
`altSum_affine`: `∑_{j=n}^{m-1} (-1)^j c = ½c·((-1)^n - (-1)^m)`. -/
theorem altSum_const (c : ℝ) (n m : ℕ) (h : n ≤ m) :
    altSum (fun _ => c) n m = (1 / 2) * c * ((-1 : ℝ) ^ n - (-1 : ℝ) ^ m) := by
  have key : (fun _ : ℕ => c) = (fun j : ℕ => c + 0 * (j : ℝ)) := by funext j; ring
  rw [key, altSum_affine c 0 n m h]; ring

end AlternatingSeriesBooleSummation
