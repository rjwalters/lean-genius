import Mathlib

/-!
# Collatz Cycles OQ-02: General Logarithmic Lower Bound on Cycle Length

`CollatzCycles.lean` establishes, for a hypothetical non-trivial Collatz cycle with
`J` odd (tripling) steps and `M` even (halving) steps, the **halving constraint**
`3 ^ J < 2 ^ M` (generalised in `collatz-cycles-oq-04`), together with a *specific*
ladder of minimal-halving bounds for small `J` (`min_halvings_one_odd` … four_odd:
`J = 1 → M ≥ 2`, `J = 2 → M ≥ 4`, `J = 3 → M ≥ 5`, `J = 4 → M ≥ 7`).

This file replaces that finite ladder by the **general** quantitative bound that holds
for every `J`. From `3 ^ J < 2 ^ M`, taking base-2 logarithms gives the sharp growth
rate

  `M > J · log₂ 3`,

hence (ceiling) `M ≥ ⌈J · log₂ 3⌉₊`, which reproduces every entry of the specific
ladder as a special case, and the total cycle length `L = M + J` obeys

  `L > J · log₂ 6 ≈ 2.585 · J`.

## Honest scope

This is the **elementary** logarithmic core of Eliahou's theorem, not the full result.
Eliahou (1993) sharpens the constant via the continued-fraction expansion of `log₂ 3`
to obtain the famous numerical bound (a non-trivial cycle has length ≥ 17,087,915);
that refinement needs Diophantine-approximation machinery not formalised here. What is
proved here is the clean linear-in-`J` lower bound implied directly by the halving
constraint, valid for all `J ≥ 1`.
-/

open Real

namespace CollatzCyclesOQ02

/-- **General halving bound.** From the cycle halving constraint `3 ^ J < 2 ^ M`,
the number of halvings exceeds `J · log₂ 3`. This is the exact growth rate
(`log₂ 3 ≈ 1.585`), valid for every `J` — generalising the specific ladder
`min_halvings_one_odd … four_odd` in `CollatzCycles.lean`. -/
theorem halvings_gt_logb {M J : ℕ} (h : 3 ^ J < 2 ^ M) :
    (J : ℝ) * Real.logb 2 3 < (M : ℝ) := by
  have hcast : (3 : ℝ) ^ J < (2 : ℝ) ^ M := by
    have := (Nat.cast_lt (α := ℝ)).mpr h
    push_cast at this
    exact this
  have h3pos : (0 : ℝ) < (3 : ℝ) ^ J := by positivity
  have hlt : Real.logb 2 ((3 : ℝ) ^ J) < Real.logb 2 ((2 : ℝ) ^ M) :=
    Real.logb_lt_logb (by norm_num) h3pos hcast
  rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at hlt
  simpa using hlt

/-- **Integer halving bound.** `M ≥ ⌈J · log₂ 3⌉₊`. Evaluating the ceiling at small
`J` recovers the specific ladder: `J = 1 → ⌈1.585⌉ = 2`, `J = 2 → ⌈3.170⌉ = 4`,
`J = 3 → ⌈4.755⌉ = 5`, `J = 4 → ⌈6.340⌉ = 7`. -/
theorem halvings_ge_ceil {M J : ℕ} (h : 3 ^ J < 2 ^ M) :
    ⌈(J : ℝ) * Real.logb 2 3⌉₊ ≤ M :=
  Nat.ceil_le.mpr (halvings_gt_logb h).le

/-- **General cycle-length lower bound.** A non-trivial cycle with `J` odd steps and
`M` even steps (so total length `L = M + J`) satisfies `L > J · log₂ 6`. Since
`log₂ 6 = 1 + log₂ 3 ≈ 2.585`, the length grows at least linearly in the number of
odd steps. -/
theorem cycle_length_gt {M J : ℕ} (h : 3 ^ J < 2 ^ M) :
    (J : ℝ) * Real.logb 2 6 < ((M + J : ℕ) : ℝ) := by
  have hb := halvings_gt_logb h
  have h6 : Real.logb 2 6 = Real.logb 2 3 + 1 := by
    rw [show (6 : ℝ) = 3 * 2 by norm_num,
        Real.logb_mul (by norm_num) (by norm_num),
        Real.logb_self_eq_one (by norm_num)]
  have hexp : (J : ℝ) * Real.logb 2 6 = (J : ℝ) * Real.logb 2 3 + (J : ℝ) := by
    rw [h6]; ring
  rw [hexp]
  push_cast
  linarith [hb]

/-- **Elementary halving bound** (no logarithms): more halvings than triplings,
`M > J`. Immediate from `2 ^ J ≤ 3 ^ J < 2 ^ M`. Weaker than `halvings_gt_logb`
(which has the sharp constant `log₂ 3 > 1`) but fully elementary. -/
theorem halvings_gt_odd_steps {M J : ℕ} (h : 3 ^ J < 2 ^ M) : J < M := by
  have h2 : 2 ^ J ≤ 3 ^ J := Nat.pow_le_pow_left (by norm_num) J
  have : 2 ^ J < 2 ^ M := lt_of_le_of_lt h2 h
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this

/-- **Elementary cycle-length bound**: `L = M + J ≥ 2J + 1`. A non-trivial cycle is
more than twice as long as its number of odd steps. (The logarithmic bound
`cycle_length_gt` improves the slope from `2` to `log₂ 6 ≈ 2.585`.) -/
theorem cycle_length_ge_two_mul {M J : ℕ} (_hJ : 1 ≤ J) (h : 3 ^ J < 2 ^ M) :
    2 * J + 1 ≤ M + J := by
  have := halvings_gt_odd_steps h
  omega

end CollatzCyclesOQ02
