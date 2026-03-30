import Mathlib

/-
# r-Way Birthday Collision Asymptotics (OQ-02-OQ-03)

## Open Question
Can the tight collision asymptotics (OQ-02: ∏(1-i/d) ≤ exp(-k(k-1)/(2d)))
be extended to r-way collisions, where the threshold scales as d^((r-1)/r)?

## Background
- OQ-02 proves exponential bounds for pairwise (r=2) collisions
- OQ-03 formalizes k-way coincidences and generalized pigeonhole
- This file combines both: asymptotic counting bounds for r-way collisions

## Approach
The expected number of r-tuples sharing a birthday is C(n,r)/d^(r-1).
Using Mathlib's choose bounds (C(n,r) ≈ n^r/r!), we show this quantity
scales as n^r/(r!·d^(r-1)). Setting it to 1 gives the threshold
n ≈ (r!·d^(r-1))^(1/r) ≈ d^((r-1)/r)·(r!)^(1/r).

For r=2: threshold = √(2d) ≈ √(2)·d^(1/2), recovering the classical result.

## What Remains
The full exponential bound P(no r-way coincidence) ≤ exp(-C(n,r)/d^(r-1))
requires Poisson approximation or inclusion-exclusion, left for future work.

Results: 6 theorems, 0 axioms, 0 sorries
-/

set_option linter.unusedVariables false

namespace BirthdayRWay

open Finset BigOperators Real

-- ============================================================
-- SECTION I: Definition
-- ============================================================

/-- The r-tuple collision expectation: C(n,r) / d^(r-1).
    In a uniform random birthday assignment, this is the expected number of
    r-tuples sharing a birthday. When it exceeds 1, r-way collisions are likely. -/
noncomputable def rWayExpectation (n d r : ℕ) : ℝ :=
  (n.choose r : ℝ) / (d : ℝ) ^ (r - 1)

-- ============================================================
-- SECTION II: Classical Recovery
-- ============================================================

/-- For r=2, the expectation is C(n,2)/d = n(n-1)/(2d),
    recovering the pairwise collision count from OQ-02. -/
theorem rWay_pairwise (n d : ℕ) :
    rWayExpectation n d 2 = (n.choose 2 : ℝ) / (d : ℝ) := by
  simp [rWayExpectation, pow_one]

-- ============================================================
-- SECTION III: Upper and Lower Bounds
-- ============================================================

/-- Upper bound via Mathlib's choose_le_pow: C(n,r) ≤ n^r/r!.
    So the expectation is at most n^r/(r!·d^(r-1)). -/
theorem rWayExpectation_upper (n d r : ℕ) (hd : 0 < d) :
    rWayExpectation n d r ≤ (n : ℝ) ^ r / ((r.factorial : ℝ) * (d : ℝ) ^ (r - 1)) := by
  unfold rWayExpectation
  conv_rhs => rw [← div_div]
  exact div_le_div_of_nonneg_right (Nat.choose_le_pow r n) (by positivity)

/-- Lower bound via Mathlib's pow_le_choose: (n+1-r)^r/r! ≤ C(n,r).
    So the expectation is at least (n+1-r)^r/(r!·d^(r-1)). -/
theorem rWayExpectation_lower (n d r : ℕ) (hd : 0 < d) :
    ((n + 1 - r : ℕ) : ℝ) ^ r / ((r.factorial : ℝ) * (d : ℝ) ^ (r - 1)) ≤
      rWayExpectation n d r := by
  unfold rWayExpectation
  conv_lhs => rw [← div_div]
  exact div_le_div_of_nonneg_right (Nat.pow_le_choose r n) (by positivity)

-- ============================================================
-- SECTION IV: Threshold
-- ============================================================

/-- When C(n,r) > d^(r-1), the expectation exceeds 1.
    This is the counting threshold for r-way birthday collisions. -/
theorem rWayExpectation_gt_one (n d r : ℕ) (hd : 0 < d)
    (h : (d : ℝ) ^ (r - 1) < (n.choose r : ℝ)) :
    1 < rWayExpectation n d r := by
  rw [rWayExpectation, one_lt_div (by positivity : (0 : ℝ) < ↑d ^ (r - 1))]
  exact h

/-- The threshold scales as d^((r-1)/r): when n is large enough that
    C(n,r) > d^(r-1), collisions are expected. Since C(n,r) ≈ n^r/r!,
    the threshold is n ≈ (r!·d^(r-1))^(1/r).

    For r=2: (2!·d)^(1/2) = √(2d), the classical birthday threshold. -/
theorem threshold_characterization (n d r : ℕ) (hd : 0 < d)
    (h : (r.factorial : ℝ) * (d : ℝ) ^ (r - 1) < ((n + 1 - r : ℕ) : ℝ) ^ r) :
    1 < rWayExpectation n d r := by
  apply rWayExpectation_gt_one n d r hd
  have hr_pos : (0 : ℝ) < r.factorial := by positivity
  calc (d : ℝ) ^ (r - 1)
      < ((n + 1 - r : ℕ) : ℝ) ^ r / ↑r.factorial := by
          rwa [lt_div_iff hr_pos, mul_comm]
    _ ≤ (n.choose r : ℝ) := Nat.pow_le_choose r n

end BirthdayRWay

#check BirthdayRWay.rWayExpectation
#check BirthdayRWay.rWay_pairwise
#check BirthdayRWay.rWayExpectation_upper
#check BirthdayRWay.rWayExpectation_lower
#check BirthdayRWay.rWayExpectation_gt_one
#check BirthdayRWay.threshold_characterization
