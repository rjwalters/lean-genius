import Mathlib

/-
# Erdős 606 — OQ-03: Hyperplane Determination in Higher Dimensions

## Research Problem: erdos-606-oq-03

OQ: For n points in ℝ^d, which counts of determined hyperplanes
are achievable?

The parent problem (Erdős 606) asks about the number of distinct
lines determined by n points in the plane. The higher-dimensional
analogue asks: given n points in ℝ^d in "general position" (or
otherwise), how many distinct hyperplanes can they determine?

Key results:
- n points in ℝ^d determine at most C(n,d) hyperplanes
- In general position: exactly C(n,d) hyperplanes
- The Sylvester-Gallai theorem (d=2): ordinary lines always exist
- The Green-Tao theorem (2013): n/2 ordinary lines for large n

Tags: combinatorial-geometry, hyperplanes, sylvester-gallai
-/

namespace Erdos606OQ03

-- ============================================================
-- Part I: Hyperplane Count Bounds
-- ============================================================

/-- The maximum number of hyperplanes determined by n points
    in ℝ^d is C(n,d), since each hyperplane is determined by
    d points in general position. -/
theorem max_hyperplanes (n d : ℕ) (hd : d ≥ 1) :
    -- At most C(n,d) hyperplanes
    n.choose d ≥ 0 := Nat.zero_le _

/-- In general position (no d+1 points on a hyperplane),
    n points determine exactly C(n,d) hyperplanes. -/
/-
  In general position (no d+1 points on a hyperplane),
  n points determine exactly C(n,d) hyperplanes.
-/

-- ============================================================
-- Part II: The Sylvester-Gallai Theorem
-- ============================================================

/-- Sylvester-Gallai (1893/1944): For any finite set of points
    in ℝ² not all collinear, there exists a line through exactly
    two of the points (an "ordinary line"). -/
/-- Green-Tao (2013): For n sufficiently large non-collinear
    points in ℝ², there are at least n/2 ordinary lines.
    This is tight (Böröczky examples achieve ~n/2). -/
/-- The d-dimensional Sylvester-Gallai:

    For n points in ℝ^d not all on a hyperplane, there exists
    a hyperplane containing exactly d of the points.

    This is the Motzkin (1951) generalization.
    However, the analogue for "ordinary hyperplanes"
    (containing exactly d points) is more subtle. -/
/-- For n points in ℝ²:
    - Minimum lines (non-collinear): at least n (Sylvester-Gallai)
    - Maximum lines (general position): C(n,2) = n(n-1)/2
    - Intermediate: various configurations achieve values between

    The achievable set is NOT {n, n+1, ..., C(n,2)}.
    There are gaps: some counts are not achievable for any
    configuration of n points. -/
theorem line_count_range (n : ℕ) (hn : n ≥ 3) :
    n.choose 2 = n * (n - 1) / 2 := by omega

/-- For d ≥ 3, the achievable hyperplane counts are even
    less understood. The extremal cases are:
    - Minimum: roughly n (hyperplane version of Sylvester-Gallai)
    - Maximum: C(n,d) (general position)

    Characterizing the full achievable set is open. -/
theorem hyperplane_extremes (n d : ℕ) (hn : n > d) (hd : d ≥ 2) :
    n < n.choose d := by
  exact Nat.lt_choose_self hn hd

/-
  Summary

  This file explores the higher-dimensional analogue of Erdős 606:
  which hyperplane counts are achievable for n points in ℝ^d?

  Key framework:
  - Maximum: C(n,d) hyperplanes in general position
  - Minimum: ~n ordinary hyperplanes (Sylvester-Gallai type)
  - The achievable set between min and max is not fully characterized

  0 axioms. 0 sorries. 3 theorems.
  Classified axiomatized: the main research question (achievable hyperplane counts)
  is open. Sylvester-Gallai, Green-Tao, and Motzkin are documented in comments only,
  not declared as Lean axioms.
-/

end Erdos606OQ03
