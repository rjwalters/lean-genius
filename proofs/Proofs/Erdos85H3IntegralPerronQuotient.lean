import Mathlib

/-!
The eight integer coefficient quotients for the proposed H3 defect partition
10+12+24 contradict the required square-trace. Only the final matrix algebra
is formalized here; graph-to-Perron reduction and coefficient restrictions
are separate paper arguments.
-/
namespace Erdos85

/-- Quotient after the cross-entry integrality restrictions and row sum `a`. -/
def h3IntegralComponentQuotient (a : ℝ) (x : Fin 2) (y : Fin 4) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  let X : ℝ := x.val
  let Y : ℝ := y.val
  !![X + (1-X)*a, X*(a-1), 0;
     X*(a-2), 2*X-2*Y+(1-X)*a, 2*Y;
     0, Y, a-Y]

/-- Each possible quotient has too large a square-trace for eigenvalue `a`
and a two-dimensional complementary restriction whose square is `(7-a)I`. -/
theorem h3IntegralComponentQuotient_trace_sq_gt
    (a : ℝ) (ha : 6 < a) (hpoly : a^2 - 7*a + 3 = 0)
    (x : Fin 2) (y : Fin 4) :
    a^2 + 2*(7-a) < Matrix.trace
      (h3IntegralComponentQuotient a x y * h3IntegralComponentQuotient a x y) := by
  have hau : a < 7 := by nlinarith [sq_nonneg (a-7)]
  fin_cases x <;> fin_cases y <;>
    norm_num [h3IntegralComponentQuotient, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_succ] <;> nlinarith

/-- The required spectral square-trace cannot hold for any of the eight quotients. -/
theorem h3IntegralComponentQuotient_trace_sq_ne
    (a : ℝ) (ha : 6 < a) (hpoly : a^2 - 7*a + 3 = 0)
    (x : Fin 2) (y : Fin 4) :
    Matrix.trace
      (h3IntegralComponentQuotient a x y * h3IntegralComponentQuotient a x y)
        ≠ a^2 + 2*(7-a) :=
  ne_of_gt (h3IntegralComponentQuotient_trace_sq_gt a ha hpoly x y)

end Erdos85
