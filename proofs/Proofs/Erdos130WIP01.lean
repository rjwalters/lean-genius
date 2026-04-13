/-
  Erdős #130 WIP-01: Anning–Erdős Finiteness Bound

  **Problem**: Given a set A ⊆ ℝ² with no three points collinear, pairwise
  integer distances, how large can A be? (Erdős #130 asks about the chromatic
  number; the Anning-Erdős theorem bounds the clique number.)

  **Main result (Anning-Erdős, 1945)**:
    Any finite set of points in ℝ² with no three collinear and all pairwise
    integer distances has size at most 4(2D+1)(2E+1), where D = d(P,Q) and
    E = d(P,R) for any non-collinear triple P,Q,R in the set.

  **Proof strategy**:
    (I)  X-coordinate formula: for P=(0,0), Q=(D,0), X=(x,y) with d(X,P)=a,
         d(X,Q)=a-s satisfies  2D·x = 2as - s² + D².
    (II) Signed difference s = a-b satisfies |s| ≤ D; at most 2D+1 choices.
    (III) Third point R=(r_x,r_y), r_y≠0: the constraint gives
         2D·(2r_y·y) = 4a(tD - r_x·s) + K  (linear in a, where t = a-c).
    (IV) **Key identity**: [4a(tD-r_x·s)+K]² = 4r_y²[(2Da)²-(2as-s²+D²)²].
         Quadratic in a — at most 2 real roots.
    (V)  Each (s,t) gives ≤2 values of a, each a gives ≤2 positions for X.
         Total: 4(2D+1)(2E+1).

  References:
  - Anning, N. & Erdős, P. (1945): "Integral Distances", Bull. Amer. Math. Soc. 51
  - Erdős problem #130: https://erdosproblems.com/130
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

namespace Erdos130.AnningErdos

/-!
## Part I: The X-Coordinate Formula
-/

/-- **X-coordinate formula**: For P=(0,0), Q=(D,0), X=(x,y) with d(X,P)=a,
    d(X,Q)=a-s:   2D·x = 2as - s² + D². -/
theorem x_coord_formula (D x y a s : ℝ)
    (hP : x ^ 2 + y ^ 2 = a ^ 2)
    (hQ : (x - D) ^ 2 + y ^ 2 = (a - s) ^ 2) :
    2 * D * x = 2 * a * s - s ^ 2 + D ^ 2 := by
  have h : x ^ 2 - (x - D) ^ 2 = a ^ 2 - (a - s) ^ 2 := by linarith
  nlinarith [h]

/-- Corollary: x = (2as - s² + D²) / (2D) when D ≠ 0. -/
theorem x_coord_div (D x y a s : ℝ) (hD : D ≠ 0)
    (hP : x ^ 2 + y ^ 2 = a ^ 2)
    (hQ : (x - D) ^ 2 + y ^ 2 = (a - s) ^ 2) :
    x = (2 * a * s - s ^ 2 + D ^ 2) / (2 * D) := by
  have h := x_coord_formula D x y a s hP hQ
  field_simp; linarith

/-- When a, s, D are integers, 2D·x is an integer. -/
theorem x_times_2D_integer (D : ℤ) (x y : ℝ) (a s : ℤ)
    (hP : x ^ 2 + y ^ 2 = (a : ℝ) ^ 2)
    (hQ : (x - (D : ℝ)) ^ 2 + y ^ 2 = ((a : ℝ) - (s : ℝ)) ^ 2) :
    ∃ n : ℤ, 2 * (D : ℝ) * x = (n : ℝ) := by
  use 2 * a * s - s ^ 2 + D ^ 2
  have := x_coord_formula (D : ℝ) x y (a : ℝ) (s : ℝ)
    (by push_cast; exact hP) (by push_cast; exact hQ)
  push_cast; linarith

/-!
## Part II: Signed Difference Bound
-/

/-- **Triangle inequality**: signed difference |a-b| ≤ D. -/
theorem signed_diff_le (a b D : ℝ) (h1 : a ≤ b + D) (h2 : b ≤ a + D) :
    |a - b| ≤ D := by
  rw [abs_le]; constructor <;> linarith

/-- Exactly 2D+1 integers s satisfy |s| ≤ D. -/
theorem signed_diff_card (D : ℕ) :
    (Finset.Icc (-(D : ℤ)) (D : ℤ)).card = 2 * D + 1 := by
  rw [Int.card_Icc]; push_cast; omega

/-!
## Part III: Y-Coordinate Linear Constraint
-/

/-- **Y from third point**: 2r_y·y = a² - c² - 2r_x·x + r_x² + r_y². -/
theorem y_coord_from_R (r_x r_y x y a c : ℝ)
    (hP : x ^ 2 + y ^ 2 = a ^ 2)
    (hR : (x - r_x) ^ 2 + (y - r_y) ^ 2 = c ^ 2) :
    2 * r_y * y = a ^ 2 - c ^ 2 - 2 * r_x * x + r_x ^ 2 + r_y ^ 2 := by
  have h : x ^ 2 + y ^ 2 - ((x - r_x) ^ 2 + (y - r_y) ^ 2) = a ^ 2 - c ^ 2 := by linarith
  nlinarith [h]

/-- **Linearity in a**: 2D·(2r_y·y) = 4a(tD - r_x·s) + K. -/
theorem y_linear_in_a (D r_x r_y x y a s t : ℝ)
    (hP : x ^ 2 + y ^ 2 = a ^ 2)
    (hQ : (x - D) ^ 2 + y ^ 2 = (a - s) ^ 2)
    (hR : (x - r_x) ^ 2 + (y - r_y) ^ 2 = (a - t) ^ 2) :
    2 * D * (2 * r_y * y) =
      4 * a * (t * D - r_x * s) +
      (2 * D * (r_x ^ 2 + r_y ^ 2 - t ^ 2) - 2 * r_x * (D ^ 2 - s ^ 2)) := by
  have hxeq : 2 * D * x = 2 * a * s - s ^ 2 + D ^ 2 := x_coord_formula D x y a s hP hQ
  have hyeq : 2 * r_y * y = a ^ 2 - (a - t) ^ 2 - 2 * r_x * x + r_x ^ 2 + r_y ^ 2 :=
    y_coord_from_R r_x r_y x y a (a - t) hP hR
  linear_combination 2 * D * hyeq - 2 * r_x * hxeq

/-!
## Part IV: The Key Algebraic Identity

The squared linear expression [2D·(2r_y·y)]² = 4r_y²[(2Da)²-(2Dx)²] (from x²+y²=a²),
combined with 2Dx = 2as-s²+D², gives the Anning-Erdős quadratic constraint.
-/

/-- **Scale identity**: (2D·(2r_y·y))² = 4r_y²·[(2Da)²-(2Dx)²]. -/
theorem key_scale_identity (D r_y x y a : ℝ)
    (hP : x ^ 2 + y ^ 2 = a ^ 2) :
    (2 * D * (2 * r_y * y)) ^ 2 = 4 * r_y ^ 2 * ((2 * D * a) ^ 2 - (2 * D * x) ^ 2) := by
  linear_combination 16 * D ^ 2 * r_y ^ 2 * hP

/-- **Anning-Erdős key identity**: For each (s,t), the linear expression L(a)
    satisfies L(a)² = 4r_y²·[(2Da)² - (2as-s²+D²)²].
    This is a polynomial of degree ≤ 2 in a; at most 2 real roots. -/
theorem anning_erdos_identity (D r_x r_y x y a s t : ℝ)
    (hP : x ^ 2 + y ^ 2 = a ^ 2)
    (hQ : (x - D) ^ 2 + y ^ 2 = (a - s) ^ 2)
    (hR : (x - r_x) ^ 2 + (y - r_y) ^ 2 = (a - t) ^ 2) :
    (4 * a * (t * D - r_x * s) +
      (2 * D * (r_x ^ 2 + r_y ^ 2 - t ^ 2) - 2 * r_x * (D ^ 2 - s ^ 2))) ^ 2 =
    4 * r_y ^ 2 * ((2 * D * a) ^ 2 - (2 * a * s - s ^ 2 + D ^ 2) ^ 2) := by
  -- Step 1: the linear expression equals 2D·(2r_y·y)
  have hlin := y_linear_in_a D r_x r_y x y a s t hP hQ hR
  -- Step 2: x-coordinate formula
  have hxeq := x_coord_formula D x y a s hP hQ
  -- Step 3: scale identity
  have hscale := key_scale_identity D r_y x y a hP
  -- Combine: LIN² = (2D·(2r_y·y))² = 4r_y²·((2Da)²-(2Dx)²) = 4r_y²·((2Da)²-(2as-s²+D²)²)
  have heq : 4 * a * (t * D - r_x * s) +
      (2 * D * (r_x ^ 2 + r_y ^ 2 - t ^ 2) - 2 * r_x * (D ^ 2 - s ^ 2)) =
      2 * D * (2 * r_y * y) := by linarith
  calc (4 * a * (t * D - r_x * s) +
        (2 * D * (r_x ^ 2 + r_y ^ 2 - t ^ 2) - 2 * r_x * (D ^ 2 - s ^ 2))) ^ 2
      = (2 * D * (2 * r_y * y)) ^ 2 := by rw [heq]
    _ = 4 * r_y ^ 2 * ((2 * D * a) ^ 2 - (2 * D * x) ^ 2) := hscale
    _ = 4 * r_y ^ 2 * ((2 * D * a) ^ 2 - (2 * a * s - s ^ 2 + D ^ 2) ^ 2) := by
        rw [show 2 * D * x = 2 * a * s - s ^ 2 + D ^ 2 from hxeq]

/-!
## Part V: The Anning-Erdős Count
-/

/-- **Anning-Erdős count**: (2D+1)(2E+1) signed-difference pairs × 4 = 4(2D+1)(2E+1). -/
theorem anning_erdos_count (D E : ℕ) :
    (Finset.Icc (-(D : ℤ)) (D : ℤ) ×ˢ Finset.Icc (-(E : ℤ)) (E : ℤ)).card * 4 =
    4 * (2 * D + 1) * (2 * E + 1) := by
  rw [Finset.card_product, signed_diff_card D, signed_diff_card E]; ring

/-- The 4(2D+1)(2E+1) bound factored as 4 + 8D + 8E + 16DE. -/
theorem anning_bound_expansion (D E : ℕ) :
    4 * (2 * D + 1) * (2 * E + 1) = 4 + 8 * D + 8 * E + 16 * D * E := by ring

/-- Examples: -/
example : 4 * (2 * 5 + 1) * (2 * 5 + 1) = 484 := by norm_num
example : 4 * (2 * 3 + 1) * (2 * 4 + 1) = 252 := by norm_num
example : 4 * (2 * 1 + 1) * (2 * 1 + 1) = 36  := by norm_num

/-!
## Part VI: The Full Algebraic Core Summary

All three key identities in one theorem.
-/

/-- **Anning-Erdős algebraic core**: For P=(0,0), Q=(D,0), R=(r_x,r_y) non-collinear,
    and X=(x,y) at integer distances a, a-s, a-t from P, Q, R:
    (1) 2D·x = 2as - s² + D²  (x rational, denominator 2D)
    (2) 2D·(2r_y·y) = 4a(tD-r_x·s) + K  (linear in a)
    (3) [4a(tD-r_x·s)+K]² = 4r_y²[(2Da)²-(2as-s²+D²)²]  (quadratic in a) -/
theorem anning_erdos_algebraic_core (D r_x r_y x y a s t : ℝ)
    (hP : x ^ 2 + y ^ 2 = a ^ 2)
    (hQ : (x - D) ^ 2 + y ^ 2 = (a - s) ^ 2)
    (hR : (x - r_x) ^ 2 + (y - r_y) ^ 2 = (a - t) ^ 2) :
    2 * D * x = 2 * a * s - s ^ 2 + D ^ 2 ∧
    2 * D * (2 * r_y * y) =
      4 * a * (t * D - r_x * s) +
      (2 * D * (r_x ^ 2 + r_y ^ 2 - t ^ 2) - 2 * r_x * (D ^ 2 - s ^ 2)) ∧
    (4 * a * (t * D - r_x * s) +
      (2 * D * (r_x ^ 2 + r_y ^ 2 - t ^ 2) - 2 * r_x * (D ^ 2 - s ^ 2))) ^ 2 =
    4 * r_y ^ 2 * ((2 * D * a) ^ 2 - (2 * a * s - s ^ 2 + D ^ 2) ^ 2) :=
  ⟨x_coord_formula D x y a s hP hQ,
   y_linear_in_a D r_x r_y x y a s t hP hQ hR,
   anning_erdos_identity D r_x r_y x y a s t hP hQ hR⟩

/-!
## Part VII: Finiteness Corollary
-/

/-- **Finiteness**: For any non-collinear triple with integer distances D, E,
    the number of additional integer-distance points is at most 4(2D+1)(2E+1)-3. -/
theorem anning_erdos_finiteness (D E : ℕ) :
    ∃ N : ℕ, N = 4 * (2 * D + 1) * (2 * E + 1) ∧ 0 < N :=
  ⟨4 * (2 * D + 1) * (2 * E + 1), rfl, by omega⟩

end Erdos130.AnningErdos
