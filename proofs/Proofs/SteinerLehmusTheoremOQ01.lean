import Mathlib.Tactic

/-!
# The Steiner–Lehmus theorem (steiner-lehmus-theorem-oq-01)

If a triangle has two **internal angle bisectors of equal length**, then it is isosceles.
Concretely, if the bisectors drawn from vertices `B` and `C` have the same length, then the
sides opposite to them are equal, `b = c`.

We work with the algebraic core of the theorem. Writing `a, b, c > 0` for the side lengths of
the triangle, the squared length of the internal bisector from `B` (which meets side `b = CA`)
is given by the classical bisector-length formula

    w_b² = a·c·(1 - (b / (a + c))²),

and symmetrically `w_c² = a·b·(1 - (c / (a + b))²)`. The Steiner–Lehmus theorem reduces to the
purely algebraic implication

    w_b² = w_c²  ⟹  b = c        (for positive reals `a, b, c`).

The decisive fact is the exact factorisation

    w_b² - w_c²
      = -a·(b - c)·(a + b + c)·(a³ + a²b + a²c + 3abc + b²c + bc²) / ((a + b)² (a + c)²),

in which the polynomial cofactor
`a·(a + b + c)·(a³ + a²b + a²c + 3abc + b²c + bc²)` is **strictly positive** for positive
`a, b, c` (every monomial is positive). Hence `w_b² = w_c²` forces `b - c = 0`.

The argument is elementary real algebra: clear denominators, expose the factorisation with
`linear_combination`/`ring`, and finish with positivity. No triangle inequality is even needed —
positivity of the three side lengths suffices. The proof is fully machine-checked, with no
axioms and no `sorry`.

Not a named Mathlib result.
-/

namespace SteinerLehmusTheoremOQ01

/-- Squared length of the internal angle bisector from the vertex opposite side `b`, i.e. the
bisector from `B` meeting side `CA`, expressed through the classical formula
`w_b² = a·c·(1 - (b/(a+c))²)`. -/
noncomputable def bisectorSq (a b c : ℝ) : ℝ := a * c * (1 - (b / (a + c)) ^ 2)

/-- The squared bisector length, after clearing the denominator `(a + c)²`. Used to turn the
hypothesis into a polynomial identity. -/
theorem bisectorSq_clear (a b c : ℝ) (hac : a + c ≠ 0) :
    bisectorSq a b c * (a + c) ^ 2 = a * c * ((a + c) ^ 2 - b ^ 2) := by
  unfold bisectorSq
  field_simp

/-- **Steiner–Lehmus (algebraic core).** For positive side lengths `a, b, c`, equal internal
bisector lengths from `B` and `C` force the opposite sides to be equal, `b = c`. -/
theorem steiner_lehmus (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (heq : bisectorSq a b c = bisectorSq a c b) : b = c := by
  have hac : a + c ≠ 0 := by positivity
  have hab : a + b ≠ 0 := by positivity
  -- Clear both denominators: the hypothesis becomes a polynomial equation.
  have hcleared :
      a * c * ((a + c) ^ 2 - b ^ 2) * (a + b) ^ 2
        = a * b * ((a + b) ^ 2 - c ^ 2) * (a + c) ^ 2 := by
    have hB : bisectorSq a b c * (a + c) ^ 2 = a * c * ((a + c) ^ 2 - b ^ 2) :=
      bisectorSq_clear a b c hac
    have hC : bisectorSq a c b * (a + b) ^ 2 = a * b * ((a + b) ^ 2 - c ^ 2) :=
      bisectorSq_clear a c b hab
    have key : (bisectorSq a b c) * ((a + c) ^ 2 * (a + b) ^ 2)
        = (bisectorSq a c b) * ((a + c) ^ 2 * (a + b) ^ 2) := by rw [heq]
    linear_combination (-(a + b) ^ 2) * hB + (a + c) ^ 2 * hC + key
  -- Exact factorisation: w_b² - w_c² ∝ (b - c) times a positive cofactor.
  have hfact :
      (b - c) * (a * (a + b + c) *
        (a ^ 3 + a ^ 2 * b + a ^ 2 * c + 3 * a * b * c + b ^ 2 * c + b * c ^ 2)) = 0 := by
    linear_combination (-1 : ℝ) * hcleared
  -- The cofactor is strictly positive, so the factor `b - c` must vanish.
  have hpos : 0 < a * (a + b + c) *
      (a ^ 3 + a ^ 2 * b + a ^ 2 * c + 3 * a * b * c + b ^ 2 * c + b * c ^ 2) := by
    positivity
  have hbc : b - c = 0 := by
    rcases mul_eq_zero.mp hfact with h | h
    · exact h
    · exact absurd h (ne_of_gt hpos)
  linarith

end SteinerLehmusTheoremOQ01
