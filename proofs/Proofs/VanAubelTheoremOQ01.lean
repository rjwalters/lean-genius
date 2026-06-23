import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# van Aubel's theorem (van-aubel-theorem-oq-01)

Given an arbitrary planar quadrilateral with vertices `a, b, c, d` (modelled as complex
numbers), erect a square externally on each directed side and let `P, Q, R, S` be the four
square centers, one per side:

* `P = squareCenter a b` on side `a → b`,
* `Q = squareCenter b c` on side `b → c`,
* `R = squareCenter c d` on side `c → d`,
* `S = squareCenter d a` on side `d → a`.

van Aubel's theorem states that the two "diagonals" of the square-center quadrilateral,
`PR` and `QS`, are **equal in length** and **perpendicular**.

The whole statement collapses to a single algebraic identity over `ℂ`:

    R - P = i · (S - Q).                                  (`vanAubel_key`)

Multiplication by `i` is a `90°` rotation that preserves length, so this identity yields both
`‖PR‖ = ‖QS‖` (`vanAubel_equal_diagonals`) and `PR ⟂ QS`, encoded as the vanishing real part
of `(R - P) · conj (S - Q)` (`vanAubel_perp_diagonals`).

The key identity is purely a `ring` computation once `Complex.I_sq : I ^ 2 = -1` is supplied,
so the proof is fully machine-checked with no axioms and no `sorry`.

Not a named Mathlib result.
-/

namespace VanAubelTheoremOQ01

open Complex ComplexConjugate

/-- Center of the square erected externally on the directed edge `u → v`, using the `+90°`
rotation convention `i · (v - u)`. -/
noncomputable def squareCenter (u v : ℂ) : ℂ := (u + v) / 2 + I * (v - u) / 2

/-- **Key identity.** For any quadrilateral `a, b, c, d`, the diagonal vector `R - P` of the
square-center quadrilateral equals `i` times the diagonal vector `S - Q`. Everything else in
van Aubel's theorem follows from this single equation. -/
theorem vanAubel_key (a b c d : ℂ) :
    squareCenter c d - squareCenter a b
      = I * (squareCenter d a - squareCenter b c) := by
  unfold squareCenter
  linear_combination (-(a + b - c - d) / 2) * Complex.I_sq

/-- **Equal diagonals.** The segments `PR` and `QS` joining opposite square centers have equal
length. Immediate from `vanAubel_key` since multiplication by `i` is norm preserving. -/
theorem vanAubel_equal_diagonals (a b c d : ℂ) :
    ‖squareCenter c d - squareCenter a b‖ = ‖squareCenter d a - squareCenter b c‖ := by
  rw [vanAubel_key, norm_mul, Complex.norm_I, one_mul]

/-- **Perpendicular diagonals.** The segments `PR` and `QS` are orthogonal: the real part of
`(R - P) · conj (S - Q)` (the Euclidean inner product of the two vectors) vanishes. Immediate
from `vanAubel_key`, because `(i z) · conj z = i · ‖z‖²` is purely imaginary. -/
theorem vanAubel_perp_diagonals (a b c d : ℂ) :
    ((squareCenter c d - squareCenter a b) *
        conj (squareCenter d a - squareCenter b c)).re = 0 := by
  rw [vanAubel_key, mul_assoc, Complex.mul_conj]
  simp [Complex.I_mul_re, Complex.ofReal_im]

end VanAubelTheoremOQ01
