import Mathlib
import Proofs.TetrahedralNumberFormulaOQ01

/-!
# Tetrahedral / simplex numbers (OQ-01, companion): the multiplicative column recurrence

The parent file `TetrahedralNumberFormulaOQ01.lean` develops the figurate ("simplex")
numbers `P_d(n) = C(n+d, d)` with their **additive** structure — Pascal's rule
(`simplexNumber_succ_succ`), the hockey-stick sums (`sum_simplex`,
`sum_simplex_over_dim`), reflection symmetry, and the ascending-factorial closed form
`d! · P_d(n) = (n+1)(n+2)⋯(n+d)`.

This companion supplies the complementary **multiplicative** structure — the *absorption*
(committee/column) recurrences that relate neighbouring entries by a ratio rather than a
sum:

* `simplexNumber_absorption` — raising the **dimension**:
  `(n+d+1) · P_d(n) = (d+1) · P_{d+1}(n)`, i.e. `P_{d+1}(n)/P_d(n) = (n+d+1)/(d+1)`.
  This is the figurate form of the binomial absorption identity
  `Nat.succ_mul_choose_eq`.
* `simplexNumber_size_absorption` — raising the **size**:
  `(n+d+1) · P_d(n) = (n+1) · P_d(n+1)`, the same recurrence read along the size axis,
  obtained from the dimension form through the reflection symmetry
  `simplexNumber_symm` (mirroring the parent's `sum_simplex` / `sum_simplex_over_dim`
  pairing).
* `simplexNumber_diag` — the **central simplex number** on the `d = n` diagonal of
  Pascal's simplex is the central binomial coefficient: `P_d(d) = C(2d, d)`.

Together with Pascal's rule these determine the whole simplex table by pure
multiplication/division, and specialise (at `d = 2, 3`) to the classical
triangular/tetrahedral growth ratios. All results are `0`-sorry / `0`-axiom on top of
Mathlib and the parent file.
-/

namespace TetrahedralNumberFormulaOQ01

open Finset Nat

/-- **Dimension absorption (column recurrence).**  Neighbouring dimensions are related
by a ratio: `(n+d+1) · P_d(n) = (d+1) · P_{d+1}(n)`, equivalently
`P_{d+1}(n) = P_d(n) · (n+d+1)/(d+1)`.  This is the figurate reading of the binomial
absorption identity `Nat.succ_mul_choose_eq`, and the multiplicative counterpart of the
additive Pascal rule `simplexNumber_succ_succ`. -/
theorem simplexNumber_absorption (d n : ℕ) :
    (n + d + 1) * simplexNumber d n = (d + 1) * simplexNumber (d + 1) n := by
  have key := Nat.succ_mul_choose_eq (n + d) d
  simp only [Nat.succ_eq_add_one] at key
  unfold simplexNumber
  rw [show n + (d + 1) = n + d + 1 from by ring, key]
  ring

/-- **Size absorption (row recurrence).**  Read along the size axis:
`(n+d+1) · P_d(n) = (n+1) · P_d(n+1)`.  Obtained from `simplexNumber_absorption` through
the reflection symmetry `P_d(n) = P_n(d)` — the multiplicative analogue of how
`sum_simplex_over_dim` mirrors `sum_simplex`. -/
theorem simplexNumber_size_absorption (d n : ℕ) :
    (n + d + 1) * simplexNumber d n = (n + 1) * simplexNumber d (n + 1) := by
  rw [simplexNumber_symm d n, simplexNumber_symm d (n + 1), Nat.add_comm n d]
  exact simplexNumber_absorption n d

/-- **Central simplex number.**  On the diagonal `d = n` of Pascal's simplex the figurate
number is the central binomial coefficient: `P_d(d) = C(2d, d)`. -/
theorem simplexNumber_diag (d : ℕ) : simplexNumber d d = (2 * d).choose d := by
  unfold simplexNumber
  rw [two_mul]

end TetrahedralNumberFormulaOQ01
