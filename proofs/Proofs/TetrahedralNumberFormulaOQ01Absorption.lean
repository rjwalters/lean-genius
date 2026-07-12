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
  have key := Nat.add_one_mul_choose_eq (n + d) d
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

/-- **Central simplex-number doubling recurrence.**  Along the diagonal `d = n` the
figurate number is the central binomial coefficient `P_d(d) = C(2d, d)`
(`simplexNumber_diag`), and successive diagonal entries obey the central binomial
recurrence

`(d+1) · P_{d+1}(d+1) = 2·(2d+1) · P_d(d)`.

Equivalently `P_{d+1}(d+1)/P_d(d) = 2(2d+1)/(d+1)`, the exact growth ratio of the
central binomials `C(2d,d)` (which underlies their `4^d/√(πd)` asymptotics and the
Catalan numbers `C(2d,d)/(d+1)`). Immediate from Mathlib's
`Nat.succ_mul_centralBinom_succ` once `simplexNumber_diag` identifies the diagonal with
`Nat.centralBinom`. This is the diagonal companion of the off-diagonal absorption
recurrences `simplexNumber_absorption` / `simplexNumber_size_absorption`. -/
theorem simplexNumber_diag_succ (d : ℕ) :
    (d + 1) * simplexNumber (d + 1) (d + 1) = 2 * (2 * d + 1) * simplexNumber d d := by
  rw [simplexNumber_diag (d + 1), simplexNumber_diag d]
  exact Nat.succ_mul_centralBinom_succ d

/-- **Catalan numbers on the diagonal.**  The `d`-th Catalan number is the central simplex
number `P_d(d) = C(2d, d)` divided by `d+1`; multiplicatively,
`(d+1) · catalan d = P_d(d)`.  Since `simplexNumber_diag` identifies the diagonal of
Pascal's simplex with the central binomial coefficient `Nat.centralBinom`, this is just
Mathlib's `Nat.succ_mul_catalan_eq_centralBinom` read through that identification.  It
places the Catalan numbers `catalan d = C(2d,d)/(d+1)` inside the figurate ladder as the
`(d+1)`-quotient of the central simplex diagonal, complementing the diagonal doubling
recurrence `simplexNumber_diag_succ`. -/
theorem simplexNumber_diag_catalan (d : ℕ) :
    (d + 1) * catalan d = simplexNumber d d := by
  rw [simplexNumber_diag d, ← Nat.centralBinom_eq_two_mul_choose]
  exact succ_mul_catalan_eq_centralBinom d


/-- **The central simplex diagonal is Mathlib's central binomial coefficient.**  The
explicit bridge `P_d(d) = Nat.centralBinom d`, making the identification behind
`simplexNumber_diag` reusable with Mathlib's `Nat.centralBinom` API (growth bounds,
positivity, Bertrand's postulate, …). -/
theorem simplexNumber_diag_eq_centralBinom (d : ℕ) :
    simplexNumber d d = Nat.centralBinom d := by
  rw [simplexNumber_diag d, ← Nat.centralBinom_eq_two_mul_choose]

/-- **Exponential lower bound on the central simplex diagonal.**  For `d ≥ 4`,
`4^d < d · P_d(d)`.  Via `simplexNumber_diag_eq_centralBinom` this is exactly Mathlib's
`Nat.four_pow_lt_mul_centralBinom`, and it makes precise the docstring remark that the
diagonal drives the `4^d/√(πd)` central-binomial growth. -/
theorem four_pow_lt_diag {d : ℕ} (hd : 4 ≤ d) :
    4 ^ d < d * simplexNumber d d := by
  rw [simplexNumber_diag_eq_centralBinom d]
  exact Nat.four_pow_lt_mul_centralBinom d hd

/-- **Exponential lower bound valid for every positive dimension.**  `4^d ≤ 2d · P_d(d)`
for all `d ≥ 1` — the (weaker but hypothesis-light) diagonal reading of
`Nat.four_pow_le_two_mul_self_mul_centralBinom`, the bound appearing in Erdős's proof of
Bertrand's postulate. -/
theorem four_pow_le_two_mul_diag {d : ℕ} (hd : 0 < d) :
    4 ^ d ≤ 2 * d * simplexNumber d d := by
  rw [simplexNumber_diag_eq_centralBinom d]
  exact Nat.four_pow_le_two_mul_self_mul_centralBinom d hd

end TetrahedralNumberFormulaOQ01
