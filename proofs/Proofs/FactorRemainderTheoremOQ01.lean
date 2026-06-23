import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-!
# Factor–remainder theorem OQ-01: the multiplicity version via derivatives

The parent entry (`factor-remainder-theorem`) proves the Factor Theorem `(X − a) ∣ p ↔
p(a) = 0`. Its OQ-01 asks for the **multiplicity version**:

> *`(X − a)ᵏ ∣ p` iff `p(a) = p′(a) = ⋯ = p^{(k−1)}(a) = 0`* — connecting the Factor Theorem
> to Taylor expansion, requiring polynomial derivatives.

Over a field of characteristic zero, Mathlib proves exactly this through `rootMultiplicity`:
`(X − a)ᵏ ∣ p` iff `k ≤ rootMultiplicity a p` (`le_rootMultiplicity_iff`), and
`n < rootMultiplicity a p` iff the first `n` iterated derivatives vanish at `a`
(`lt_rootMultiplicity_iff_isRoot_iterate_derivative...`). Combining them gives the
multiplicity factor theorem. `0` axioms.

## Main results

* `pow_dvd_iff_iterate_derivative_eval_eq_zero` : `(X − a)ᵏ ∣ p ↔ ∀ m < k, p^{(m)}(a) = 0`
  (the OQ's target, for `p ≠ 0`, `k ≥ 1`, over a characteristic-zero field).
* `factor_theorem` : `(X − a) ∣ p ↔ p(a) = 0` (the `k = 1` base case).
* `double_root_iff` : `(X − a)² ∣ p ↔ p(a) = 0 ∧ p′(a) = 0` (the `k = 2` case).
-/

namespace FactorRemainderTheoremOQ01

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- In a characteristic-zero field, every factorial is a nonzerodivisor (it is a nonzero
    natural number cast into the field). -/
theorem factorial_mem_nonZeroDivisors (n : ℕ) :
    (n.factorial : K) ∈ nonZeroDivisors K := by
  rw [mem_nonZeroDivisors_iff_ne_zero]
  exact_mod_cast n.factorial_ne_zero

/-- **The multiplicity factor theorem.** Over a characteristic-zero field, for a nonzero
    polynomial `p` and `k ≥ 1`, the factor `(X − a)ᵏ` divides `p` if and only if `p` and its
    first `k − 1` derivatives all vanish at `a`:
    `(X − a)ᵏ ∣ p ↔ ∀ m < k, p^{(m)}(a) = 0`. -/
theorem pow_dvd_iff_iterate_derivative_eval_eq_zero {p : K[X]} (hp : p ≠ 0) {a : K} {k : ℕ}
    (hk : 1 ≤ k) :
    (X - C a) ^ k ∣ p ↔ ∀ m < k, (derivative^[m] p).eval a = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  rw [← le_rootMultiplicity_iff hp, Nat.add_one_le_iff,
    lt_rootMultiplicity_iff_isRoot_iterate_derivative_of_mem_nonZeroDivisors hp
      (factorial_mem_nonZeroDivisors n)]
  simp only [IsRoot.def, Nat.lt_succ_iff]

/-- **Factor Theorem** (`k = 1`): `(X − a) ∣ p ↔ p(a) = 0`. (Mathlib: `dvd_iff_isRoot`.) -/
theorem factor_theorem {p : K[X]} {a : K} : (X - C a) ∣ p ↔ p.eval a = 0 :=
  dvd_iff_isRoot

/-- **Double-root criterion** (`k = 2`): `(X − a)² ∣ p ↔ p(a) = 0 ∧ p′(a) = 0`. A polynomial
    has `a` as a root of multiplicity at least two iff both `p` and its derivative vanish
    there. -/
theorem double_root_iff {p : K[X]} (hp : p ≠ 0) {a : K} :
    (X - C a) ^ 2 ∣ p ↔ p.eval a = 0 ∧ (derivative p).eval a = 0 := by
  rw [pow_dvd_iff_iterate_derivative_eval_eq_zero hp (by norm_num)]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ m hm
    interval_cases m
    · simpa using h0
    · simpa using h1

end FactorRemainderTheoremOQ01
