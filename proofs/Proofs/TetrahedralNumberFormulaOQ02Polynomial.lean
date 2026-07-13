import Proofs.TetrahedralNumberFormulaOQ02
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Eval.Defs

/-
# The Figurate-Sum Cleared Form as a First-Class Monic Polynomial

## Open Question (tetrahedral-number-formula-oq-02, polynomial follow-up)

The companion file `TetrahedralNumberFormulaOQ02` proves the uniform
cleared-denominator identity

    (d+1)! · S_d(n) = ∏_{i<d+1} (n+1+i)          (`factorial_mul_sum_simplex`)

where `S_d(n) = ∑_{k≤n} P_d(k)` is the running total of the `d`-dimensional
figurate row.  There the right-hand side is a *product expression* in `ℕ`,
described informally in the docstring as "a monic polynomial of degree `d+1` in
`n`".  This entry makes that description **literal**: it packages the cleared
form as a genuine `Polynomial ℤ`

    Q_d(X) = ∏_{i<d+1} (X + (i+1)) = (X+1)(X+2)⋯(X+d+1)        (`figuratePoly`)

and proves its three structural properties as a polynomial.

## Result

* `figuratePoly_monic` : `Q_d` is **monic** — a product of monic linear factors.

* `figuratePoly_natDegree` : `Q_d` has **degree exactly `d+1`**, the sum of the
  `d+1` unit degrees of its linear factors.

* `figuratePoly_eval` : the **bridge to the arithmetic** — evaluating `Q_d` at an
  integer point `n` recovers the cleared figurate sum,
  `Q_d(n) = (d+1)! · S_d(n)`.  This ties the abstract polynomial back to the
  `ℕ`-identity `factorial_mul_sum_simplex`.

* `figuratePoly_factorial_dvd_eval` : the integrality content read off the
  polynomial — `(d+1)! ∣ Q_d(n)` for every integer `n`.

## Novelty

`OQ02` states the cleared form only as an equation between natural numbers; the
"polynomial of degree `d+1`" is prose.  Here the object is a first-class
`Polynomial ℤ` whose monicity and degree are theorems, and whose evaluation map
is proved to reproduce the figurate partial sum.  This is the Mathlib-native
`Polynomial` upgrade flagged as the sole remaining `nextStep` of `OQ02`.

0 sorries, 0 axioms.
-/

namespace TetrahedralNumberFormulaOQ02

open Finset Polynomial TetrahedralNumberFormulaOQ01

/-- The **figurate-sum cleared-form polynomial**
`Q_d(X) = ∏_{i<d+1} (X + (i+1)) = (X+1)(X+2)⋯(X+d+1)`, the `Polynomial ℤ` whose
value at `n` is `(d+1)! · S_d(n)`. -/
noncomputable def figuratePoly (d : ℕ) : Polynomial ℤ :=
  ∏ i ∈ range (d + 1), (X + C ((i : ℤ) + 1))

/-- `Q_d` is **monic**: a finite product of the monic linear factors `X + (i+1)`. -/
theorem figuratePoly_monic (d : ℕ) : (figuratePoly d).Monic :=
  monic_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)

/-- `Q_d` has **degree exactly `d+1`**: the sum of the `d+1` unit degrees of its
monic linear factors. -/
theorem figuratePoly_natDegree (d : ℕ) : (figuratePoly d).natDegree = d + 1 := by
  rw [figuratePoly, natDegree_prod_of_monic _ _ (fun _ _ => monic_X_add_C _)]
  simp only [natDegree_X_add_C, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]

/-- **Evaluation bridge.** Evaluating the cleared-form polynomial at the integer
point `n` returns the cleared figurate sum: `Q_d(n) = (d+1)! · S_d(n)`. This is
the `Polynomial`-level restatement of `factorial_mul_sum_simplex`. -/
theorem figuratePoly_eval (d n : ℕ) :
    (figuratePoly d).eval (n : ℤ)
      = ((Nat.factorial (d + 1) * figurateSum d n : ℕ) : ℤ) := by
  have hnat := factorial_mul_sum_simplex d n
  rw [figuratePoly, eval_prod]
  have hcast : ∀ i ∈ range (d + 1),
      (X + C ((i : ℤ) + 1)).eval (n : ℤ) = ((n + 1 + i : ℕ) : ℤ) := by
    intro i _
    simp only [eval_add, eval_X, eval_C]
    push_cast
    ring
  rw [Finset.prod_congr rfl hcast, ← Nat.cast_prod, ← hnat]

/-- **Integrality, read off the polynomial.** `(d+1)!` divides the value of the
cleared-form polynomial at every integer point `n`, since that value is exactly
`(d+1)! · S_d(n)`. -/
theorem figuratePoly_factorial_dvd_eval (d n : ℕ) :
    ((Nat.factorial (d + 1) : ℤ)) ∣ (figuratePoly d).eval (n : ℤ) := by
  rw [figuratePoly_eval, Nat.cast_mul]
  exact Dvd.intro _ rfl

end TetrahedralNumberFormulaOQ02
