import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-
# A Constructive (Computable) Sign-Variation Count for Descartes' Rule

*Open Question from DescartesRuleOfSignsOQ01*: Can the proof be made constructive
(using decidable instances), i.e. can the sign-variation bound of Descartes' Rule
be turned into something a machine can actually **compute**?

## The obstruction

Mathlib's `Polynomial.signVariations P` is, as a function of the *polynomial*,
**noncomputable** over the usual coefficient fields:

* `Polynomial.coeffList` is built from `P.degree` and `P.coeff`, which go through
  the `Finsupp`/`AddMonoidAlgebra` representation of polynomials and are not
  computable in general.
* over `ℝ` the sign map `SignType.sign : ℝ → SignType` is noncomputable as well,
  since `ℝ` has no decidable order in Lean's constructive sense.

So one cannot just `#eval P.signVariations` for `P : ℝ[X]` (or even `ℚ[X]`).

## What *is* constructive

The sign-variation count is a finite combinatorial function of the *coefficient
list*. Over a field with a decidable order — `ℚ` is the canonical example — that
list-level function is fully computable. This file:

1. defines `signVarList : List ℚ → ℕ`, a **computable** mirror of the Mathlib
   definition (it `#eval`s and is provable by `decide`);
2. proves the bridge `signVarList P.coeffList = P.signVariations` so the
   computable count is *certified* to agree with the abstract one;
3. transports Mathlib's Descartes bound to the computable side
   (`posRoots_le_signVarList`);
4. derives a **decidable sound certificate**: `signVarList l = 0` is a finite,
   decidable test that — when `l` is the coefficient list of `P` — proves `P`
   has no positive roots (`no_pos_roots_of_signVarList_zero`).

The root *count* itself (`P.roots.countP (0 < ·)`) stays noncomputable — locating
real roots exactly needs Sturm's algorithm, not Descartes. But the **bound** side
of Descartes' Rule is fully constructive, and that is exactly what this file
exhibits and proves correct.

## Main results

- `signVarList` (computable `List ℚ → ℕ`)
- `signVarList_coeffList` : `signVarList P.coeffList = P.signVariations`
- `posRoots_le_signVarList` : `P.roots.countP (0 < ·) ≤ signVarList P.coeffList`
- `no_pos_roots_of_signVarList_zero` : a decidable certificate of no positive roots
- worked computable examples discharged by `decide`
-/

namespace DescartesConstructive

open Polynomial

/-- A **computable** sign-variation count on an explicit list of rational
coefficients (ordered leading-coefficient-first, matching `Polynomial.coeffList`).

This is the constructive core of the file: every operation — `SignType.sign` on
`ℚ`, the `· ≠ 0` filter, and `List.destutter (· ≠ ·)` — is decidable, so the
whole function reduces in the kernel and `#eval`s. -/
def signVarList (l : List ℚ) : ℕ :=
  (((l.map SignType.sign).filter (· ≠ 0)).destutter (· ≠ ·)).length - 1

/-- The computable list-level count agrees, by definition, with Mathlib's abstract
`Polynomial.signVariations` once we feed it the polynomial's coefficient list.

This is the *certificate of correctness* for `signVarList`: it computes precisely
the quantity Descartes' Rule bounds. -/
theorem signVarList_coeffList (P : ℚ[X]) :
    signVarList P.coeffList = P.signVariations := by
  rfl

/-- **Descartes' bound, constructive form.** The number of positive roots of a
rational polynomial is at most the *computable* sign-variation count of its
coefficient list. The right-hand side is a finite algorithm on the coefficients;
no root finding is required. -/
theorem posRoots_le_signVarList (P : ℚ[X]) :
    P.roots.countP (0 < ·) ≤ signVarList P.coeffList := by
  rw [signVarList_coeffList]
  exact P.roots_countP_pos_le_signVariations

/-- **A decidable, sound certificate of "no positive roots".**

The hypothesis `signVarList P.coeffList = 0` is a finite decidable test on the
coefficient list. When it holds, `P` provably has no positive roots (counted with
multiplicity). This is the constructive payoff: a checkable witness, produced by a
terminating algorithm, that certifies a structural fact about the (noncomputable)
root multiset. -/
theorem no_pos_roots_of_signVarList_zero (P : ℚ[X])
    (h : signVarList P.coeffList = 0) :
    P.roots.countP (0 < ·) = 0 :=
  Nat.le_zero.mp (h ▸ posRoots_le_signVarList P)

/-- Conversely, a nonzero positive-root count forces a positive sign-variation
count — the contrapositive certificate. -/
theorem signVarList_pos_of_pos_roots (P : ℚ[X])
    (h : 0 < P.roots.countP (0 < ·)) :
    0 < signVarList P.coeffList :=
  lt_of_lt_of_le h (posRoots_le_signVarList P)

/-! ## Worked computable examples

These reduce entirely in the kernel: `decide` confirms the `signVarList` algorithm
on explicit rational coefficient lists. No axioms (`decide`, not `native_decide`). -/

/-- `x³ - x² - x + 1 = (x-1)²(x+1)` has coefficients `[1, -1, -1, 1]`: two sign
changes (`+ - - +`). Hence at most two positive roots (in fact one, doubled). -/
example : signVarList [1, -1, -1, 1] = 2 := by decide

/-- `x² + 3x + 2 = (x+1)(x+2)`, coefficients `[1, 3, 2]`: no sign changes, so the
certificate fires — no positive roots. -/
example : signVarList [1, 3, 2] = 0 := by decide

/-- `x² - 1 = (x-1)(x+1)`, coefficients `[1, 0, -1]`: one sign change (the
interior zero is ignored), hence exactly the one positive root `x = 1`. -/
example : signVarList [1, 0, -1] = 1 := by decide

/-- Interior zeros never count as sign changes: `[1, 0, 0, 1]` has none. -/
example : signVarList [1, 0, 0, 1] = 0 := by decide

/-- A fully alternating list `+ - + -` realises the maximal three sign changes. -/
example : signVarList [1, -2, 3, -4] = 3 := by decide

/-- The empty list (the zero polynomial's `coeffList`) and singletons have zero
variations. -/
example : signVarList [] = 0 := by decide

example : signVarList [5] = 0 := by decide

end DescartesConstructive
