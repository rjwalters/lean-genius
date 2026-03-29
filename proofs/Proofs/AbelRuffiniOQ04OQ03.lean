import Mathlib.FieldTheory.AbelRuffini
import Mathlib.GroupTheory.Solvable
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Tactic

/-
# Galois's Solvability Criterion (OQ-04-OQ-03)

## Research Question

Formalize Galois's criterion: a polynomial is solvable by radicals iff
its Galois group is solvable.

## What We Prove

### ✅ Forward direction (from Mathlib):
  IsSolvableByRad F α ∧ Irreducible q ∧ q(α) = 0 → IsSolvable q.Gal

This is Mathlib's `solvableByRad.isSolvable'`.

### ❌ Reverse direction (AXIOMATIZED):
  IsSolvable q.Gal → roots of q are solvable by radicals

This requires constructing radical towers from the composition series of the
Galois group via Kummer theory. Not currently in Mathlib.

## The Full Criterion

The iff form: given an irreducible polynomial q over F (with char F = 0 or
sufficient roots of unity), a root α is solvable by radicals iff q.Gal
is a solvable group.

## References

- Galois, É. (1831). "Mémoire sur les conditions de résolubilité des
  équations par radicaux"
- Lang, S. (2002). "Algebra", Chapter VI
- Mathlib: FieldTheory.AbelRuffini
-/

set_option linter.unusedVariables false

noncomputable section

namespace GaloisCriterion

open Polynomial

variable {F : Type*} [Field F]
variable {E : Type*} [Field E] [Algebra F E]

-- ============================================================
-- PART 1: Forward Direction (Proved — from Mathlib)
-- ============================================================

/-- **Forward direction of Galois's criterion** (Mathlib):
If α is solvable by radicals and q is its irreducible minimal polynomial,
then the Galois group of q is solvable.

This is the easier direction, using the tower theorem:
radical extensions have solvable Galois groups, and solvability is
inherited by quotients. -/
theorem solvableByRad_implies_solvableGal
    (q : Polynomial F) (hq : Irreducible q)
    (α : E) (hroot : Polynomial.aeval α q = 0)
    (hrad : IsSolvableByRad F α) :
    IsSolvable q.Gal :=
  solvableByRad.isSolvable' hq hroot hrad

/-- Contrapositive: unsolvable Galois group → not solvable by radicals. -/
theorem not_solvableByRad_of_not_solvableGal
    (q : Polynomial F) (hq : Irreducible q)
    (α : E) (hroot : Polynomial.aeval α q = 0)
    (hns : ¬IsSolvable q.Gal) :
    ¬IsSolvableByRad F α :=
  fun hrad => hns (solvableByRad_implies_solvableGal q hq α hroot hrad)

-- ============================================================
-- PART 2: Reverse Direction (Axiomatized)
-- ============================================================

/-
The reverse direction requires:
1. A solvable group has a composition series with cyclic quotients
2. By Kummer theory (over fields with enough roots of unity),
   cyclic Galois extensions are radical extensions
3. Composing these gives a radical tower containing the splitting field
4. Every root of q lies in this tower → solvable by radicals

This is a deep theorem requiring Kummer theory, which is not yet
fully formalized in Mathlib.

Note: The reverse direction requires char F = 0 (or char F ∤ |Gal(q)|)
to ensure the needed roots of unity exist. Over characteristic p,
inseparable extensions complicate the picture.
-/

/-- **Reverse direction of Galois's criterion** (Axiomatized):
If the Galois group of an irreducible polynomial q over F is solvable,
and F has characteristic 0, then any root of q is solvable by radicals.

Proof requires Kummer theory for cyclic extensions, not yet in Mathlib. -/
axiom solvableGal_implies_solvableByRad
    (q : Polynomial F) (hq : Irreducible q) [CharZero F]
    (α : E) (hroot : Polynomial.aeval α q = 0)
    (hs : IsSolvable q.Gal) :
    IsSolvableByRad F α

-- ============================================================
-- PART 3: The Full Criterion (Iff)
-- ============================================================

/-- **Galois's Solvability Criterion** (Full iff):

A root of an irreducible polynomial over a field of characteristic 0
is solvable by radicals if and only if its Galois group is solvable.

Forward: Mathlib's `solvableByRad.isSolvable'`
Reverse: Axiomatized (requires Kummer theory) -/
theorem galois_criterion
    (q : Polynomial F) (hq : Irreducible q) [CharZero F]
    (α : E) (hroot : Polynomial.aeval α q = 0) :
    IsSolvableByRad F α ↔ IsSolvable q.Gal :=
  ⟨fun h => solvableByRad_implies_solvableGal q hq α hroot h,
   fun h => solvableGal_implies_solvableByRad q hq α hroot h⟩

-- ============================================================
-- PART 4: Applications
-- ============================================================

/-- **Corollary**: Over ℚ (char 0), polynomial solvability by radicals
is characterized entirely by its Galois group. -/
theorem galois_criterion_rationals
    {E : Type*} [Field E] [Algebra ℚ E]
    (q : Polynomial ℚ) (hq : Irreducible q)
    (α : E) (hroot : Polynomial.aeval α q = 0) :
    IsSolvableByRad ℚ α ↔ IsSolvable q.Gal :=
  galois_criterion q hq α hroot

/-- **Converse of Abel-Ruffini**: if a polynomial's Galois group IS
solvable (e.g., for degree ≤ 4), then its roots ARE expressible by
radicals (justifying the existence of the quadratic/cubic/quartic formulas). -/
theorem solvable_gal_means_radical_formula
    (q : Polynomial F) (hq : Irreducible q) [CharZero F]
    (α : E) (hroot : Polynomial.aeval α q = 0)
    (hs : IsSolvable q.Gal) :
    IsSolvableByRad F α :=
  (galois_criterion q hq α hroot).mpr hs

-- ============================================================
-- PART 5: Structural Observations
-- ============================================================

/-- The criterion makes the Abel-Ruffini theorem a special case:
S₅ is not solvable (Mathlib), so any polynomial with Galois group S₅
is not solvable by radicals. The criterion says this is the COMPLETE
obstruction: solvability of the Galois group is both necessary and sufficient. -/
theorem abel_ruffini_as_galois_special_case
    (q : Polynomial F) (hq : Irreducible q) [CharZero F]
    (α : E) (hroot : Polynomial.aeval α q = 0)
    (hns : ¬IsSolvable q.Gal) :
    ¬IsSolvableByRad F α :=
  fun h => hns ((galois_criterion q hq α hroot).mp h)

end GaloisCriterion
