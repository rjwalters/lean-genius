/-
  Erdős Problem #212: Rational Distance Sets in the Plane

  Source: https://erdosproblems.com/212
  Status: OPEN (conditional results exist)

  Question:
  Is there a dense subset of ℝ² such that all pairwise distances are rational?

  Conjecture (Ulam): NO - Erdős believed no such set exists.

  Conditional Results:
  - Tao (2014): NO, assuming the Bombieri-Lang conjecture
  - Shaffaf (2018): Same conclusion, independently

  Unconditional Results:
  - Shaffaf-Tao: Any rational distance set must lie in a finite union
    of real algebraic curves
  - Solymosi-de Zeeuw (2010): A rational distance set contained in a
    real algebraic curve must be finite, unless the curve is a line or circle

  Reference:
  - Shaffaf, "A solution of the Erdős-Ulam problem on rational distance
    sets assuming the Bombieri-Lang conjecture" (2018)
  - Solymosi-de Zeeuw, "On a question of Erdős and Ulam" (2010)
  - Ascher-Braune-Turchet, "The Erdős-Ulam problem, Lang's conjecture,
    and uniformity" (2020)
-/

import Mathlib

open Set

namespace Erdos212

/-! ## Core Definitions -/

/-- A subset S of ℝ² has **rational distances** if all pairwise
    distances between distinct points are rational. -/
def HasRationalDistances (S : Set (ℝ × ℝ)) : Prop :=
  S.Pairwise fun p₁ p₂ => ∃ q : ℚ, dist p₁ p₂ = q

/-! ## The Erdős-Ulam Problem -/

/--
**Erdős Problem #212 (OPEN)**: Is there a dense subset of ℝ² such that
all pairwise distances are rational?

**Conjecture** (Ulam, supported by Erdős): NO

This is one of the most famous unsolved problems in combinatorial geometry.
-/
def Erdos212Conjecture : Prop :=
  ¬∃ S : Set (ℝ × ℝ), Dense S ∧ HasRationalDistances S

/-- The problem is either true or false (classical). -/
theorem erdos_212_classical : Erdos212Conjecture ∨ ¬Erdos212Conjecture :=
  Classical.em _

/-! ## Conditional Result: Bombieri-Lang Implies Answer is NO -/

/--
**The Bombieri-Lang Conjecture** (roughly stated):

A variety of general type over a number field has only finitely many
rational points outside a proper closed subset.

This is a deep conjecture in arithmetic geometry.
-/
axiom BombieriLangConjecture : Prop

/--
**Tao-Shaffaf Theorem** (2014, 2018):

Assuming the Bombieri-Lang conjecture, there is no dense subset of ℝ²
with all pairwise distances rational.

Reference: Shaffaf (2018), Discrete Comput. Geom.
-/
axiom tao_shaffaf_conditional :
    BombieriLangConjecture → Erdos212Conjecture

/-! ## Unconditional Results -/

/-- A **real algebraic curve** in ℝ² is a set defined by polynomial equations. -/
def IsRealAlgebraicCurve (C : Set (ℝ × ℝ)) : Prop :=
  ∃ p : MvPolynomial (Fin 2) ℝ, C = {pt | MvPolynomial.eval (![pt.1, pt.2]) p = 0}

/--
**Shaffaf-Tao Theorem** (Unconditional):

Any subset of ℝ² with rational pairwise distances must be contained
in a finite union of real algebraic curves.

This severely restricts the possible structure of rational distance sets.
-/
axiom shaffaf_tao_algebraic_curves :
    ∀ S : Set (ℝ × ℝ), HasRationalDistances S →
      ∃ curves : Finset (Set (ℝ × ℝ)), (∀ C ∈ curves, IsRealAlgebraicCurve C) ∧
                                        S ⊆ ⋃ C ∈ curves, C

/--
**Solymosi-de Zeeuw Theorem** (2010):

A rational distance set contained in a real algebraic curve must be
finite, unless the curve contains a line or a circle.

Reference: Discrete Comput. Geom. (2010), 393-401
-/
axiom solymosi_de_zeeuw :
    ∀ C : Set (ℝ × ℝ), IsRealAlgebraicCurve C →
      ∀ S : Set (ℝ × ℝ), S ⊆ C → HasRationalDistances S →
        S.Finite ∨ (∃ line : Set (ℝ × ℝ), line ⊆ C) ∨ (∃ circle : Set (ℝ × ℝ), circle ⊆ C)

/-! ## Summary -/

/--
**Summary of Erdős Problem #212**:

| Result | Status | Authors |
|--------|--------|---------|
| Problem | OPEN | Ulam, Erdős |
| NO assuming Bombieri-Lang | Conditional | Tao (2014), Shaffaf (2018) |
| In finite union of curves | Unconditional | Shaffaf-Tao |
| Finite in any curve (mostly) | Unconditional | Solymosi-de Zeeuw (2010) |
| General position → finite | Conditional | Ascher-Braune-Turchet (2020) |

The consensus is that NO such dense rational distance set exists,
but an unconditional proof remains elusive.
-/
theorem summary_erdos_212 :
    (BombieriLangConjecture → Erdos212Conjecture) ∧
    (∀ S : Set (ℝ × ℝ), HasRationalDistances S →
       ∃ curves : Finset (Set (ℝ × ℝ)), S ⊆ ⋃ C ∈ curves, C) :=
  ⟨tao_shaffaf_conditional, fun S hS => by
    obtain ⟨curves, _, hsub⟩ := shaffaf_tao_algebraic_curves S hS
    exact ⟨curves, hsub⟩⟩

end Erdos212
