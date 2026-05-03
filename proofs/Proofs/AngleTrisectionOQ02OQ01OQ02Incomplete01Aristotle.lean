/-
Aristotle companion for AngleTrisectionOQ02OQ01OQ02Incomplete01.lean
Problem: angle-trisection-oq-02-oq-01-oq-02-incomplete-01

Isolates the `hβ_dvd` sub-sorry at line 185:
  Goal: Module.finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ ∣ 2

Context: β : ℂ algebraic over ℚ, β² = a, ℚ⟮a⟯ ≤ ℚ⟮β⟯,
         Algebra ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ via inclusion, IsScalarTower ℚ ↥ℚ⟮a⟯ ↥ℚ⟮β⟯.

Proof plan: β satisfies X²-a over ↥ℚ⟮a⟯, so minpoly ↥ℚ⟮a⟯ βel has degree ≤ 2.
            finrank = natDegree(minpoly) ≤ 2; finrank ≥ 1; hence divides 2.
            The key finrank = natDegree step follows from βel generating ↥ℚ⟮β⟯ over ↥ℚ⟮a⟯
            (since β generates ℚ⟮β⟯ over ℚ, and ↥ℚ⟮a⟯ ⊇ ℚ).
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.Tactic

open Polynomial IntermediateField

namespace AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle

/-- Key lemma: if β is algebraic over ℚ and β² = a, then
    the degree [ℚ⟮β⟯:ℚ⟮a⟯] divides 2.

    Equivalent to: the extension ℚ⟮a⟯ ≤ ℚ⟮β⟯ has degree 1 or 2,
    which holds because β satisfies the quadratic X² - a over ℚ⟮a⟯. -/
theorem finrank_adjoin_β_over_adjoin_a_dvd_two
    (β a : ℂ)
    (halg_β : IsAlgebraic ℚ β)
    (hβ2 : β * β = a)
    (ha_le_β : (ℚ⟮a⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮β⟯)
    [hAlg : Algebra ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)]
    [hST : IsScalarTower ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)] :
    Module.finrank ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) ∣ 2 := by
  sorry

end AngleTrisectionOQ02OQ01OQ02Incomplete01Aristotle
