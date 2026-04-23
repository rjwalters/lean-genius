/-
  Aristotle targets for Erdős Problem #214 (Unit Distance Free Sets)
  Routine supporting lemmas for automated proof search.
  See Erdos214Problem.lean for the main formalization.

  Sorries here:
  1. isometry_maps_unit_square: isometries preserve unit squares (unfold + rw pattern)
  2. unit_square_from_stronger: JuhaszStrongerTheorem → Erdos214Statement
     (construct standard unit square as PointSet 4, apply stronger theorem)
-/
import Proofs.Erdos214Problem

namespace Erdos214Aristotle

open Erdos214

/-- Routine: an isometry maps every unit square to a unit square.
    Proof: unfold IsUnitSquare, rewrite each of the 6 distance equations
    using hf applied to the appropriate pair. -/
theorem isometry_maps_unit_square
    (f : Plane → Plane)
    (hf : ∀ x y : Plane, dist (f x) (f y) = dist x y)
    (p₁ p₂ p₃ p₄ : Plane)
    (h : IsUnitSquare p₁ p₂ p₃ p₄) :
    IsUnitSquare (f p₁) (f p₂) (f p₃) (f p₄) := by
  sorry

/-- Routine: JuhaszStrongerTheorem (any 4-point config embeds in complement)
    implies Erdos214Statement (unit square embeds in complement).
    Proof: instantiate JuhaszStronger with the standard unit square PointSet,
    extract the isometry, apply isometry_maps_unit_square. -/
theorem unit_square_from_stronger :
    JuhaszStrongerTheorem → Erdos214Statement := by
  sorry

end Erdos214Aristotle
