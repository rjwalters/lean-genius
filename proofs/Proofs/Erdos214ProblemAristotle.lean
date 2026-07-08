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
    (hf : ∀ x y : Plane, Erdos214.dist (f x) (f y) = Erdos214.dist x y)
    (p₁ p₂ p₃ p₄ : Plane)
    (h : IsUnitSquare p₁ p₂ p₃ p₄) :
    IsUnitSquare (f p₁) (f p₂) (f p₃) (f p₄) := by
  obtain ⟨h12, h23, h34, h41, h13, h24⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hf]
  · exact h12
  · exact h23
  · exact h34
  · exact h41
  · exact h13
  · exact h24

/-- Routine: JuhaszStrongerTheorem (any 4-point config embeds in complement)
    implies Erdos214Statement (unit square embeds in complement).
    Proof: instantiate JuhaszStronger with the standard unit square PointSet,
    extract the isometry, apply isometry_maps_unit_square. -/
theorem unit_square_from_stronger :
    JuhaszStrongerTheorem → Erdos214Statement := by
  intro hStrong S hFree
  -- The standard unit square as a 4-point configuration.
  set P : PointSet 4 := ![!₂[0, 0], !₂[1, 0], !₂[1, 1], !₂[0, 1]] with hP
  -- Juhász's stronger theorem gives a congruent copy of `P` inside `Sᶜ`.
  obtain ⟨f, hf_isom, hf_mem⟩ := hStrong S hFree P
  -- `P` itself is a unit square, and `f` is an isometry, so the image is one too.
  have hsq : IsUnitSquare (P 0) (P 1) (P 2) (P 3) := by
    simp only [hP, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
    exact isUnitSquare_standard
  exact ⟨f (P 0), f (P 1), f (P 2), f (P 3), hf_mem 0, hf_mem 1, hf_mem 2, hf_mem 3,
    isometry_maps_unit_square f hf_isom _ _ _ _ hsq⟩

end Erdos214Aristotle
