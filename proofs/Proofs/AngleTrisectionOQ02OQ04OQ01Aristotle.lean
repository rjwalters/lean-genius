/-
  Aristotle targets for AngleTrisectionOQ02OQ04OQ01
  Routine supporting lemmas for automated proof search.
  See AngleTrisectionOQ02OQ04OQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the deep Galois correspondence theorems (500+ lines each)
  - NOT the abstract tower-Galois equivalence
  - Concrete example: ℚ(√2) as an explicit quadratic tower of height 1
  - No axioms, no definition sorries, no open conjectures
  - Use only block comments, not module docstrings

  Included targets (1):
  - sqrt2_constructible_tower_ari: √2 lies in a quadratic tower of height 1 over ℚ

  NOT included (too complex for Aristotle):
  - galois_two_group_implies_tower: requires Galois correspondence glue (~500 lines)
  - tower_implies_galois_two_group: requires splitting field degree arguments (~300 lines)
-/
import Mathlib
import Proofs.AngleTrisectionOQ02OQ04OQ01

namespace AngleTrisectionOQ02OQ04OQ01Aristotle

open AngleTrisectionOQ02OQ04OQ01 IntermediateField FiniteDimensional

/-
## Concrete Example: √2 in a Quadratic Tower

The number √2 lies in ℚ(√2) = IntermediateField.adjoin ℚ {Real.sqrt 2},
which has degree 2 over ℚ. This gives a quadratic tower of height 1:
  ℚ = ⊥ ⊆ ℚ(√2) with [ℚ(√2):ℚ] = 2.

Proof strategy:
1. Take K = IntermediateField.adjoin ℚ {Real.sqrt 2}
2. Show ⊥ ≤ K (trivial)
3. Show [K:ℚ] = 2 (from X² - 2 being the minimal polynomial of √2)
4. Conclude QuadraticTower ℚ ℝ K 1 via QuadraticTower.step
5. Note Real.sqrt 2 ∈ K by definition of adjoin
-/

/-- √2 lies in a quadratic tower of height 1 over ℚ.
    Now proved in the main file via tower-formula + `Sqrt2Minpoly.adjoin_sqrt_two_finrank`. -/
theorem sqrt2_constructible_tower_ari :
    ∃ (K : IntermediateField ℚ ℝ),
      QuadraticTower ℚ ℝ K 1 ∧ (Real.sqrt 2 : ℝ) ∈ K :=
  AngleTrisectionOQ02OQ04OQ01.sqrt2_constructible_tower

end AngleTrisectionOQ02OQ04OQ01Aristotle
