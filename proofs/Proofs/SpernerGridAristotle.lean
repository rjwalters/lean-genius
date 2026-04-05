/-
  Aristotle targets for SpernerGrid.lean
  Routine supporting lemmas for the grid adjacency relation.
  See SpernerGrid.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main abstract Sperner theorem (proved in SpernerMathlib4.lean)
  - NOT boundary_doors_odd (hard: requires induction on dimension)
  - NOT boundary_verts_on_face (incorrect, pending architectural redesign)
  - Structural properties of gridAdj: symmetry, shared-face, distinctness

  These three lemmas follow from the definitions of gridAdj, interiorFlip,
  boundaryFlip0, and boundaryFlipLast: the flip operations are involutions
  that change exactly one vertex while preserving the rest.
-/
import Mathlib
import Proofs.SpernerGrid

namespace SpernerGrid

/-- Adjacency is symmetric: if s is adjacent to s' through facet k,
    then s' is adjacent to s through some facet k'. -/
theorem gridAdj_symm (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    gridAdj d N s' k' = some (s, k) := by
  sorry

/-- Adjacent cells share their codimension-1 face:
    if s adj s' via k and k', then their faces (all vertices except k and k'
    respectively) are equal as sets. -/
theorem gridAdj_vertex (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    (Finset.univ.erase k).image s.verts =
    (Finset.univ.erase k').image s'.verts := by
  sorry

/-- Adjacent cells are distinct: the flip changes at least one vertex. -/
theorem gridAdj_ne (s : GridSimplex d N)
    (k : Fin (d + 1)) (s' : GridSimplex d N)
    (k' : Fin (d + 1))
    (h : gridAdj d N s k = some (s', k')) :
    s ≠ s' := by
  sorry

end SpernerGrid
