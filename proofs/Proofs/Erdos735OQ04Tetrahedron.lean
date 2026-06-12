/-
  Erdős Problem #735, Open Question #04 (oq-04) — S6a ACT:
  The regular tetrahedron is a 2-flat-magic configuration in ℝ³.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).

  This file ships a single concrete *existence* witness for the higher-flat
  (`k ≥ 2`) magic family conjectured in the parent slug: the regular
  tetrahedron at alternate cube vertices

      v₁ = ( 1,  1,  1),  v₂ = ( 1, -1, -1),
      v₃ = (-1,  1, -1),  v₄ = (-1, -1,  1)

  is `(k = 2)`-flat magic in `EuclideanSpace ℝ (Fin 3)` with magic constant 3
  under the uniform weighting `wᵢ = 1`.

  ## Proof architecture (affine-independence route)

  The S6a PREP (sessions/2026-05-13-s6a-prep-...) proposed enumerating the four
  triangular faces `F₁…F₄` and proving "no other minimal-spanning 2-flat". This
  file uses a cleaner route that avoids face enumeration entirely:

    * `tetra_affineIndependent` : the four vertices are affinely independent.
      Equivalently their `vectorSpan` is all of ℝ³ (`finrank = 3`).
    * For any `F : ConfigKFlat 2 tetraConfig`, the filtered point set has card
      `≥ 3` (config constraint) and `≤ 3` (a rank-2 flat cannot contain all four
      affinely independent vertices, else `finrank F.direction ≥ 3 > 2`). Hence
      card `= 3`, and the uniform-weight sum is `3 · 1 = 3`.

  The magic constant `c = 3` is exactly "k+1" — every minimal-spanning 2-flat in
  an affinely independent configuration meets it in exactly 3 points.

  ## Status (this iteration — S6a ACT scaffold, researcher-2)

  Docker build-verified against Mathlib v4.26.0: the `tetraVertex` / `tetraConfig`
  definitions and both theorem *statements* typecheck. The two proofs are
  isolated `sorry`s pending discharge (counts: 0 axioms, 2 sorries). This lands
  the first Lean realization of the concrete higher-flat (`k = 2`) magic witness
  and replaces the S6a PREP's face-enumeration plan with the leaner
  affine-independence architecture above.

  Discharge route for the two obligations (verified-tractable, no new axioms):

    * `tetra_affineIndependent`:
        rw [affineIndependent_iff_linearIndependent_vsub ℝ tetraVertex 0]
      then linear independence of the three difference vectors
      `v₂-v₁ = (0,-2,-2)`, `v₃-v₁ = (-2,0,-2)`, `v₄-v₁ = (-2,-2,0)`
      (determinant `-16 ≠ 0`).

    * `tetraConfig_isKFlatMagic`: witnesses `w ≡ 1`, `c = 3`. For
      `F : ConfigKFlat 2 tetraConfig` the filtered card is `≥ 3` (config
      constraint) and `≤ 3`: if all four vertices lay in `F` then
      `affineSpan ℝ (range tetraVertex) ≤ F`, so
      `vectorSpan ℝ (range tetraVertex) ≤ F.direction`; by
      `tetra_affineIndependent` + `AffineIndependent.finrank_vectorSpan`
      (`Fintype.card (Fin 4) = 3 + 1`) the left side has `finrank = 3`, forcing
      `finrank F.direction ≥ 3`, contradicting `Module.rank F.direction = 2`.
      Hence card `= 3` and the uniform-weight sum is `3`.

  (Aristotle MCP discharge was attempted this session but the backend was
  unreachable — "Resource not found"; the route above is hand-discharge-ready.)
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Proofs.Erdos735OQ04

namespace Erdos735OQ04Tetra

open Erdos735OQ04
open scoped Classical

/-- The four vertices of a regular tetrahedron at alternate cube corners,
    as points of `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def tetraVertex : Fin 4 → EuclideanSpace ℝ (Fin 3)
  | 0 => !₂[ 1,  1,  1]
  | 1 => !₂[ 1, -1, -1]
  | 2 => !₂[-1,  1, -1]
  | 3 => !₂[-1, -1,  1]

/-- The tetrahedron as a `PointConfigD 3`. -/
noncomputable def tetraConfig : PointConfigD 3 :=
  Finset.image tetraVertex Finset.univ

/-- The four tetrahedron vertices are affinely independent (no plane contains
    all four). Their difference vectors from `v₁` have determinant `-16 ≠ 0`. -/
theorem tetra_affineIndependent : AffineIndependent ℝ tetraVertex := by
  sorry

/-- The regular tetrahedron is `(k = 2)`-flat magic in ℝ³ with magic constant 3
    under the uniform weighting. -/
theorem tetraConfig_isKFlatMagic : IsKFlatMagic 2 tetraConfig := by
  sorry

end Erdos735OQ04Tetra
