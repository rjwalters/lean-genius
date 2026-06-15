/-
Aristotle target for `feuerbachs-theorem-oq-02-murakami` (step S10).

DISCHARGE TARGET for the lone axiom of the parent file
`proofs/Proofs/FeuerbachsTheoremOQ02.lean`:

    axiom feuerbach_3d_fails_general :
        ∃ T : Tetrahedron,
          (dot3 (vec3 T.A T.B) (vec3 T.C T.D) ≠ 0) ∧            -- non-orthocentric
          ¬ spheresInternallyTangent T.twentyFourPointCenter T.incenter
              T.twentyFourPointRadius T.inradius                -- 24-pt sphere NOT
                                                                -- tangent to insphere

The axiom asserts that the 3D "Feuerbach" tangency (twenty-four-point sphere
internally tangent to the insphere) can FAIL for a non-orthocentric
tetrahedron — i.e. orthocentricity is genuinely necessary. Prior slug
refutations (the trirectangular T0 and the regular tetrahedron) are ALL
orthocentric (dot3(AB,CD) = 0), so none of them witness this axiom; a
non-orthocentric witness is required.

EXPLICIT WITNESS (this file): T1 with
    A = (0,0,0),  B = (1,0,0),  C = (0,1,0),  D = (1,1,1).

Exact quantities (sympy-certified, see
`proofs/scripts/verify_feuerbach3d_fails_witness_exact.py`):
  • signedVolume6 = 1               (nondegenerate)
  • dot3(AB,CD) = 1 ≠ 0             (non-orthocentric: AB=(1,0,0), CD=(1,0,1))
  • circumcenter O = (1/2,1/2,1/2),  R = √3/2,  twentyFourPointRadius = √3/6
  • centroid G = (1/2,1/2,1/4),  mongePoint M = 4G−3O = (1/2,1/2,−1/2)
  • twentyFourPointCenter N₂₄ = midpoint(O,M) = (1/2,1/2,0)   ← RATIONAL
  • faceAreas = (√3/2, √2/2, √2/2, 1/2),  surfaceArea S = (1+√3+2√2)/2
  • inradius r = 3V/S = 1/(1+√3+2√2),  incenter
        I = ((1+√2)/Δ, (1+√2)/Δ, 1/Δ),   Δ = 1+√3+2√2
  • dist(N₂₄,I)² = (3−√3)/Δ²,   (R/3 − r)² = (−3+√3+2√6)²/(36 Δ²)

NON-TANGENCY ⇔ dist(N₂₄,I) ≠ |R/3 − r|.  Both sides are ≥ 0, so it suffices
to separate the squares.  Clearing the common factor 36 Δ² > 0:

    36 Δ² · dist(N₂₄,I)²  −  36 Δ² · (R/3 − r)²
      = 36(3−√3) − (−3+√3+2√6)²
      = 72 − 30√3 − 12√2 + 12√6                       (≈ 32.4618 ≠ 0).

So the WHOLE discharge reduces to the three-surd inequality

    72 − 30√3 − 12√2 + 12√6 ≠ 0       (in fact > 0).

This is the sharp, sqrt-free-after-squaring target.  A future Docker/Aristotle
session can close it by:
  • bounding √2 < 1.41422, √3 < 1.73206, √6 > 2.44948 (`Real.sqrt_lt'` /
    `Real.lt_sqrt`) and `nlinarith`/`linarith`, OR
  • carrying s2,s3 with s2²=2, s3²=3, s6=s2·s3, and `nlinarith [sq_nonneg …]`.

UNVERIFIED — authored under a Docker + Aristotle blackout; main proof left as
`sorry`.  This file does NOT touch the registered parent file and is NOT
itself registered in `Proofs.lean`, so it cannot affect the gallery build.
-/
import Mathlib
import Proofs.FeuerbachsTheoremOQ02

set_option maxHeartbeats 1000000

open scoped Real

namespace FeuerbachsTheoremOQ02

/-- The explicit non-orthocentric witness tetrahedron T1. -/
def witnessT1 : Tetrahedron where
  A := (0, 0, 0)
  B := (1, 0, 0)
  C := (0, 1, 0)
  D := (1, 1, 1)
  nondegenerate := by norm_num [vec3, dot3, cross3]

/-- The squared-separation core: the genuinely hard content of the discharge,
isolated as a self-contained three-surd inequality (see the file header for
the reduction).  `Δ = 1+√3+2√2 > 0`, so this is equivalent to
`dist(N₂₄,I)² ≠ (R/3 − r)²`. -/
theorem witnessT1_surd_separation :
    (72 : ℝ) - 30 * Real.sqrt 3 - 12 * Real.sqrt 2 + 12 * Real.sqrt 6 ≠ 0 := by
  sorry

/-- The witness T1 is non-orthocentric AND its twenty-four-point sphere is NOT
internally tangent to its insphere.  This is exactly the body of the parent
axiom `feuerbach_3d_fails_general`, specialised to T1. -/
theorem witnessT1_fails :
    (dot3 (vec3 witnessT1.A witnessT1.B) (vec3 witnessT1.C witnessT1.D) ≠ 0) ∧
    ¬ spheresInternallyTangent
        witnessT1.twentyFourPointCenter witnessT1.incenter
        witnessT1.twentyFourPointRadius witnessT1.inradius := by
  sorry

/-- Discharge of the parent existence axiom from the explicit witness. -/
theorem feuerbach_3d_fails_general_proved :
    ∃ T : Tetrahedron,
      (dot3 (vec3 T.A T.B) (vec3 T.C T.D) ≠ 0) ∧
      ¬ spheresInternallyTangent
          T.twentyFourPointCenter T.incenter
          T.twentyFourPointRadius T.inradius :=
  ⟨witnessT1, witnessT1_fails⟩

end FeuerbachsTheoremOQ02
