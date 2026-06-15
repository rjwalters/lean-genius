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

This is the sharp, sqrt-free-after-squaring target.  It is now CLOSED below
(`witnessT1_surd_separation`) by the rational separating bounds
√3 < 1.7321, √2 < 1.41422, √6 > 2.4494, each obtained from the squared
identity `Real.sq_sqrt` plus `Real.sqrt_nonneg` via `nlinarith` (the negated
goal multiplied by `0 ≤ √·` yields the matching one-sided bound), then
`linarith` for positivity.  No `Real.sqrt_lt'`/`Real.lt_sqrt` iff-lemma is
needed.

REMAINING SORRIES: `witnessT1_fails` (full non-tangency for the concrete T1 —
requires unfolding `twentyFourPointCenter`, `incenter`, `inradius`,
`twentyFourPointRadius` at the witness, sympy-certified in
`verify_feuerbach3d_fails_witness_exact.py` but heavy to transcribe) and the
trivial discharge that consumes it.  The genuinely number-theoretic kernel —
the three-surd separation — is the part now machine-statable and proved.

PARTIALLY VERIFIED — the surd kernel is a hand proof authored under a Docker +
Aristotle blackout (not yet compiler-checked); the witness non-tangency is
still `sorry`.  This file does NOT touch the registered parent file and is NOT
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
  -- The expression is in fact strictly positive (≈ 32.4618), so it is ≠ 0.
  -- Rational separating bounds (each verified by the squared identity + nonneg):
  --   √3 < 1.7321   (1.7321² = 3.00017… > 3)
  --   √2 < 1.41422  (1.41422² = 2.00002… > 2)
  --   √6 > 2.4494   (2.4494² = 5.99956… < 6)
  -- giving 72 − 30√3 − 12√2 + 12√6 > 72 − 51.963 − 16.97064 + 29.3928 ≈ 32.459 > 0.
  have h3 : Real.sqrt 3 < 1.7321 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3), Real.sqrt_nonneg 3]
  have h2 : Real.sqrt 2 < 1.41422 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have h6 : (2.4494 : ℝ) < Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 6), Real.sqrt_nonneg 6]
  have hpos : (0 : ℝ) < 72 - 30 * Real.sqrt 3 - 12 * Real.sqrt 2 + 12 * Real.sqrt 6 := by
    linarith
  exact ne_of_gt hpos

/-- The non-orthocentric conjunct of the witness, discharged outright.
`vec3 A B = (1,0,0)`, `vec3 C D = (1,0,1)`, so `dot3 = 1 ≠ 0` — a pure rational
computation (same `norm_num [vec3, dot3, …]` pattern as `witnessT1.nondegenerate`),
needing none of the surd-laden tangency definitions. This peels the easy half off
`witnessT1_fails`, leaving only the non-tangency as the lone remaining `sorry`. -/
theorem witnessT1_nonorthocentric :
    dot3 (vec3 witnessT1.A witnessT1.B) (vec3 witnessT1.C witnessT1.D) ≠ 0 := by
  norm_num [witnessT1, vec3, dot3]

/-- The witness T1 is non-orthocentric AND its twenty-four-point sphere is NOT
internally tangent to its insphere.  This is exactly the body of the parent
axiom `feuerbach_3d_fails_general`, specialised to T1.

The non-orthocentric conjunct is now the proven `witnessT1_nonorthocentric`; the
remaining `sorry` is ONLY the non-tangency, whose reduction to the proven surd
kernel `witnessT1_surd_separation` requires the heavy definitional unfold of
`twentyFourPointCenter`/`incenter`/`inradius`/`twentyFourPointRadius` at T1
(sympy-certified in `verify_feuerbach3d_fails_witness_exact.py`, build-gated). -/
theorem witnessT1_fails :
    (dot3 (vec3 witnessT1.A witnessT1.B) (vec3 witnessT1.C witnessT1.D) ≠ 0) ∧
    ¬ spheresInternallyTangent
        witnessT1.twentyFourPointCenter witnessT1.incenter
        witnessT1.twentyFourPointRadius witnessT1.inradius := by
  refine ⟨witnessT1_nonorthocentric, ?_⟩
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
