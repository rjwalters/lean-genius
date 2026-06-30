import Proofs.PascalsHexagon
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Brianchon's Theorem (projective dual of Pascal's Hexagon Theorem)

## What This Proves
**Brianchon's Theorem** (the projective dual of Pascal's Hexagon Theorem, Wiedijk #28):
If a hexagon is *circumscribed* about a conic — i.e. each of its six sides is tangent to
the conic — then the three **main diagonals** (the lines joining opposite vertices) are
**concurrent**.

This is the OQ-01 follow-up to `pascals-hexagon`: where Pascal concerns six points *on* a
conic and produces three *collinear* points, Brianchon concerns six lines *tangent to* a
conic and produces three *concurrent* lines. The two statements are exchanged by the
point ↔ line duality of the projective plane.

## Approach: duality is definitional in the homogeneous-coordinate model
We reuse the homogeneous-coordinate model of `PascalsHexagon.lean` verbatim:
- points and lines are both nonzero vectors in `ℝ³` (`ProjPoint = ProjLine = Fin 3 → ℝ`);
- `lineThrough p q = lineIntersection p q = crossProduct p q` (the *same* operation —
  the cross product simultaneously joins two points and meets two lines);
- `collinear`/`concurrent` are both "the 3×3 determinant of the three vectors vanishes".

Under this model the point ↔ line duality is literally the identity on `Fin 3 → ℝ`, and a
conic `C` (a symmetric matrix) is sent to its **dual conic** — the locus of its tangent
lines — represented by the **adjugate matrix** `adjugate C` (which equals `det C · C⁻¹` for
nondegenerate `C`, so the two define the same projective conic).

The pivotal observation is that the concurrency determinant of Brianchon's three main
diagonals is *the very same expression* as Pascal's collinearity determinant evaluated on
the six tangent lines:

  diagonal joining `(a ∩ b)` and `(d ∩ e)`
    = `crossProduct (crossProduct a b) (crossProduct d e)`
    = Pascal point `AB ∩ DE` with `A,B,D,E := a,b,d,e`.

So Brianchon's conclusion `concurrent` is *definitionally equal* to
`pascalConstraint a b c d e f`, and the six tangency hypotheses are exactly the statement
that `a,…,f` lie on the dual conic `adjugate C`. Brianchon therefore follows from the
single fact already isolated in `PascalsHexagon.lean`,
`conic_implies_pascal_constraint`, with **no new axiom** introduced here.

## Axiom status
Like `pascals-hexagon`, this entry is **axiomatized**: it depends on
`conic_implies_pascal_constraint` (the Cayley–Bacharach/Bézout fact underlying Pascal).
No `axiom`, `sorry`, or `native_decide` occurs in *this* file — the duality reduction is
fully machine-checked.

## Mathlib Dependencies
- `Matrix.adjugate` (`Mathlib.LinearAlgebra.Matrix.Adjugate`) — the dual conic.
- Everything else is inherited from `PascalsHexagon.lean`.
-/

set_option linter.unusedVariables false

open Matrix

namespace Brianchon

-- ============================================================
-- PART 1: The dual conic and tangency
-- ============================================================

/-- The **dual conic** of `C`: the conic whose points are the lines tangent to `C`.
    It is represented by the adjugate matrix. For a nondegenerate `C`,
    `adjugate C = det C • C⁻¹`, so `adjugate C` and `C⁻¹` describe the same projective
    conic; the adjugate is used because it is defined for every `C`. -/
noncomputable def dualConic (C : Conic) : Conic := Matrix.adjugate C

/-- A line `ℓ` is **tangent** to the conic `C` iff it lies on the dual conic, i.e.
    `ℓᵀ (adjugate C) ℓ = 0`. This is the standard projective tangency condition. -/
def lineTangentToConic (l : ProjLine) (C : Conic) : Prop :=
  pointOnConic l (dualConic C)

-- ============================================================
-- PART 2: Hexagon circumscribed about a conic
-- ============================================================

/-- Six lines `a b c d e f` forming a hexagon **circumscribed about** a conic `C`:
    every side is tangent to `C`. The vertices are the intersections of consecutive
    sides. This is the projective dual of `InscribedHexagon`. -/
structure CircumscribedHexagon (C : Conic) where
  a : ProjLine
  b : ProjLine
  c : ProjLine
  d : ProjLine
  e : ProjLine
  f : ProjLine
  ha : lineTangentToConic a C
  hb : lineTangentToConic b C
  hc : lineTangentToConic c C
  hd : lineTangentToConic d C
  he : lineTangentToConic e C
  hf : lineTangentToConic f C
  -- Validity conditions (lines are nonzero in projective space)
  havalid : ProjLine.valid a
  hbvalid : ProjLine.valid b
  hcvalid : ProjLine.valid c
  hdvalid : ProjLine.valid d
  hevalid : ProjLine.valid e
  hfvalid : ProjLine.valid f

variable {C : Conic}

/-- Vertex `a ∩ b` of the circumscribed hexagon (intersection of consecutive sides). -/
noncomputable def vertexAB (hex : CircumscribedHexagon C) : ProjPoint :=
  lineIntersection hex.a hex.b

/-- Vertex `b ∩ c`. -/
noncomputable def vertexBC (hex : CircumscribedHexagon C) : ProjPoint :=
  lineIntersection hex.b hex.c

/-- Vertex `c ∩ d`. -/
noncomputable def vertexCD (hex : CircumscribedHexagon C) : ProjPoint :=
  lineIntersection hex.c hex.d

/-- Vertex `d ∩ e`. -/
noncomputable def vertexDE (hex : CircumscribedHexagon C) : ProjPoint :=
  lineIntersection hex.d hex.e

/-- Vertex `e ∩ f`. -/
noncomputable def vertexEF (hex : CircumscribedHexagon C) : ProjPoint :=
  lineIntersection hex.e hex.f

/-- Vertex `f ∩ a`. -/
noncomputable def vertexFA (hex : CircumscribedHexagon C) : ProjPoint :=
  lineIntersection hex.f hex.a

/-- First main diagonal: joins opposite vertices `(a ∩ b)` and `(d ∩ e)`. -/
noncomputable def mainDiagonal1 (hex : CircumscribedHexagon C) : ProjLine :=
  lineThrough (vertexAB hex) (vertexDE hex)

/-- Second main diagonal: joins opposite vertices `(b ∩ c)` and `(e ∩ f)`. -/
noncomputable def mainDiagonal2 (hex : CircumscribedHexagon C) : ProjLine :=
  lineThrough (vertexBC hex) (vertexEF hex)

/-- Third main diagonal: joins opposite vertices `(c ∩ d)` and `(f ∩ a)`. -/
noncomputable def mainDiagonal3 (hex : CircumscribedHexagon C) : ProjLine :=
  lineThrough (vertexCD hex) (vertexFA hex)

-- ============================================================
-- PART 3: The duality bridge (fully verified)
-- ============================================================

/-- A circumscribed hexagon for `C` is the same data as a hexagon **inscribed in the dual
    conic** `dualConic C`: tangency to `C` is, by definition, incidence with `dualConic C`.
    This realizes the point ↔ line duality concretely. -/
noncomputable def toInscribedDual (hex : CircumscribedHexagon C) :
    InscribedHexagon (dualConic C) where
  A := hex.a
  B := hex.b
  C' := hex.c
  D := hex.d
  E := hex.e
  F := hex.f
  hA := hex.ha
  hB := hex.hb
  hC := hex.hc
  hD := hex.hd
  hE := hex.he
  hF := hex.hf
  hAvalid := hex.havalid
  hBvalid := hex.hbvalid
  hCvalid := hex.hcvalid
  hDvalid := hex.hdvalid
  hEvalid := hex.hevalid
  hFvalid := hex.hfvalid

/-- **Duality identity.** The concurrency determinant of Brianchon's three main diagonals is
    *identically* Pascal's collinearity determinant for the six tangent lines. This is the
    formal content of "Brianchon is the dual of Pascal": the same algebraic expression reads
    as a concurrence of lines or a collinearity of points depending on interpretation. -/
theorem concurrent_diagonals_eq_pascalConstraint (hex : CircumscribedHexagon C) :
    concurrent (mainDiagonal1 hex) (mainDiagonal2 hex) (mainDiagonal3 hex)
      ↔ pascalConstraint hex.a hex.b hex.c hex.d hex.e hex.f :=
  -- Both sides are the determinant of the *same* three cross-product vectors, because
  -- `lineThrough = lineIntersection = crossProduct`. The duality is definitional.
  Iff.rfl

-- ============================================================
-- PART 4: Brianchon's Theorem
-- ============================================================

/-- **Brianchon's Theorem.**

    If a hexagon with sides `a b c d e f` is circumscribed about a conic `C` (every side is
    tangent to `C`), then its three main diagonals — joining opposite vertices `(a∩b)–(d∩e)`,
    `(b∩c)–(e∩f)`, `(c∩d)–(f∩a)` — are concurrent.

    Proof: tangency to `C` is incidence with the dual conic `dualConic C`, so the six sides
    form a hexagon inscribed in `dualConic C`. Pascal's theorem
    (`conic_implies_pascal_constraint`) then yields the Pascal constraint for those six
    points, which is *definitionally* the concurrency of the three main diagonals. -/
theorem brianchon_theorem (C : Conic) (hex : CircumscribedHexagon C) :
    concurrent (mainDiagonal1 hex) (mainDiagonal2 hex) (mainDiagonal3 hex) := by
  rw [concurrent_diagonals_eq_pascalConstraint]
  -- Pascal's theorem for the six tangent lines, viewed as points on the dual conic.
  exact conic_implies_pascal_constraint (dualConic C) (toInscribedDual hex)

end Brianchon
