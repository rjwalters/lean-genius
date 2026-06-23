/-
  Pascal's Hexagon — Open Question OQ-02: Brianchon's Theorem by Projective Duality

  Parent: `pascals-hexagon` (Pascal's Hexagon Theorem, Wiedijk #28).

  Open question:
  > Brianchon's theorem is the projective dual of Pascal's theorem. Formally
  > derive Brianchon (the three main diagonals of a hexagon circumscribed about
  > a conic are concurrent) from the already-formalized Pascal theorem, via
  > point–line duality.

  ## Resolution

  YES. In the homogeneous-coordinate model of `PascalsHexagon.lean` projective
  duality is *built in*: points and lines are both `Fin 3 → ℝ`, the join of two
  points and the meet of two lines are the **same** operation (`crossProduct`),
  and `collinear` / `concurrent` are the **same** determinant predicate. Pascal,
  applied to the six lines viewed as points on the dual (line-)conic, therefore
  yields Brianchon directly — no new geometric axiom is introduced.

  ## Mathematical content

  Let `D` be the line-conic (the dual of a point-conic; concretely the adjugate
  matrix `adj C`). A line `ℓ` is *tangent* to the point-conic `C` iff, as a
  vector, it lies on `D`: `ℓᵀ (adj C) ℓ = 0`. Six tangent lines `a,b,c,d,e,f`
  form a hexagon circumscribed about `C`. Its vertices are the meets of
  consecutive sides (`a∧b`, `b∧c`, …), and its three *main diagonals* join
  opposite vertices:

      AD : (a∧b) ∨ (d∧e)
      BE : (b∧c) ∨ (e∧f)
      CF : (c∧d) ∨ (f∧a)

  Reading the six tangent lines as six points on `D` and applying Pascal, the
  three "opposite-side intersection points" of that inscribed hexagon are
  collinear. But those three points are *literally* the three diagonals above
  (join = meet = `crossProduct`), and collinearity of three lines **is**
  concurrency. Hence the diagonals are concurrent — Brianchon's theorem.

  ## Axioms

  Inherits the single Pascal axiom `conic_implies_pascal_constraint` from
  `PascalsHexagon.lean`. Brianchon adds **no** new axioms and **no** sorries.
-/

import Mathlib.LinearAlgebra.Matrix.Adjugate
import Proofs.PascalsHexagon

open Matrix

namespace Brianchon

set_option linter.unusedVariables false

-- ============================================================
-- PART 1: The dual conic and tangency
-- ============================================================

/-- The **dual (line-)conic** of a point-conic `C`, represented by the adjugate
    matrix.  For a nondegenerate `C` one has `adj C = (det C) • C⁻¹`, so the
    line-conic carves out exactly the lines tangent to `C`. -/
noncomputable def dualConic (C : Conic) : Conic := C.adjugate

/-- A line `ℓ` is **tangent** to the conic `C` iff, viewed as a homogeneous
    vector, it lies on the dual conic: `ℓᵀ (adj C) ℓ = 0`.  This is the standard
    projective tangency/envelope condition. -/
def IsTangentLine (l : ProjLine) (C : Conic) : Prop :=
  pointOnConic l (dualConic C)

/-- The adjugate of a symmetric matrix is symmetric, so the dual of a symmetric
    conic is again a symmetric conic. -/
theorem dualConic_symmetric {C : Conic} (h : C.symmetric) :
    (dualConic C).symmetric := by
  have hCt : Cᵀ = C := by
    ext i j
    rw [Matrix.transpose_apply]
    exact h j i
  have hadj : C.adjugate = (C.adjugate)ᵀ := by
    have key : (Cᵀ).adjugate = (C.adjugate)ᵀ := Matrix.adjugate_transpose C
    rwa [hCt] at key
  intro i j
  show C.adjugate i j = C.adjugate j i
  calc C.adjugate i j
      = (C.adjugate)ᵀ i j := by rw [← hadj]
    _ = C.adjugate j i := Matrix.transpose_apply _ _ _

-- ============================================================
-- PART 2: Circumscribed hexagons
-- ============================================================

/-- A hexagon **circumscribed about** the line-conic `K`: six valid lines, each
    lying on `K` (i.e. tangent to the point-conic whose dual is `K`).  The sides
    are taken in cyclic order `a, b, c, d, e, f`. -/
structure CircumscribedHexagon (K : Conic) where
  a : ProjLine
  b : ProjLine
  c : ProjLine
  d : ProjLine
  e : ProjLine
  f : ProjLine
  ha : pointOnConic a K
  hb : pointOnConic b K
  hc : pointOnConic c K
  hd : pointOnConic d K
  he : pointOnConic e K
  hf : pointOnConic f K
  havalid : a ≠ 0
  hbvalid : b ≠ 0
  hcvalid : c ≠ 0
  hdvalid : d ≠ 0
  hevalid : e ≠ 0
  hfvalid : f ≠ 0

variable {K : Conic}

/-- The main diagonal `AD`, joining vertex `a∧b` to vertex `d∧e`. -/
noncomputable def diagAD (hex : CircumscribedHexagon K) : ProjLine :=
  lineThrough (lineIntersection hex.a hex.b) (lineIntersection hex.d hex.e)

/-- The main diagonal `BE`, joining vertex `b∧c` to vertex `e∧f`. -/
noncomputable def diagBE (hex : CircumscribedHexagon K) : ProjLine :=
  lineThrough (lineIntersection hex.b hex.c) (lineIntersection hex.e hex.f)

/-- The main diagonal `CF`, joining vertex `c∧d` to vertex `f∧a`. -/
noncomputable def diagCF (hex : CircumscribedHexagon K) : ProjLine :=
  lineThrough (lineIntersection hex.c hex.d) (lineIntersection hex.f hex.a)

/-- Read the six tangent lines of a circumscribed hexagon as six points
    inscribed in the line-conic `K`.  This is the duality bridge: a line on `K`
    is a point on `K` in the self-dual coordinate model. -/
def toInscribed (hex : CircumscribedHexagon K) : InscribedHexagon K where
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

/-- Under the duality bridge, the Pascal point `P = AB ∩ DE` of the inscribed
    reading is *definitionally* the diagonal `AD` of the circumscribed hexagon:
    both are `crossProduct (crossProduct a b) (crossProduct d e)`. -/
theorem pascalP_toInscribed (hex : CircumscribedHexagon K) :
    pascalP (toInscribed hex) = diagAD hex := rfl

theorem pascalQ_toInscribed (hex : CircumscribedHexagon K) :
    pascalQ (toInscribed hex) = diagBE hex := rfl

theorem pascalR_toInscribed (hex : CircumscribedHexagon K) :
    pascalR (toInscribed hex) = diagCF hex := rfl

-- ============================================================
-- PART 3: Brianchon's Theorem
-- ============================================================

/-- **Brianchon's Theorem** (projective dual of Pascal's theorem).

    If a hexagon is circumscribed about a conic — its six sides `a,…,f` lie on
    the line-conic `K` — then its three main diagonals `AD`, `BE`, `CF` are
    concurrent.

    The proof is pure duality: the six sides, read as points on `K`, form an
    inscribed hexagon; Pascal's theorem makes the three opposite-side
    intersection points collinear; those points are exactly the three diagonals,
    and collinearity of lines is concurrency. -/
theorem brianchon_theorem (hex : CircumscribedHexagon K) :
    concurrent (diagAD hex) (diagBE hex) (diagCF hex) := by
  have hpascal := pascal_hexagon_theorem K (toInscribed hex)
  -- `collinear` and `concurrent` are the same determinant predicate, and the
  -- three Pascal points coincide definitionally with the three diagonals.
  rw [pascalP_toInscribed, pascalQ_toInscribed, pascalR_toInscribed] at hpascal
  exact hpascal

/-- Brianchon's theorem phrased via tangency to a point-conic `C`: a hexagon
    whose six sides are tangent to `C` (equivalently, lie on the dual conic
    `adj C`) has concurrent main diagonals.  This is the corollary obtained by
    taking the line-conic to be `dualConic C`. -/
theorem brianchon_circumscribed (C : Conic)
    (hex : CircumscribedHexagon (dualConic C)) :
    concurrent (diagAD hex) (diagBE hex) (diagCF hex) :=
  brianchon_theorem hex

/-- Sanity check on the tangency framing: membership of a side in the dual conic
    of `C` is, by definition, tangency to `C`. -/
theorem side_tangent_iff_on_dualConic (l : ProjLine) (C : Conic) :
    IsTangentLine l C ↔ pointOnConic l (dualConic C) := Iff.rfl

end Brianchon
