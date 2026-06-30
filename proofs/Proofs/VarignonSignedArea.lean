import Mathlib.Tactic

/-
# Varignon's Half-Area Law via Signed (Shoelace) Area

## What This Proves
For an *arbitrary* quadrilateral `ABCD` in the plane — convex, concave, or
self-intersecting — the Varignon parallelogram `PQRS` formed by the four side
midpoints satisfies the universal identity

  [PQRS] = ½ [ABCD],

where `[·]` is the **signed shoelace area**.  No convexity, simplicity, or
orientation hypothesis is needed: this is a pure polynomial identity in the eight
vertex coordinates.

## Context — the parent open question
The parent entry `varignon-theorem-oq-01` proves the *parallelogram structure*
of `PQRS` for any `ABCD` (`Q − P = R − S = (C − A)/2`, by `ring`) but says
nothing about area.  Its first open question asks:

> "What is the relationship between the Varignon parallelogram's area and the
>  original quadrilateral's area in the self-intersecting case?"

The classical "half-area" companion fact is stated only for *convex*
quadrilaterals and *unsigned* area, where it is "obvious from a picture."
Pictures fail exactly in the self-intersecting (bowtie) case the open question
singles out: such a figure encloses two lobes of opposite orientation, so the
word "area" is ambiguous.

## Resolution
Replace unsigned area by the **signed** shoelace functional.  With that single
correct invariant the half-area law becomes a *hypothesis-free* affine identity
that holds for all quadrilaterals at once — there is no case distinction between
convex and crossed.  We:

* define `signedArea` as the shoelace alternating-determinant half-sum;
* prove the universal identity `signedArea P Q R S = signedArea A B C D / 2`
  (the crux, by `ring`);
* give the conceptual diagonal-cross-product reformulation
  `signedArea A B C D = ½ ((C − A) ×_z (D − B))`, which *explains* the factor
  (the Varignon sides are the half-diagonals);
* exhibit an explicit **crossed** quadrilateral where `[ABCD] = 0`, the four
  midpoints are collinear, and `[PQRS] = 0` — the unsigned intuition collapses
  while the signed law continues to hold.

The model (`Point := ℝ × ℝ`, `midpoint2`) and the `dsimp only [...]; ring`
discipline are reused verbatim from the parent `VarignonTheorem.lean`.
-/

namespace VarignonSignedArea

/-- A point of the plane, modeled as a pair of real coordinates. -/
abbrev Point := ℝ × ℝ

/-- The midpoint of two points (the componentwise average).  Same definition as
the parent `VarignonTheorem.midpoint2`. -/
noncomputable def midpoint2 (X Y : Point) : Point := ((X.1 + Y.1) / 2, (X.2 + Y.2) / 2)

/-- The `2×2` signed area (cross product `z`-component) of the parallelogram
spanned by two vectors `U, V`: `U.x V.y − U.y V.x`. -/
def cross (U V : Point) : ℝ := U.1 * V.2 - U.2 * V.1

/-- The **signed (shoelace) area** of the quadrilateral `ABCD`, traversed in the
cyclic order `A → B → C → D → A`.  It is the alternating sum of the `2×2`
determinants of consecutive vertices, divided by two:
`½ Σ (Pᵢ.x Pᵢ₊₁.y − Pᵢ₊₁.x Pᵢ.y)`.  Unlike geometric area this carries a sign
governed by orientation, and is well defined (and additive) for every
quadrilateral including self-intersecting ones. -/
noncomputable def signedArea (A B C D : Point) : ℝ :=
  ((A.1 * B.2 - B.1 * A.2) + (B.1 * C.2 - C.1 * B.2)
    + (C.1 * D.2 - D.1 * C.2) + (D.1 * A.2 - A.1 * D.2)) / 2

/-- **Crux — the universal half-area law.**  For *every* quadrilateral `ABCD`
(no convexity, simplicity, or orientation hypothesis), the signed area of the
Varignon midpoint parallelogram `PQRS` is exactly half the signed area of
`ABCD`.  Pure polynomial identity in the eight coordinates, closed by `ring`. -/
theorem varignon_signed_area_eq_half (A B C D : Point) :
    signedArea (midpoint2 A B) (midpoint2 B C) (midpoint2 C D) (midpoint2 D A)
      = signedArea A B C D / 2 := by
  dsimp only [signedArea, midpoint2]; ring

/-- **Diagonal cross-product reformulation.**  The signed area of `ABCD` equals
half the `z`-cross-product of its two diagonals `AC = C − A` and `BD = D − B`.
This is the conceptual reason the half-area law holds: the Varignon sides are the
half-diagonals (`Q − P = (C − A)/2`, `P − S = (D − B)/2`), so the parallelogram
area is a *quarter* of the diagonal cross-product, i.e. *half* the quadrilateral
area. -/
theorem signedArea_eq_half_diagonal_cross (A B C D : Point) :
    signedArea A B C D = cross (C.1 - A.1, C.2 - A.2) (D.1 - B.1, D.2 - B.2) / 2 := by
  dsimp only [signedArea, cross]; ring

/-- The Varignon parallelogram's signed area equals one *quarter* of the diagonal
cross-product — exhibiting the "½ of the diagonals' cross is the quadrilateral,
¼ is the Varignon parallelogram" hierarchy directly. -/
theorem varignon_signed_area_eq_quarter_diagonal_cross (A B C D : Point) :
    signedArea (midpoint2 A B) (midpoint2 B C) (midpoint2 C D) (midpoint2 D A)
      = cross (C.1 - A.1, C.2 - A.2) (D.1 - B.1, D.2 - B.2) / 4 := by
  dsimp only [signedArea, midpoint2, cross]; ring

/-- **Signed area is genuinely signed.**  Reversing the traversal orientation
`A → D → C → B` negates the signed area.  This is what makes the unsigned
"area" notion ambiguous and forces the signed invariant. -/
theorem signedArea_reverse (A B C D : Point) :
    signedArea A D C B = - signedArea A B C D := by
  dsimp only [signedArea]; ring

/-- **Triangle-split additivity along the diagonal `AC`.**  The signed area of
`ABCD` is the sum of the signed (shoelace) areas of triangles `ABC` and `ACD`.
This records that `signedArea` is the honest shoelace functional, additive over
the diagonal decomposition even when `ABCD` is non-convex (where the two
triangles may carry opposite signs and partially cancel). -/
theorem signedArea_triangle_split (A B C D : Point) :
    signedArea A B C D
      = ((A.1 * B.2 - B.1 * A.2) + (B.1 * C.2 - C.1 * B.2) + (C.1 * A.2 - A.1 * C.2)) / 2
        + ((A.1 * C.2 - C.1 * A.2) + (C.1 * D.2 - D.1 * C.2) + (D.1 * A.2 - A.1 * D.2)) / 2 := by
  dsimp only [signedArea]; ring

/-! ## Worked witnesses pinning down the statement -/

/-- **Convex sanity check.**  The unit square `A=(0,0), B=(1,0), C=(1,1),
D=(0,1)` has signed area `1`, and its Varignon parallelogram has signed area
`1/2` — the classical convex half-area fact as a special case. -/
theorem witness_square :
    signedArea ((0:ℝ), (0:ℝ)) (1, 0) (1, 1) (0, 1) = 1 ∧
    signedArea
        (midpoint2 ((0:ℝ), (0:ℝ)) (1, 0)) (midpoint2 (1, 0) (1, 1))
        (midpoint2 (1, 1) (0, 1)) (midpoint2 (0, 1) ((0:ℝ), (0:ℝ))) = 1 / 2 := by
  refine ⟨?_, ?_⟩ <;> · dsimp only [signedArea, midpoint2]; norm_num

/-- **Asymmetric (non-symmetric convex) witness.**  `A=(0,0), B=(4,0), C=(5,3),
D=(1,4)` has signed area `29/2` and Varignon signed area `29/4`, confirming the
half-law away from any symmetry. -/
theorem witness_asymmetric :
    signedArea ((0:ℝ), (0:ℝ)) (4, 0) (5, 3) (1, 4) = 29 / 2 ∧
    signedArea
        (midpoint2 ((0:ℝ), (0:ℝ)) (4, 0)) (midpoint2 (4, 0) (5, 3))
        (midpoint2 (5, 3) (1, 4)) (midpoint2 (1, 4) ((0:ℝ), (0:ℝ))) = 29 / 4 := by
  refine ⟨?_, ?_⟩ <;> · dsimp only [signedArea, midpoint2]; norm_num

/-- **Crossed (self-intersecting "bowtie") witness — resolves the open
question.**  Take `A=(0,0), B=(2,0), C=(0,2), D=(2,2)`.  Drawn in the order
`A→B→C→D` this is a crossed quadrilateral: the segments `AB`/`CD` and `BC`/`DA`
produce two triangular lobes of opposite orientation.  Its *signed* area is `0`
(the lobes cancel), so the naive "Varignon area = half the enclosed area"
intuition is meaningless — there is no single enclosed region.

The four side midpoints are `P=(1,0), Q=(1,1), R=(1,2), S=(1,1)`: they are
**collinear** (all on the line `x=1`), so the "parallelogram" degenerates to a
doubled segment of signed area `0`.  The universal identity nevertheless holds:
`[PQRS] = 0 = ½·0 = ½[ABCD]`.  This is the precise sense in which the *signed*
law is the correct self-intersecting statement where the unsigned one fails. -/
theorem witness_crossed :
    signedArea ((0:ℝ), (0:ℝ)) (2, 0) (0, 2) (2, 2) = 0 ∧
    (midpoint2 ((0:ℝ), (0:ℝ)) (2, 0) = (1, 0) ∧
      midpoint2 ((2:ℝ), (0:ℝ)) (0, 2) = (1, 1) ∧
      midpoint2 ((0:ℝ), (2:ℝ)) (2, 2) = (1, 2) ∧
      midpoint2 ((2:ℝ), (2:ℝ)) (0, 0) = (1, 1)) ∧
    signedArea
        (midpoint2 ((0:ℝ), (0:ℝ)) (2, 0)) (midpoint2 (2, 0) (0, 2))
        (midpoint2 (0, 2) (2, 2)) (midpoint2 (2, 2) ((0:ℝ), (0:ℝ))) = 0 := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    · dsimp only [signedArea, midpoint2]; norm_num

/-- **The half-law on the crossed witness, packaged as the identity itself.**
Even though both sides are `0`, this is the genuine instance
`[PQRS] = ½[ABCD]` of the universal theorem on a self-intersecting figure,
making explicit that no convexity hypothesis was used. -/
theorem witness_crossed_half_law :
    signedArea
        (midpoint2 ((0:ℝ), (0:ℝ)) (2, 0)) (midpoint2 (2, 0) (0, 2))
        (midpoint2 (0, 2) (2, 2)) (midpoint2 (2, 2) ((0:ℝ), (0:ℝ)))
      = signedArea ((0:ℝ), (0:ℝ)) (2, 0) (0, 2) (2, 2) / 2 :=
  varignon_signed_area_eq_half _ _ _ _

end VarignonSignedArea
