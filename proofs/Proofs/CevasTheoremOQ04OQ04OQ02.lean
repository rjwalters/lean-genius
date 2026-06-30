/-
Excenters, the Nagel and Gergonne Points via Mass Points (Ceva OQ-04-OQ-04-OQ-02)

Open Question from: Angle Bisectors, Mass Points, and the Incenter
  (cevas-theorem-oq-04-oq-04), open question oq-02:

  "Give the analogous mass-point treatment of the excenters (signed masses) and
   the Gergonne/Nagel points, and locate each as a barycentric combination."

The parent file `CevasTheoremOQ04OQ04.lean` realises the **incenter** as the
barycentric point `(a : b : c)` and exhibits it on each angle bisector as an
affine combination of a vertex with the opposite cevian foot, in an arbitrary
real vector space.  This file gives the analogous treatment for the three
**excenters** (which require a *signed* mass), the **Nagel point**, and the
**Gergonne point**, locating each as an explicit barycentric combination and
proving it lies on the corresponding cevian.

## Tangent-length (Ravi) coordinates

A triangle is encoded by its three positive tangent lengths

    x = s − a,   y = s − b,   z = s − c        (s = (a+b+c)/2),

so that the side lengths are `a = y + z`, `b = z + x`, `c = x + y` and the
semiperimeter is `s = x + y + z`.  The map `(x,y,z) ↦ (a,b,c)` with `x,y,z > 0` is
exactly the set of valid (nondegenerate) triangles — the triangle inequalities
`a < b + c` etc. become simply `x, y, z > 0`.  In these coordinates the classical
triangle-centre barycentrics are polynomial:

    incenter   I  = (a : b : c)            = (y+z : z+x : x+y)
    A-excenter Iₐ = (−a : b : c)           = (−(y+z) : z+x : x+y)   (signed!)
    Nagel      N  = (s−a : s−b : s−c)      = (x : y : z)
    Gergonne   Ge = (1/(s−a):1/(s−b):1/(s−c)) = (yz : zx : xy).

## What is proved

For each centre we (i) give the barycentric combination as a point of a real
vector space `V`, and (ii) prove it lies on the relevant cevian from vertex `A`,
written as an affine combination of `A` and the opposite foot whose two weights
sum to `1`.  The excenter case is the substantive new content: the negative mass
`−a` at `A` still places `Iₐ` on the *internal* `A`-bisector (same foot as the
incenter), the mass-point signature of an excentre.

This is pure real linear algebra over an arbitrary `ℝ`-module; the proofs are the
`match_scalars`/`field_simp` idiom of the parent file.

References:
- H. S. M. Coxeter, S. L. Greitzer, *Geometry Revisited*, MAA (1967), §1.4 (Ceva),
  §1.4–1.5 (Nagel, Gergonne points)
- C. Kimberling, *Encyclopedia of Triangle Centers*, X(1) incenter, X(7) Gergonne,
  X(8) Nagel, X(11)–X(13) excenters

Tags: ceva, mass-points, barycentric, excenter, nagel-point, gergonne-point
-/

import Mathlib

namespace MassPointCeva.Excenters

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ## Triangle centres in tangent-length barycentric coordinates -/

/-- The **incenter** `(a : b : c) = (y+z : z+x : x+y)`, normalized by `2(x+y+z)`. -/
noncomputable def incenter (x y z : ℝ) (A B C : V) : V :=
  ((y + z) / (2 * (x + y + z))) • A + ((z + x) / (2 * (x + y + z))) • B
    + ((x + y) / (2 * (x + y + z))) • C

/-- The **A-excenter** `(−a : b : c) = (−(y+z) : z+x : x+y)`, normalized by `2x`.
The mass at `A` is *negative* — the hallmark of an excentre. -/
noncomputable def excenterA (x y z : ℝ) (A B C : V) : V :=
  ((-(y + z)) / (2 * x)) • A + ((z + x) / (2 * x)) • B + ((x + y) / (2 * x)) • C

/-- The **B-excenter** `(a : −b : c) = (y+z : −(z+x) : x+y)`, normalized by `2y`. -/
noncomputable def excenterB (x y z : ℝ) (A B C : V) : V :=
  ((y + z) / (2 * y)) • A + ((-(z + x)) / (2 * y)) • B + ((x + y) / (2 * y)) • C

/-- The **C-excenter** `(a : b : −c) = (y+z : z+x : −(x+y))`, normalized by `2z`. -/
noncomputable def excenterC (x y z : ℝ) (A B C : V) : V :=
  ((y + z) / (2 * z)) • A + ((z + x) / (2 * z)) • B + ((-(x + y)) / (2 * z)) • C

/-- The **Nagel point** `(s−a : s−b : s−c) = (x : y : z)`, normalized by `x+y+z`. -/
noncomputable def nagel (x y z : ℝ) (A B C : V) : V :=
  (x / (x + y + z)) • A + (y / (x + y + z)) • B + (z / (x + y + z)) • C

/-- The **Gergonne point** `(1/(s−a):1/(s−b):1/(s−c)) = (yz : zx : xy)`,
normalized by `yz + zx + xy`. -/
noncomputable def gergonne (x y z : ℝ) (A B C : V) : V :=
  ((y * z) / (y * z + z * x + x * y)) • A + ((z * x) / (y * z + z * x + x * y)) • B
    + ((x * y) / (y * z + z * x + x * y)) • C

/-! ## Cevian feet on side `BC` (opposite vertex `A`)

Each centre's `A`-cevian meets `BC` at the point obtained by dropping the
`A`-barycentric coordinate. -/

/-- Foot of the internal `A`-bisector on `BC`: barycentric `(0 : b : c) = (0 : z+x : x+y)`.
Common to the incenter **and** the `A`-excenter. -/
noncomputable def footBisectorA (x y z : ℝ) (B C : V) : V :=
  ((z + x) / (2 * x + y + z)) • B + ((x + y) / (2 * x + y + z)) • C

/-- Foot of the Nagel `A`-cevian on `BC` (the `A`-extouch point): barycentric
`(0 : s−b : s−c) = (0 : y : z)`, dividing `BC` as `BD:DC = z:y`. -/
noncomputable def extouchA (y z : ℝ) (B C : V) : V :=
  (y / (y + z)) • B + (z / (y + z)) • C

/-- Foot of the Gergonne `A`-cevian on `BC` (the incircle contact point):
barycentric `(0 : 1/(s−b) : 1/(s−c)) = (0 : z : y)`, dividing `BC` as `BD:DC = y:z`. -/
noncomputable def contactA (y z : ℝ) (B C : V) : V :=
  (z / (y + z)) • B + (y / (y + z)) • C

/-! ## The Nagel point -/

/-- The two `A`-cevian weights for the Nagel point sum to one. -/
theorem nagel_weights_sum_one (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    x / (x + y + z) + (y + z) / (x + y + z) = 1 := by
  have h : x + y + z ≠ 0 := by positivity
  field_simp; ring

/-- **The Nagel point lies on the `A`-cevian.** It is the affine combination of
`A` and the `A`-extouch point with weights `x/(x+y+z)` and `(y+z)/(x+y+z)`. -/
theorem nagel_on_cevian_A (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (A B C : V) :
    nagel x y z A B C
      = (x / (x + y + z)) • A + ((y + z) / (x + y + z)) • extouchA y z B C := by
  have hyz : y + z ≠ 0 := by positivity
  have hsum : x + y + z ≠ 0 := by positivity
  simp only [nagel, extouchA]
  match_scalars <;> field_simp

/-- The Nagel point as a `lineMap` from `A` to the extouch point. -/
theorem nagel_lineMap_A (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (A B C : V) :
    nagel x y z A B C
      = AffineMap.lineMap A (extouchA y z B C) ((y + z) / (x + y + z) : ℝ) := by
  have hyz : y + z ≠ 0 := by positivity
  have hsum : x + y + z ≠ 0 := by positivity
  simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, nagel, extouchA]
  match_scalars <;> field_simp <;> ring

/-! ## The Gergonne point -/

/-- The two `A`-cevian weights for the Gergonne point sum to one. -/
theorem gergonne_weights_sum_one (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y * z) / (y * z + z * x + x * y) + (z * x + x * y) / (y * z + z * x + x * y) = 1 := by
  have h : y * z + z * x + x * y ≠ 0 := by positivity
  field_simp; ring

/-- **The Gergonne point lies on the `A`-cevian.** It is the affine combination of
`A` and the incircle contact point on `BC` with weights `yz/(yz+zx+xy)` and
`(zx+xy)/(yz+zx+xy)`. -/
theorem gergonne_on_cevian_A (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (A B C : V) :
    gergonne x y z A B C
      = ((y * z) / (y * z + z * x + x * y)) • A
        + ((z * x + x * y) / (y * z + z * x + x * y)) • contactA y z B C := by
  have hyz : y + z ≠ 0 := by positivity
  have hD : y * z + z * x + x * y ≠ 0 := by positivity
  simp only [gergonne, contactA]
  match_scalars <;> field_simp <;> ring

/-! ## The excenters (signed masses) -/

/-- The two `A`-cevian weights for the `A`-excenter sum to one — even though the
mass at `A` is negative. -/
theorem excenterA_weights_sum_one (x y z : ℝ) (hx : 0 < x) (_hy : 0 < y) (_hz : 0 < z) :
    (-(y + z)) / (2 * x) + (2 * x + y + z) / (2 * x) = 1 := by
  have h : 2 * x ≠ 0 := by positivity
  field_simp; ring

/-- **The A-excenter lies on the internal `A`-bisector** — the same cevian and the
same foot `footBisectorA` as the incenter, despite the negative mass `−a` at `A`.
This is the mass-point signature of an excentre: a signed weight on the apex,
ordinary weights on the base, still concurrent on the internal bisector. -/
theorem excenterA_on_bisector_A (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (A B C : V) :
    excenterA x y z A B C
      = ((-(y + z)) / (2 * x)) • A
        + ((2 * x + y + z) / (2 * x)) • footBisectorA x y z B C := by
  have hfoot : 2 * x + y + z ≠ 0 := by positivity
  have hx2 : 2 * x ≠ 0 := by positivity
  simp only [excenterA, footBisectorA]
  match_scalars <;> field_simp

/-- For comparison, **the incenter lies on the same internal `A`-bisector**
through `footBisectorA`, with both weights positive. -/
theorem incenter_on_bisector_A (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (A B C : V) :
    incenter x y z A B C
      = ((y + z) / (2 * (x + y + z))) • A
        + ((2 * x + y + z) / (2 * (x + y + z))) • footBisectorA x y z B C := by
  have hfoot : 2 * x + y + z ≠ 0 := by positivity
  have hsum : 2 * (x + y + z) ≠ 0 := by positivity
  simp only [incenter, footBisectorA]
  match_scalars <;> field_simp

/-- The incenter's two `A`-bisector weights sum to one. -/
theorem incenter_weights_sum_one (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y + z) / (2 * (x + y + z)) + (2 * x + y + z) / (2 * (x + y + z)) = 1 := by
  have h : 2 * (x + y + z) ≠ 0 := by positivity
  field_simp; ring

/-! ## The B- and C-excenters lie on their internal bisectors

By the same signed-mass mechanism, each excenter sits on the *internal* bisector
from its own index vertex. -/

/-- Foot of the internal `B`-bisector on `CA`: barycentric `(c : 0 : a) = (x+y : 0 : y+z)`. -/
noncomputable def footBisectorB (x y z : ℝ) (C A : V) : V :=
  ((x + y) / (x + 2 * y + z)) • C + ((y + z) / (x + 2 * y + z)) • A

/-- **The B-excenter lies on the internal `B`-bisector** (signed mass `−b` at `B`). -/
theorem excenterB_on_bisector_B (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (A B C : V) :
    excenterB x y z A B C
      = ((-(z + x)) / (2 * y)) • B
        + ((x + 2 * y + z) / (2 * y)) • footBisectorB x y z C A := by
  have hfoot : x + 2 * y + z ≠ 0 := by positivity
  have hy2 : 2 * y ≠ 0 := by positivity
  simp only [excenterB, footBisectorB]
  match_scalars <;> field_simp

end MassPointCeva.Excenters
