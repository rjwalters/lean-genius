# Knowledge Base: spherical-law-of-cosines-oq-03

## Source
Seeker-selected gallery-extracted open question extending **spherical-law-of-cosines**.

## The question
Formalise the **dual** (angles) spherical law of cosines:

  cos C = − cos A · cos B + sin A · sin B · cos c

the polar dual of the parent's **side** law `cos c = cos a cos b + sin a sin b cos C`.
The minus sign on `cos A cos B` is the signature of spherical duality (the polar
triangle has sides `π − A`, angles `π − a`).

## Progress Summary
PROGRESS (S1, ACT). Wrote `proofs/Proofs/SphericalLawOfCosinesOQ03.lean`: a
self-contained, division-free, radical-free formalisation of the dual law, plus
reusable 3-D cross-product infrastructure (the parent file has none). Build is
PENDING — authored during a Docker + Aristotle dual-backend outage, so not yet
machine-checked; all proofs are `ring` / `rw`+`ring` / `nlinarith` only (no
`field_simp`, no division), and every identity is verified numerically over
3·10⁵ random spherical triangles (`research/scripts/verify-spherical-dual.py`,
all checks ≤ 8·10⁻¹⁴).

## Key mathematical reduction
Encode vectors in ℝ³ as a 3-field structure `V` with `dot`/`cross`. For a triangle
of unit vectors `u,v,w`, side cosines `ca=⟨v,w⟩, cb=⟨w,u⟩, cc=⟨u,v⟩`. The
interior-angle normal forms (verified independently against tangent-projection
angles):

  cos A = (ca − cb·cc)/(sin b·sin c),   sin A = |[u v w]|/(sin b·sin c)

with `[u v w] = ⟨u, v×w⟩` the scalar triple product and `sin a = √(1−ca²)`.
Substituting and multiplying by `sin a·sin b·sin²c` turns the trig dual law into
the pure polynomial identity (`dual_poly`, `ring`):

  (cc − ca·cb)(1 − cc²) = −(ca − cb·cc)(cb − ca·cc) + (1 − ca² − cb² − cc² + 2 ca cb cc)·cc

Hand-expanded and confirmed: both sides equal (cc − ca·cb)(1 − cc²).

## Theorems in the file (all `ring`-class, no division)
- `binet_cauchy`     ⟨a×b,c×d⟩ = ⟨a,c⟩⟨b,d⟩ − ⟨a,d⟩⟨b,c⟩
- `lagrange_identity` ‖a×b‖² = ‖a‖²‖b‖² − ⟨a,b⟩²
- `dot_cross_left/right`  cross ⟂ each factor
- `triple_sq`        [u v w]² = Gram determinant
- `cross_norm_sq_nonneg`, `one_sub_sq_nonneg`  side sines well defined (spherical C–S)
- `dual_poly`        algebraic heart (ring)
- `dual_law_cleared`             abstract cleared dual law
- `dual_spherical_law_cleared`   geometric cleared dual law for unit `u,v,w`

The "cleared" forms multiply the trig identity through by the (positive)
denominators, eliminating sqrt/division side-conditions — a standard, rigorous
formalisation choice (`1 − cc² = sin²c`, `[u v w]² = sin²A·sin²b·sin²c`).

## Mathlib Notes
- Worked over a bespoke `V := {x,y,z}` structure rather than `EuclideanSpace ℝ (Fin 3)`
  (the parent's `Vec3`) to keep every vector identity a transparent component-wise
  `ring` proof; Mathlib's `crossProduct` lives on `Fin 3 → ℝ` and interop with the
  parent's `PiLp` inner product adds friction for no benefit here.
- The parent `SphericalLawOfCosines.lean` proves the side law via an inner-product
  decomposition but introduces NO cross products; this file's Binet–Cauchy / Gram
  lemmas are new reusable infrastructure.

## Next steps
1. When Docker/Aristotle return: build `Proofs.SphericalLawOfCosinesOQ03`; fix any
   `simp only [dot,cross]` projection-reduction hiccups (add `dsimp only` if needed).
2. Optionally add the division/trig form
   `cos C = −cos A cos B + sin A sin B cos c` as a corollary of the cleared form
   (needs `field_simp` + non-degeneracy `sin a,b,c > 0`; deferred to avoid an
   unverifiable `field_simp` proof under the backend outage).
3. Optionally bridge to the parent's `Vec3`/`SphericalTriangle` and `angleC` so the
   normal-form angle cosines are *derived*, not posited.
