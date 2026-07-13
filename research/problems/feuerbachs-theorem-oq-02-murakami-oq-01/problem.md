# Problem: Grace's Theorem Beyond the Trirectangular Tetrahedron

**Slug**: feuerbachs-theorem-oq-02-murakami-oq-01
**Created**: 2026-06-30
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The parent proof verifies **Grace's theorem (the 3D Feuerbach theorem)** for the
**trirectangular** tetrahedron: there is a single sphere through the three
vertices $A, B, C$ opposite the right-angle vertex $D$ that is internally
tangent to both the insphere and the $D$-exsphere, with a rational centre
$\Theta$ and rational radius $R$.

This problem asks to **extend the tangency result beyond the trirectangular
class** — to a broader family such as the **orthocentric** tetrahedra (those
whose four altitudes are concurrent) or the **isodynamic** tetrahedra — and, in
the fully general case, to characterize exactly which tetrahedra admit the
Grace tangent sphere.

### Plain Language

For the special "corner" (trirectangular) tetrahedron, the gallery already
proves a clean Feuerbach-type tangency with rational data. Real tetrahedra are
more general. The question is how far the tangency survives: does an analogous
sphere, tangent to both the insphere and an exsphere, exist for orthocentric
tetrahedra? For general tetrahedra? Identifying the right hypothesis and proving
(or formally refuting with a witness) the tangency for the next class up is the
goal.

### Why This Matters

The planar Feuerbach theorem (the nine-point circle is tangent to the incircle
and excircles) is a gem of classical geometry; its 3D analogue (Grace's theorem)
is far less standard and barely formalized. Pushing the verified case from the
trirectangular corner tetrahedron to a genuinely non-degenerate family is the
natural next increment and probes how much of the elegant planar tangency
persists in three dimensions.

## Known Results

### What's Already Proven

- Parent `feuerbachs-theorem-oq-02-murakami`
  (`Proofs/StatementOnly_FeuerbachOQ02Murakami_GraceTrirectangular.lean`):
  for the trirectangular tetrahedron a single sphere through $A, B, C$ is
  internally tangent to both the insphere and the $D$-exsphere, with rational
  centre and radius despite the irrational radii of the tangent spheres
  (0 sorry, 0 axiom).
- Planar Feuerbach theorem and its supporting circle/tangency machinery live in
  the `feuerbachs-theorem*` gallery family.

### What's Still Open

- An analogous tangency statement for **orthocentric** tetrahedra.
- A characterization of which tetrahedra admit the Grace tangent sphere.
- Whether rational centre/radius data persists outside the trirectangular case
  (likely not — expect algebraic-number data).

### Our Goal

Formalize a Grace-type tangency for at least one class strictly larger than the
trirectangular tetrahedra (target: orthocentric or isodynamic), or, failing a
positive result, produce a concrete tetrahedron witnessing the **failure** of
the tangency to sharpen the boundary of validity.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| feuerbachs-theorem-oq-02-murakami | Trirectangular Grace tangency (parent) | sphere tangency, coordinate geometry |
| feuerbachs-theorem | Planar Feuerbach tangency, nine-point circle | incircle/excircle tangency |
| feuerbachs-theorem-defs | Circle/sphere and tangency definitions | EuclideanGeometry, distances |

## Initial Thoughts

### Potential Approaches

1. **Coordinate computation for orthocentric tetrahedra**: Place an orthocentric
   tetrahedron in coordinates, compute insphere / exsphere centres and radii,
   and search for a sphere through one face internally tangent to both.
   - Risk: The algebra is heavier than the trirectangular case; radii become
     irrational and the tangent-sphere data may not be rational.
2. **Invariant / reduction argument**: Identify the geometric invariant that made
   the trirectangular case work (right-angle corner) and isolate the minimal
   hypothesis it can be relaxed to.
   - Risk: May reveal the tangency is special to the trirectangular class,
     turning the problem into a sharp counterexample hunt.

### Key Difficulties

- 3D tangency computations are algebraically heavy and Mathlib's spherical
  tangency API is thin compared to the planar circle API.
- The rational-data phenomenon is likely special to the trirectangular case;
  the general statement may need algebraic (non-rational) centres and radii.
