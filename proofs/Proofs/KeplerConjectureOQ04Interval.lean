import Mathlib
import Proofs.KeplerConjectureOQ04

/-!
# Kepler Conjecture OQ-04 (companion): the packing-density interval as reusable API

The parent file `KeplerConjectureOQ04.lean` builds the non-spherical packing hierarchy
`fcc < ellipsoid < tetrahedron < octahedron < rhombicDodecahedron = 1` and proves the
universal ceiling `packingDensity_le_rhombicDodecahedron` (every density `≤ 1`, attained
by the space-filling rhombic dodecahedron).  The `PackingDensity` structure carries the
two-sided bound as separate fields `nonneg : 0 ≤ density` and `le_one : density ≤ 1`, but
never packages them as a single interval membership for downstream interval/positivity
reasoning.

This companion supplies that reusable API:

* `packingDensity_mem_Icc` — every packing density lies in `Set.Icc 0 1`.
* `packingDensity_mem_Icc_rhombicDodecahedron` — the same bound stated against the
  attained ceiling `rhombicDodecahedronPackingDensity = 1`, tying the universal maximum
  `packingDensity_le_rhombicDodecahedron` to the interval form.

All results are `0`-sorry / `0`-axiom on top of Mathlib and the parent file.
-/

namespace KeplerConjectureOQ04

open Real KeplerConjecture

/-- **Packing densities live in `[0, 1]`.**  Packaging the `PackingDensity` fields
`nonneg` and `le_one` as a single interval membership, for downstream positivity /
interval reasoning (the analogue of an `edgeDensity_mem_Icc`-style API lemma). -/
theorem packingDensity_mem_Icc (d : PackingDensity) :
    d.density ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨d.nonneg, d.le_one⟩

/-- **Packing densities lie below the attained ceiling.**  The interval form of the
universal maximum `packingDensity_le_rhombicDodecahedron`: every density lies in
`Set.Icc 0 rhombicDodecahedronPackingDensity`, whose upper endpoint is the space-filling
value `1` and is genuinely attained (`exists_packingDensity_eq_one`). -/
theorem packingDensity_mem_Icc_rhombicDodecahedron (d : PackingDensity) :
    d.density ∈ Set.Icc (0 : ℝ) rhombicDodecahedronPackingDensity :=
  ⟨d.nonneg, packingDensity_le_rhombicDodecahedron d⟩

/-!
## The Ulam interval `[fcc, 1]` for centrally symmetric convex bodies

For a *general* packing density the only interval available is `[0, 1]` above.  The
one class where the lower endpoint sharpens is the centrally symmetric convex bodies:
Ulam's conjecture (the file's `ulam_conjecture` axiom) asserts each of them packs at
density at least the sphere/FCC value `fccDensity = π/(3√2)`, and the structural ceiling
`le_one` still caps it at `1`.  Packaging the two as a single interval membership gives
the sharpest two-sided bound the file supports for this class, conditional on Ulam.
-/

/-- **Symmetric-convex-body densities lie in `[fccDensity, 1]`.**  The Ulam-conditional
sharpening of `packingDensity_mem_Icc`: for a centrally symmetric convex body packing the
lower endpoint rises from `0` to the sphere/FCC value `fccDensity` (`ulam_conjecture`),
while `le_one` keeps the upper endpoint at `1`.  Depends on the `ulam_conjecture` axiom
(an open conjecture), so this interval is conditional. -/
theorem symmetricConvexBody_density_mem_Icc_fcc (p : SymmetricConvexBody3DPacking) :
    p.density ∈ Set.Icc fccDensity 1 :=
  ⟨ulam_conjecture p, p.le_one⟩

/-- **Same interval stated against the named `fccPacking` instance.**  The interval
`[fccPacking.density, 1]` form, tying the lower endpoint to the concrete FCC packing
instance from the parent file via `ulam_le_fccPacking_density`. -/
theorem symmetricConvexBody_density_mem_Icc_fccPacking
    (p : SymmetricConvexBody3DPacking) :
    p.density ∈ Set.Icc fccPacking.density 1 :=
  ⟨ulam_le_fccPacking_density p, p.le_one⟩

end KeplerConjectureOQ04
