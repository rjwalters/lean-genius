# Soundness Audit — kepler-conjecture-oq-04 (S11, researcher-5, 2026-06-15)

## Finding (CRITICAL): the development is logically inconsistent — `False` is provable

The OQ-04 file `proofs/Proofs/KeplerConjectureOQ04.lean` together with its parent
`proofs/Proofs/KeplerConjecture.lean` admits a closed-term proof of `False`. The
gallery presents this entry as a clean axiomatized hierarchy (0 sorries, "2 deep
axioms"), but the axiom set is contradictory, so every theorem in the entry is
vacuously derivable and the "0 sorries / verified hierarchy" claim is unsound.

### The two ingredients

1. **Parent axiom, over-quantified** (`KeplerConjecture.lean`):

   ```lean
   -- line 276
   axiom kepler_conjecture (d : PackingDensity) : d.density ≤ fccDensity
   -- line 289
   axiom gauss_lattice_theorem : ∀ (d : PackingDensity), d.density ≤ fccDensity
   ```

   Both quantify over the **abstract** structure `PackingDensity`, which carries
   no sphere / lattice hypothesis at all:

   ```lean
   structure PackingDensity where
     density : ℝ
     nonneg  : 0 ≤ density
     le_one  : density ≤ 1
   ```

   So as stated, these axioms assert "**every** real number in `[0,1]` that is
   wrapped in a `PackingDensity` is `≤ fccDensity`" — far stronger than the Kepler
   / Gauss theorems, which only bound *sphere* packings.

2. **Child counterexample, proven axiom-free** (`KeplerConjectureOQ04.lean`):

   ```lean
   -- line 242
   noncomputable def tetrahedronDimerPacking : PackingDensity where
     density := tetrahedronDimerDensity        -- = 4000/4671 ≈ 0.8563
     nonneg  := tetrahedronDimerDensity_pos.le
     le_one  := tetrahedronDimerDensity_lt_one.le

   -- line 207 (axiom-free, fully machine-checked)
   theorem tetrahedronDimerDensity_gt_fccDensity : fccDensity < tetrahedronDimerDensity

   -- line 259
   theorem exists_packingDensity_gt_fcc : ∃ p : PackingDensity, fccDensity < p.density :=
     ⟨tetrahedronDimerPacking, tetrahedronDimerDensity_gt_fccDensity⟩
   ```

### The contradiction

`tetrahedronDimerPacking : PackingDensity` is a concrete inhabitant with
`density = 4000/4671 > fccDensity ≈ 0.7405`. Feeding it to the universal parent
axiom gives the opposite bound:

```lean
example : False := by
  obtain ⟨p, hp⟩ := exists_packingDensity_gt_fcc        -- hp : fccDensity < p.density
  exact absurd (gauss_lattice_theorem p) (not_le.mpr hp) -- p.density ≤ fccDensity ⊥
```

(Equivalently use `kepler_conjecture tetrahedronDimerPacking` directly:
`4000/4671 ≤ fccDensity` contradicts `tetrahedronDimerDensity_gt_fccDensity`.)

This is a genuine `False`, not a near-miss: the witness is a `def` (not an axiom),
and `tetrahedronDimerDensity_gt_fccDensity` is axiom-free arithmetic.

### Why it slipped through

The child file's own docstring (line 256) already states the correct fact —
"the parent's abstract `PackingDensity` type, taken without the sphere assumption,
is **NOT** bounded above by `fccDensity`" — but never connected that observation to
the parent axiom, which asserts exactly the bound the child refutes. The two files
were authored/audited separately, so no session cross-checked the parent's
quantifier against the child's existence theorem.

## Proposed fix (requires Docker — NOT applied here under blackout)

The intended math is sound; only the **quantifier domain** of the two parent axioms
is wrong. The Kepler / Gauss theorems are statements about **sphere** packings, so
they must be restricted to a sphere marker rather than the abstract structure.

In `KeplerConjecture.lean`:

```lean
/-- Marker: a PackingDensity arising from a packing of congruent balls in ℝ³. -/
structure SpherePacking extends PackingDensity

axiom kepler_conjecture     (d : SpherePacking) : d.density ≤ fccDensity
axiom gauss_lattice_theorem (d : SpherePacking) : d.density ≤ fccDensity
-- (or a separate LatticeSpherePacking marker for the Gauss lattice case)
```

and make `fccPacking` an inhabitant of `SpherePacking` (it is the FCC ball packing),
so the existing `density_comparison`-style consumers in the parent still typecheck.

### Blast-radius note for consumers

- `EllipsoidLatticePacking` and `SymmetricConvexBody3DPacking` (child) `extends
  PackingDensity` and are **not** `SpherePacking`, so after the fix they are no
  longer in the domain of `gauss_lattice_theorem` — which is correct: an ellipsoid
  lattice / symmetric body is not a sphere packing.
- **Consequence for open PR #24509 (S10):** that PR "discharges"
  `bezdek_kuperberg_ellipsoid_lattice_upper_bound` to a theorem via
  `:= gauss_lattice_theorem e.toPackingDensity`. That discharge is only valid
  because the current axiom is over-broad; under the fix it no longer typechecks
  (an `EllipsoidLatticePacking` is not a `SpherePacking`). Bezdek–Kuperberg (2007)
  is a genuinely separate result (its proof needs affine density invariance, not
  just the sphere Kepler bound), so it should remain a `STATEMENT axiom`. **PR
  #24509 should be reconsidered/closed** — the apparent axiom reduction was an
  artifact of the unsound quantifier, not real progress.

## Recommended status change

While the inconsistency stands, the entry should not advertise a clean verified
hierarchy. After the fix lands, `axiomCount` should reflect: `kepler_conjecture`,
`gauss_lattice_theorem` (restricted), `bezdek_kuperberg_…` (restored), and
`ulam_conjecture` — i.e. the Bezdek axiom returns, raising the count back from the
#24509 reduction.

## Verification

This is a logic/typing issue, not arithmetic, so there is no Python certificate.
The `False` derivation above is a 3-line Lean term checkable in any Docker build
once the blackout lifts; it is intentionally **not** added to the library as a
live theorem (it would be a `False`-proving landmine). The fix, not the witness,
is the deliverable.
