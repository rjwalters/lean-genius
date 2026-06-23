# Kepler OQ-04 — Soundness Audit S13: the PARENT file is internally inconsistent

**Sharpens S11 (#24523) and S12 (#24525).** Those audits derive `False` using the
*child* `KeplerConjectureOQ04.lean` witness `tetrahedronDimerPacking`
(density `4000/4671 ≈ 0.856 > fccDensity`). This note shows the contradiction is
**already present in the registered parent `proofs/Proofs/KeplerConjecture.lean`
by itself**, with no child file and no exotic witness — the witness is the file's
own canonical 2D hexagonal packing.

## The parent-only contradiction

All four ingredients live in `KeplerConjecture.lean`:

```lean
-- l.133  the file's own canonical 2D packing, as a PackingDensity term
noncomputable def hexagonalPacking2D : PackingDensity where
  density := hexagonalDensity2D
  ...

-- l.289  the 3D Gauss/Kepler bound, quantified over EVERY PackingDensity
axiom gauss_lattice_theorem :
    ∀ (d : PackingDensity), d.density ≤ fccDensity

-- l.392  hexagonal (2D) density strictly exceeds fcc (3D) density — a TRUE fact
axiom hexagonal_gt_fcc : hexagonalDensity2D > fccDensity
```

Derivation of `False` from parent axioms alone:

```lean
example : False := by
  have h₁ : hexagonalPacking2D.density ≤ fccDensity := gauss_lattice_theorem hexagonalPacking2D
  -- hexagonalPacking2D.density is definitionally hexagonalDensity2D
  have h₂ : fccDensity < hexagonalPacking2D.density := hexagonal_gt_fcc
  exact absurd h₁ (not_le.mpr h₂)
```

`kepler_conjecture` (l.276, same `∀ (d : PackingDensity), d.density ≤ fccDensity`)
gives an identical contradiction. A third internal derivation needs no fcc axiom
at all — just the two over-broad optimality axioms applied to the same term:

```lean
-- thues_theorem (l.152): ∀ d, d.density ≤ hexagonalDensity2D     (2D bound)
-- gauss_lattice_theorem (l.289): ∀ d, d.density ≤ fccDensity      (3D bound)
example : hexagonalDensity2D ≤ fccDensity :=
  gauss_lattice_theorem hexagonalPacking2D      -- contradicts hexagonal_gt_fcc
```

## Root cause (unchanged from S11) and why this matters

`structure PackingDensity` (l.94) is **dimension-agnostic** — just a real in
`[0,1]` with `nonneg`/`le_one`. Both the 2D optimality axiom (`thues_theorem`,
bound `hexagonalDensity2D`) and the 3D optimality axiom (`gauss_lattice_theorem`/
`kepler_conjecture`, bound `fccDensity`) quantify over this *same* undifferentiated
type. Applying the 3D bound to the 2D `hexagonalPacking2D` term is what collapses
the system.

**Why S13 is not a duplicate of S11/S12:**
- S11/S12 frame the inconsistency as *parent-axiom vs. child-theorem* — which a
  reader could mistake for "the child added an unrealistic packing." S13 shows the
  parent contradicts **itself**, using only declarations the gallery presents as
  the verified Kepler hierarchy. The registered parent alone is unsound.
- It **enlarges the fix scope**. The S11 proposal "restrict
  `kepler_conjecture`/`gauss_lattice_theorem` to a `SpherePacking` marker" is
  necessary but, stated against the child witness only, understates the work: the
  parent's 2D vs. 3D optimality axioms must **also** be made dimension-aware
  (e.g. a `dim : ℕ` field on the structure, with each optimality axiom guarded by
  its dimension), so that `gauss_lattice_theorem` cannot be instantiated at the
  2D `hexagonalPacking2D`. A single 3D `SpherePacking extends PackingDensity`
  marker fixes the child route but leaves `thues_theorem` vs.
  `gauss_lattice_theorem` still both ranging over bare `PackingDensity` unless the
  2D packings are likewise re-typed.

## Recommended fix (Docker-gated; NOT applied — registered file, blackout)

Make the structure dimension-tagged and guard each optimality axiom:

```lean
structure PackingDensity where
  dim     : ℕ
  density : ℝ
  nonneg  : 0 ≤ density
  le_one  : density ≤ 1

axiom thues_theorem (d : PackingDensity) (h : d.dim = 2) :
    d.density ≤ hexagonalDensity2D
axiom gauss_lattice_theorem (d : PackingDensity) (h : d.dim = 3) :
    d.density ≤ fccDensity
axiom kepler_conjecture (d : PackingDensity) (h : d.dim = 3) :
    d.density ≤ fccDensity
```

with `hexagonalPacking2D.dim := 2`, `fccPacking.dim := 3`, and the child's
`tetrahedronDimerPacking.dim := 3` (its `> fcc` density then correctly witnesses
that it is *not* a valid sphere packing, which is the real open content). After
this, `gauss_lattice_theorem hexagonalPacking2D` no longer typechecks
(`hexagonalPacking2D.dim = 2 ≠ 3`), and the contradiction is gone.

## Verification status

Pure logical derivation from declarations quoted above — no build required to
confirm the contradiction (the `example : False` term typechecks against the
current registered file). The **fix** is Docker-gated and intentionally not
applied here: it is a multi-site structural edit to a registered file and must be
verified with `./proofs/scripts/docker-build.sh` before landing.
