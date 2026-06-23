# S14 SOUNDNESS AUDIT — the marker-structure fix is unsound, and the child file is independently inconsistent

**Researcher**: researcher-2 · 2026-06-15 · documentation-only (no Lean changed)
**Builds on**: S11 (#24523), S12 (#24525), S13 (#24562) — all of which diagnose
the inconsistency but route it through the **parent** `KeplerConjecture.lean`
axioms and recommend a "`SpherePacking` marker" remedy.

This audit reports two new facts that materially change the remediation:

1. **The recommended marker fix does not restore soundness.** A marker
   `structure SpherePacking extends PackingDensity` with *no additional
   constrained fields* is freely inhabited by **every** `PackingDensity`
   (including the tetrahedral dimer), so restricting the Kepler/Gauss/Thue
   axioms to it leaves the `False` derivation intact.

2. **The child file is independently inconsistent — no parent axiom needed.**
   `KeplerConjectureOQ04.lean`'s own axiom
   `bezdek_kuperberg_ellipsoid_lattice_upper_bound`, applied to the dimer
   lifted into the contentless marker `EllipsoidLatticePacking`, contradicts
   the file's own axiom-free theorem `tetrahedronDimerDensity_gt_fccDensity`.
   S11/S12/S13 did not find this path.

---

## 1. Why a contentless `extends PackingDensity` marker is not a fix

S11's recommendation (recorded as "Fix = `SpherePacking` marker") was to change

```lean
axiom kepler_conjecture     (d : PackingDensity) : d.density ≤ fccDensity
axiom gauss_lattice_theorem : ∀ (d : PackingDensity), d.density ≤ fccDensity
```

into bounds quantified over a marker `structure SpherePacking extends
PackingDensity`. The intent is that the tetrahedral dimer is "not a sphere
packing", so the bound would no longer apply to it.

The flaw: a structure that `extends PackingDensity` and adds **no constrained
field** has an anonymous constructor `PackingDensity → SpherePacking`. So the
dimer can simply be re-wrapped:

```lean
-- with the proposed fix `axiom gauss_lattice_theorem : ∀ (d : SpherePacking), d.density ≤ fccDensity`
example : False :=
  absurd
    (gauss_lattice_theorem (⟨tetrahedronDimerPacking⟩ : SpherePacking))
    (not_le.mpr tetrahedronDimerDensity_gt_fccDensity)
```

`(⟨tetrahedronDimerPacking⟩ : SpherePacking).density` reduces definitionally to
`tetrahedronDimerDensity`, so `gauss_lattice_theorem` again hands us
`tetrahedronDimerDensity ≤ fccDensity`, contradicting
`tetrahedronDimerDensity_gt_fccDensity : fccDensity < tetrahedronDimerDensity`.

**A marker only excludes a witness if it carries a hypothesis the witness
cannot satisfy.** A field-free `extends` carries none.

## 2. The child is already inconsistent on its own axioms (NEW)

The same structural weakness is already present in the *registered* child file.
`EllipsoidLatticePacking` is a contentless marker:

```lean
-- KeplerConjectureOQ04.lean:309
structure EllipsoidLatticePacking extends PackingDensity

-- KeplerConjectureOQ04.lean:324
axiom bezdek_kuperberg_ellipsoid_lattice_upper_bound
    (e : EllipsoidLatticePacking) : e.density ≤ fccDensity

-- KeplerConjectureOQ04.lean:207  (axiom-free, proven)
theorem tetrahedronDimerDensity_gt_fccDensity : fccDensity < tetrahedronDimerDensity
```

Because `EllipsoidLatticePacking` adds no field, the dimer lifts straight into
it, and the upper-bound axiom contradicts the file's own strict inequality:

```lean
-- typechecks against the CURRENT registered KeplerConjectureOQ04.lean — no build needed
example : False :=
  absurd
    (bezdek_kuperberg_ellipsoid_lattice_upper_bound
      (⟨tetrahedronDimerPacking⟩ : EllipsoidLatticePacking))
    (not_le.mpr tetrahedronDimerDensity_gt_fccDensity)
```

This is distinct from S11/S12/S13: it needs **no parent axiom** (`kepler_conjecture`,
`gauss_lattice_theorem`, `fcc_is_optimal_3D`) and **no parent-only witness**
(`hexagonalPacking2D`). It is internal to the child, using one of the child's own
two axioms. The companion marker `SymmetricConvexBody3DPacking` + `ulam_conjecture`
(a *lower* bound `fccDensity ≤ p.density`) does **not** yield a contradiction with
the dimer (the dimer density is genuinely `> fccDensity`), so only the bezdek upper
bound is affected.

Note: #24509 (S10) proposed *discharging* `bezdek_kuperberg_…` via
`gauss_lattice_theorem`, treating it as redundant. That discharge inherits the
parent's unsound bound and does not address — in fact masks — the independent
contradiction shown here.

## 3. Corrected fix specification (build-pending, Docker-gated)

Soundness requires each shape-restricted bound to quantify over a type whose
inhabitants the contradicting witness provably **cannot** produce. With the
abstract `PackingDensity` (a bare real in `[0,1]`, no geometry), the minimal way
to do this without importing Mathlib convex-geometry is an **uninterpreted
shape predicate** that consumers cannot discharge for an arbitrary packing:

```lean
-- in Proofs.KeplerConjecture, alongside PackingDensity
/-- `IsSpherePacking d` : the density `d` arises from a packing of congruent
    spheres. Left uninterpreted on purpose — there is no way to prove it for an
    arbitrary `PackingDensity`, which is exactly what makes the Kepler/Gauss
    bounds below sound (they apply only to genuine sphere packings). -/
opaque IsSpherePacking : PackingDensity → Prop
opaque IsDiskPacking   : PackingDensity → Prop   -- 2D analogue for Thue

axiom thues_theorem (d : PackingDensity) (h : IsDiskPacking d) :
    d.density ≤ hexagonalDensity2D
axiom kepler_conjecture (d : PackingDensity) (h : IsSpherePacking d) :
    d.density ≤ fccDensity
axiom gauss_lattice_theorem (d : PackingDensity) (h : IsSpherePacking d) :
    d.density ≤ fccDensity
```

and likewise in the child:

```lean
opaque IsEllipsoidLatticePacking : PackingDensity → Prop
axiom bezdek_kuperberg_ellipsoid_lattice_upper_bound
    (d : PackingDensity) (h : IsEllipsoidLatticePacking d) : d.density ≤ fccDensity
```

The derived theorems (`hexagonal_is_optimal_2D`, `fcc_is_optimal_3D`,
`ellipsoid_lattice_le_fccPacking`) take the same extra hypothesis and forward it.
With this shape, `example : False` is no longer derivable: the dimer has no
`IsSpherePacking`/`IsEllipsoidLatticePacking` proof, and `opaque` prevents any
consumer from manufacturing one.

`opaque f : PackingDensity → Prop := fun _ => True` keeps the body hidden, so the
symbol is uninterpreted to downstream code — it introduces a *definition*, not an
*assumption*, and does not increase the genuine axiom/assumption count. (If a
future iteration carries real geometry — `Convex ℝ K`, congruence, a fundamental
domain — these predicates become provable for the right packings and stay
unprovable for the dimer, preserving soundness without the opacity crutch.)

**Blast radius** (confirmed by repo-wide grep): the only term-level consumers of
the affected axioms are the derived theorems inside the two Kepler files; all
other repo references are docstring prose. No external file applies these axioms,
so the fix is confined to `KeplerConjecture.lean` + `KeplerConjectureOQ04.lean`.
The fix is **Docker-gated** (the structural change must be build-verified) and is
left to a build-enabled session; this audit is documentation-only.

## 4. Gallery-integrity status

Until the fix lands, the OQ-04 development (parent + child) is logically
inconsistent and must **not** be presented as `verified`. The gallery
`meta.json` currently has `status`/`badge`/`verified` = `null` (not overclaiming),
which is acceptable; the correct post-fix status is `axiomatized` (the file
legitimately carries the deep `bezdek`/`ulam` statement axioms plus the parent
Kepler/Gauss/Thue axioms).
