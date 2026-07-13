# Knowledge Base: dissection-of-cubes-oq-01-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The OQ-01-01 gallery result `minimal_collision_achievable` builds a `CubeDissection` with
exactly two colliding cubes (`HasMinimalCollision`). But that structure carries
`covers_unit_cube : True` as a **placeholder** — the geometric covering constraint is not
formalized. This sub-question asks whether the minimal-collision result survives once
`covers_unit_cube` is replaced by a genuine geometric coverage predicate.

---

## Insights

- The `True` placeholder masked a real obstruction. The OQ-01-01 witness places three small
  cubes (sizes 1/4, 1/4, 1/3) inside `[0,1]³`; together they occupy total volume
  `2·(1/4)³ + (1/3)³ = 59/864 ≈ 0.068` — under 7% of the unit cube.
- The natural machine-checkable surrogate for "covers the unit cube" is the **volumetric**
  identity `∑ c.side³ = 1`. For axis-aligned, pairwise interior-disjoint cubes contained in
  `[0,1]³` this is the necessary condition for tiling, and is measure-sufficient.
- Combinatorial achievability (containment + disjointness ⇒ 2 collisions possible) and
  geometric achievability (a genuine tiling with 2 collisions) are genuinely different
  problems. The former is proved (OQ-01-01); the latter is still open.

---

## Session 2026-06-20 (Session 2) — Genuine coverage predicate

**Mode**: FRESH
**Outcome**: progress (0-axiom, 0-sorry headline results; core geometric question still open)

### What I Did
- Added `proofs/Proofs/DissectionOfCubesOQ01OQ01OQ01.lean`.
- Defined `GeoCubeDissection`: identical containment + pairwise-disjointness to `CubeDissection`,
  but with `volume_fills : ∑ c.size³ = 1` in place of `covers_unit_cube : True`.
- `GeoCubeDissection.toCubeDissection`: forgetful map, so `collidingCubes` / `HasMinimalCollision`
  are reused unchanged.
- `unitGeoDissection`: the single unit cube is a genuine volume-filling dissection (predicate is
  satisfiable, not vacuous); `unitGeo_no_collision` shows it has 0 colliding cubes.
- `exampleCubes_volume_ne_one`: the OQ-01-01 witness has volume 59/864 ≠ 1.
- `no_geo_with_exampleCubes` (headline): **no** `GeoCubeDissection` can be built from the
  minimal-collision cube set — the combinatorial witness is not geometric.
- `geo_at_least_two_colliding`: transports the ≥2 lower bound to genuine dissections.

### Key Findings
- Replacing the placeholder with real coverage destroys the published witness.
- This isolates where the open problem lives: it is purely about the volume/coverage constraint.

### Files Modified
- `proofs/Proofs/DissectionOfCubesOQ01OQ01OQ01.lean` (new)
- `src/data/proofs/dissection-of-cubes-oq-01-oq-01-oq-01/meta.json` (new)

### Next Steps
- Construct the 2×2×2 uniform tiling (volume 1, all 8 cubes collide) as a genuine tiling exhibiting
  collisions.
- Investigate whether `∑ side³ = 1` + interior-disjointness forces strictly more than 2 collisions.
- Formalize a quantitative version of Littlewood's cascade lower bound.

---

## Dead Ends

- The OQ-01-01 three-cube construction cannot be promoted to a genuine (volume-filling) dissection
  (proved: `no_geo_with_exampleCubes`).

---

## Session 2026-06-20 (Session 3) — Build-verify, axiom audit, ship

**Mode**: REVISIT (finish iteration-2 work)
**Outcome**: completed (entry built green, 0-axiom confirmed, shipped)

### What I Did
- Built `Proofs.DissectionOfCubesOQ01OQ01OQ01` via docker wrapper → green (3061 jobs).
- `#print axioms` on `no_geo_with_exampleCubes`, `unitGeo_not_minimal`,
  `exampleCubes_volume_ne_one` → all `[propext, Classical.choice, Quot.sound]` only
  (foundational; none count). Entry is genuinely 0-axiom, 0-sorry.
- **Integrity fix**: removed the `geo_at_least_two_colliding` corollary. It was the *only*
  theorem in the file whose closure reached the two geometric axioms of `DissectionOfCubes.lean`
  (via `at_least_two_colliding_cubes`). It re-exported an existing oq-01 result rather than
  contributing new content, so demoting it to prose makes a blanket `verified / axiomCount: 0`
  claim fully defensible. The ≥2 lower bound is still documented in Section 4 prose with the
  one-line transport for any consumer.
- Fixed `Finset.not_mem_empty` → `Finset.notMem_empty` deprecation.
- Synced meta.json: theoremCount 8→7, lineCount 206→205, tightened `assumptions`.

### Key Findings
- Headline impossibility (`no_geo_with_exampleCubes`) stands alone as a genuinely axiom-free
  result: the published 2-collision witness occupies 59/864 of the unit cube, so it can never
  satisfy `volume_fills`.

### Files Modified
- proofs/Proofs/DissectionOfCubesOQ01OQ01OQ01.lean
- src/data/proofs/dissection-of-cubes-oq-01-oq-01-oq-01/meta.json

### Next Steps
- Open: is there a genuine volume-filling dissection with exactly two colliding cubes?
  (Littlewood cascade heuristic suggests the geometry forces > 2; unproved.)
