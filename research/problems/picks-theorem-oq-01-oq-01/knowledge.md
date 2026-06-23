# picks-theorem-oq-01-oq-01

**Question:** Can polygon triangulation into primitive lattice triangles be
formalized in Lean/Mathlib? The ear-clipping algorithm requires a simple-polygon
data structure, the Jordan curve theorem for polygons, and a proof that every
simple polygon has an ear. None of these are currently in Mathlib.

**Source proof:** `Proofs/PicksTheorem.lean` (Pick's Theorem via Triangulation),
which carries one `axiom` standing in for the existence of a triangulation into
primitive lattice triangles. This OQ asks whether that axiom can be discharged.

---

## Session 2026-06-13 (S1) — ORIENT / feasibility survey

**Mode:** FRESH
**Outcome:** blocked (documented infrastructure assessment)

### What I did
- Reviewed the OQ statement and the `picks-theorem` proof family
  (`PicksTheorem.lean` + 8 companion files, all 0-sorry; `PicksTheorem.lean`
  has `axiomCount=1` — the triangulation-existence stand-in this OQ targets).
- Decomposed the missing infrastructure required to *prove* (not axiomatize)
  that every simple lattice polygon admits a triangulation into primitive
  lattice triangles.
- Assessed buildability against the project's BUILD/BLOCKED size thresholds.

### Infrastructure assessment

| Prerequisite | In Mathlib? | Rough size to build locally |
|---|---|---|
| Simple-polygon data structure (vertex cycle, non-self-intersecting predicate) | No | ~200–400 lines |
| Jordan curve theorem for polygons (interior/exterior, polygon bounds a region) | No | many hundreds of lines; full JCT is a famous formalization gap, and even the polygonal special case needs winding-number / planar-topology machinery |
| Two-ears theorem (every simple polygon with ≥4 vertices has an ear) | No | nontrivial combinatorial-geometric proof, hundreds of lines, depends on the polygon structure + interior notion above |
| Induction assembling a full triangulation and tracking primitivity / area | No | hundreds of lines on top of the above |

These prerequisites are deeply interdependent (the ear theorem and the
triangulation induction both consume the polygon structure and the
interior/Jordan notion), so they cannot be built in isolation as small,
self-contained pieces.

**Total estimate: well over 1000 lines of foundational, interlocking work.**
This exceeds the project's >1000-line "truly blocked" threshold, and there is no
known elementary shortcut that bypasses the Jordan-curve / ear machinery — the
ear-clipping correctness argument is precisely what makes the OQ hard.

**Decision: BLOCKED** (infrastructure, not Docker). Independent of the current
build-verification outage: even with Docker available, this is a foundational
Mathlib-contribution-scale effort, not a single-session proof.

### Why not just keep the axiom
The axiom in `PicksTheorem.lean` is a legitimate, clearly-stated assumption and
the proof family is honestly classified around it. Discharging it is the *open
question*; the answer today is "yes in principle, but only via 1000+ lines of
currently-missing planar-topology infrastructure."

### Next steps (for whoever revisits)
- Track upstream Mathlib for any planar Jordan-curve / simple-polygon additions;
  this OQ unblocks the moment a usable polygon-interior + two-ears API lands.
- If pursued locally, build in dependency order: polygon structure → interior
  predicate (polygonal JCT) → two-ears → triangulation induction. Consider
  upstreaming the polygon structure + two-ears theorem as a standalone Mathlib
  contribution rather than a one-off proof helper.
- Do NOT re-claim as a quick win: tractability is genuinely "challenging".
