# Knowledge Base: sperner-simplicial-instance-oq-03

Boundary Door Parity for the Standard n-Simplex Triangulation.

---

## Problem Understanding

Goal stated by the OQ: prove `boundary_doors_odd` from first principles for the
standard n-simplex triangulation and discharge the assumption in the parent file.

**Key reframing (this session).** Reading `proofs/Proofs/SpernerSimplicialInstance.lean`,
`boundary_doors_odd` (theorem at **line 173**) is *already proven* — it is a parity
**transfer** theorem, not an open assumption:

- It takes explicit hypotheses `_hSperner`, `_hBoundaryOnFace`, `_hLowerDim`, `_hLastFace`.
- Its proof shows the boundary-door set `S` equals the top-facet door set `S_n`
  (every boundary door is forced onto geometric face `n` by the Sperner condition —
  a `IsDoor` at a lower color contradicts `IsSpernerColoring`), then concludes
  `Odd |S|` **from** `_hLastFace : Odd |S_n|`.
- `_hLowerDim` is **vestigial**: the final proof body uses only the `S = S_n`
  reduction and `_hLastFace`, never `_hLowerDim`.

So the genuine remaining first-principles gap is **`_hLastFace`** (the door count on
the top facet is odd) **plus the base case**, both to be discharged for the standard
triangulation by **induction on dimension**:

> top facet of `Δⁿ` is a `Δⁿ⁻¹` carrying the *induced* Sperner coloring ⇒ its door
> count is odd by the induction hypothesis; base case `n=1` gives exactly one door.

---

## Insights

- **Doors live only on the top facet.** Geometric facet `k` = facet opposite vertex
  `k`. Sperner forces: facet 0 colors ⊆ {1,2}, facet 1 colors ⊆ {0,2} (n=2 case) —
  neither can host a `{0,…,n-1}` door. Only the top facet can. This is exactly the
  Lean `S = S_n` reduction, confirmed numerically per-facet.
- **Induction bridge (the heart of `_hLastFace`).** `#boundary doors of Δⁿ` =
  `#doors on the top facet` = `#doors of the Sperner coloring induced on that facet
  (a Δⁿ⁻¹)`. Verified for n=2: equals the induced 1-D door count, which is odd.
- **Base case n=1.** Subdivided interval has exactly one boundary door (the left
  endpoint, colored 0), for every Sperner coloring.

### Numerical verification (build-free, durable)

`verify_boundary_doors.py` exhaustively enumerates **all** Sperner colorings and checks,
matching the Lean semantics (`IsSpernerColoring`, `IsDoor`, `IsPanchromatic`):

| Case | Colorings | Checks (all True) |
|------|-----------|-------------------|
| n=1 interval, m=1..5 | up to 16 | boundary doors odd (==1) |
| n=2 Kuhn grid, m=1..4 | up to 13 824 | panchromatic odd; boundary doors odd; **all on top facet**; count == induced 1-D door count |

This grounds the base case, the `S = S_n` reduction, and the induction bridge that
`_hLastFace` requires — without a Lean build (Docker down this session).

---

## Dead Ends / Cautions

- Do **not** try to re-prove `boundary_doors_odd` as a whole — it is already a proven
  theorem. Target the `_hLastFace` hypothesis specifically.
- The file currently has only `intervalTriangulation 1` (n=1) and a single 2-simplex
  fixture — no general standard/Kuhn triangulation instance. That construction is the
  prerequisite for the induction and is the main build work.

---

## Next Steps (ACT, build-gated)

1. Construct an explicit standard/Kuhn `Triangulation` instance for general `n`.
2. Define the **facet-restriction** map (top facet of dim-`n` triangulation → dim-`(n-1)`
   `Triangulation`) and prove the restricted coloring is Sperner.
3. Prove the **door bijection** between top-facet doors (dim `n`) and doors of the
   restricted triangulation (dim `n-1`); conclude `_hLastFace` by induction + base case.
4. ~200–400 LOC, medium difficulty. The door-bijection lemma is a good Aristotle candidate
   once the triangulation instance compiles.

---

## Session Log

### 2026-06-14 (Session 1) — ORIENT

**Mode**: FRESH · **Outcome**: progress (ORIENT, no .lean)

- Read parent `SpernerSimplicialInstance.lean`; found `boundary_doors_odd` already proven
  (line 173) as a parity-transfer theorem; identified `_hLastFace` as the real gap and
  `_hLowerDim` as vestigial.
- Wrote `verify_boundary_doors.py`; verified base case, `S = S_n` reduction, and the
  induction bridge over 14k+ Sperner colorings (n=1 and n=2 Kuhn grids).
- Updated research JSON knowledge; phase OBSERVE → ORIENT.
- **Files**: `verify_boundary_doors.py`, `knowledge.md`, `state.md`,
  `src/data/research/problems/sperner-simplicial-instance-oq-03.json`.
- **Next**: ACT — build the standard triangulation instance + facet-restriction + door
  bijection (Docker-gated).
