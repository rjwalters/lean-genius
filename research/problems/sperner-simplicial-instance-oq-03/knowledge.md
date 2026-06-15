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

**Key re-scoping (Session 2).** The induction does NOT need a fresh door-counting
argument — the parity engine is already proven elsewhere in the gallery.
`proofs/Proofs/SpernerNDim.lean:601` proves (**0 sorries, 0 axioms**) the abstract
theorem `sperner_parity`:

> `#FC simplices ≡ #(boundary doors on face d)  (mod 2)` for any `SpernerTriangulation d N`,

where `IsFC s` = the coloring is surjective on `s`'s `d+1` vertices (panchromatic) and
`isDoorAt s k` = the `d` vertices `≠ k` carry all colors `{0..d-1}`. The doors on the top
facet of `Δⁿ` are exactly the **FC cells of the `Δⁿ⁻¹` coloring induced on that facet**, so

> `_hLastFace[n]`  =  "Odd #FC of the induced `Δⁿ⁻¹` Sperner coloring"
>                  =  (via `sperner_parity[n-1]`)  "Odd #(face-(n-1) boundary doors)"  =  `_hLastFace[n-1]`,

recursing to the `n=1` base. Hence the open Lean work is the cross-dimensional
**facet-restriction map** wiring `SpernerSimplicialInstance.Triangulation` to
`SpernerNDim.SpernerTriangulation` — both already sorry-free — **not a new parity proof**.

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
| `sperner_parity` on 2-D Kuhn mesh, m=1..4 | up to 13 824 | `#FC ≡ #(face-2 boundary doors)  (mod 2)` — confirms the abstract `SpernerNDim` theorem instantiates on the concrete triangulation the ACT will build |
| dim-3 → dim-2 reduction, facet grid m=1..4 | up to 13 824 | restriction is Sperner (induced coloring ⊆ {0,1,2}); `#(top-facet doors of Δ³) == #FC of induced Δ² coloring == odd` — discharges `_hLastFace[3]` mesh-free |

This grounds the base case, the `S = S_n` reduction, the induction bridge, the
`sperner_parity` instantiation, and the dim-3 discharge of `_hLastFace` — all without a
Lean build (Docker down this session).

---

## Dead Ends / Cautions

- Do **not** try to re-prove `boundary_doors_odd` as a whole — it is already a proven
  theorem. Target the `_hLastFace` hypothesis specifically.
- The file currently has only `intervalTriangulation 1` (n=1) and a single 2-simplex
  fixture — no general standard/Kuhn triangulation instance. That construction is the
  prerequisite for the induction and is the main build work.

---

## Next Steps (ACT, build-gated) — re-scoped to reuse `sperner_parity`

1. Construct an explicit standard/Kuhn `SpernerTriangulation`/`Triangulation` instance
   for general `n`.
2. Define the **facet-restriction** map (top facet of dim-`n` triangulation → dim-`(n-1)`
   `SpernerTriangulation`) and prove the restricted coloring is Sperner (color `n` is
   forbidden on every top-facet vertex — nearly definitional).
3. Prove the **door ⟺ FC identification**: a dim-`n` top-facet door (the `d` vertices
   `≠ apex` carry `{0..n-1}`) ⟺ the corresponding dim-`(n-1)` triangle is `IsFC`.
4. Conclude `_hLastFace` from **`SpernerNDim.sperner_parity` applied in dim `n-1`** + IH,
   base case `n=1`. **Do NOT re-prove the parity counting** — it is already sorry-free.
   This is smaller than the prior "~200–400 LOC from scratch" estimate; the work is the
   structural wiring between two existing sorry-free files. The door⟺FC lemma is a good
   Aristotle candidate once the instances compile.

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

### 2026-06-14 (Session 2) — ORIENT (re-scope + cross-link)

**Mode**: CONTINUE · **Outcome**: progress (ACT re-scoped; Docker down)

- Surveyed the sibling Sperner Lean files and found the abstract parity engine
  `SpernerNDim.sperner_parity` (`SpernerNDim.lean:601`, **0 sorries / 0 axioms**):
  `#FC ≡ #(face-d boundary doors) (mod 2)` for any `SpernerTriangulation d N`.
- Realized `_hLastFace` is dischargeable by **citing** `sperner_parity` in dim `n-1`
  on the induced facet coloring — the open work is the cross-dimensional facet-restriction
  map between two already-sorry-free frameworks, not a fresh parity proof. Re-scoped the
  ACT accordingly (smaller than the prior 200–400 LOC estimate).
- Extended `verify_boundary_doors.py` with two new checks (all pass): (i) `sperner_parity`
  congruence on the concrete 2-D Kuhn mesh; (ii) the dim-3 → dim-2 reduction that
  discharges `_hLastFace[3]` mesh-free (restriction-is-Sperner + door==FC == odd).
- **Files**: `verify_boundary_doors.py`, `knowledge.md`, `state.md`, research JSON.
- **Next**: ACT (Docker-gated) — instantiate the general-n triangulation, build the
  facet-restriction map, prove door⟺FC, close `_hLastFace` via `sperner_parity[n-1]`.
