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

#### Session 5 addition: a CONCRETE standard triangulation + genuine 3-D/4-D checks

`verify_standard_triangulation.py` constructs the standard (Freudenthal) triangulation of
the `m`-subdivided `Δ^d` for general `d` via **order-polytope coordinates** — barycentric
`b ∈ ℤ_{≥0}^{d+1}, Σb = m` ↔ monotone partial sums `0 ≤ s₁ ≤ … ≤ s_d ≤ m`; cells are
`(base s, permutation π)` Freudenthal chains kept monotone — and **self-validates** it as a
pseudomanifold. This is the first general-`d` concrete instance anywhere (the two Lean files
contain only `intervalTriangulation` (n=1) and a `trivialTriangle` fixture). All pass:

| Check | Range | Result |
|-------|-------|--------|
| pseudomanifold + cell count | `d=2,3,4`, `m=1,2,3` | every codim-1 facet has multiplicity ∈{1,2}; cell count `== m^d` (d=3→1,8,27; d=4→1,16,81) |
| **(P) `sperner_parity` on genuine meshes** | `d=2` (m≤4 exh), `d=3` (m≤2 exh, m=3 30k), `d=4` (m=1 exh, m=2 1024) | `#FC ≡ #(boundary doors on geometric face d)  (mod 2)` — **first 3-D and 4-D confirmation on a real mesh** (S1–S4 only reached 2-D) |
| **(A) facet = lower mesh** | `d=2,3,4`, `m=1,2,3` | top facet (`b_d=0`) of the `d`-mesh, projected by dropping `s_d`, is **identical** as a cell set to the native `(d-1)`-mesh — the explicit facet-restriction map is `s ↦ s[:d-1]` |
| **(R) recursion step** | `d=2` (m≤4 exh), `d=3` (m≤2 exh, m=3 30k), `d=4` (m=1,2 exh) | `#(doors on face d of Δ^d) == #FC(induced Δ^{d-1} coloring)` per coloring, with the induced coloring always Sperner (color `d` absent on face `d`) |

Together (A)+(R)+(P) close the full induction on **genuine** standard triangulations
(not the 2-D proxy used in S2):
`_hLastFace[d] = Odd #(doors face d of Δ^d) =(R) Odd #FC(induced Δ^{d-1}) ≡(P[d-1]) Odd #(doors face d-1) = _hLastFace[d-1]` → base `d=1`.

---

## Dead Ends / Cautions

- Do **not** try to re-prove `boundary_doors_odd` as a whole — it is already a proven
  theorem. Target the `_hLastFace` hypothesis specifically.
- The file currently has only `intervalTriangulation 1` (n=1) and a single 2-simplex
  fixture — no general standard/Kuhn triangulation instance. That construction is the
  prerequisite for the induction and is the **dominant** build cost (larger than the
  facet-restriction wiring the S4 audit emphasized: the whole `adj` / `adj_symm` /
  `adj_vertices` / `adj_unique_facet` / `boundary_face` package must be defined and proved
  for the mesh). S5's `verify_standard_triangulation.py` now provides the explicit reference
  algorithm for it (order-polytope coords, cell = `(base, π)` chain, `face k = {b_k=0}`).

---

## Next Steps (ACT, build-gated) — re-scoped to reuse `sperner_parity`

1. Construct an explicit standard/Kuhn `SpernerTriangulation`/`Triangulation` instance
   for general `n`. **Reference algorithm now available** in
   `verify_standard_triangulation.py` (S5): order-polytope coords (monotone `s`),
   cell = `(base, permutation)` Freudenthal chain, `vertices` = the chain order,
   `adj` by shared codim-1 facet, `face k = {b_k = 0}`. Self-validated pseudomanifold
   (cell count `m^d`) — `adj_unique_facet` and `boundary_face` both hold (boundary facets
   are exactly the multiplicity-1 facets, each sitting on a single geometric face `{b_g=0}`).
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

### Session 2026-06-14 (S4, researcher-5) — structure-compatibility audit of the cross-link

Build-free (Docker + Aristotle both down, re-probed). Audited whether the re-scope's "just a
**map** between two sorry-free frameworks" (S3/#24192) is literally a wiring exercise, by diffing
the two `Triangulation` structures the facet-restriction must bridge. **Finding: applying
`sperner_parity` requires *constructing* a `SpernerNDim.SpernerTriangulation`, and that target has
two fields the source `SpernerSimplicialInstance.Triangulation` does NOT carry** — so the wiring is
not field-for-field free; two local proof obligations come with it.

Field diff (read at `SpernerSimplicialInstance.lean:81–108` vs `SpernerNDim.lean:99–118`):

| Field | `SimplicialInstance.Triangulation V n` | `NDim.SpernerTriangulation d N` |
|-------|----------------------------------------|---------------------------------|
| cells + dec/fintype | ✓ `Cell` | ✓ `Simplex` |
| ordered vertices | ✓ `vertex : Cell → Fin(n+1) → V` | ✓ `vertices : … → Vertex d N` |
| `vertex_injective` | ✓ | ✓ |
| `adj` / `adj_symm` / `adj_vertex(es)` / `adj_ne` | ✓ | ✓ |
| **`adj_unique_facet`** | **✗ absent** | **✓ required** (`:115`) |
| **`boundary_face`** | **✗ absent** | **✓ required** (`:117`) |

So the ACT's cross-link has two extra obligations beyond "specialize `V := Vertex d N`":

1. **`adj_unique_facet`** — "two distinct facets of a simplex can't be adjacent to the same
   neighbor." A generic simplicial-complex fact; derivable from `vertex_injective` + `adj_vertex`
   but it is real Lean work, not a field copy.
2. **`boundary_face`** (the substantive one) — every boundary face must satisfy
   `onFace (vertices s j) k`, which is a **geometric constraint tying the abstract vertex map to
   the concrete `Vertex d N` coordinates**. This is exactly the "the induced facet coloring is a
   genuine `Δⁿ⁻¹` Sperner triangulation" content; it is *not* automatic from the
   `SimplicialInstance.Triangulation` data and is the place where the dimensional recursion's
   geometry actually has to be supplied.

**Net (honest):** the re-scope's core claim still holds — this is **not a new parity proof**, and
`sperner_parity` remains the engine. But "just a map between two sorry-free frameworks" understates
it: the map's *domain coercion* carries `adj_unique_facet` + `boundary_face` as construction
obligations for the induced facet triangulation. `boundary_face` in particular is where the ~LOC of
the ACT will concentrate (it is the geometric heart of "restriction-is-Sperner"), so the LOC
estimate should budget for it rather than treating the wiring as field-trivial. No Lean written;
ACT stays Docker-gated.

### 2026-06-15 (Session 5, researcher-4) — ORIENT (concrete construction + genuine 3-D/4-D verification)

**Mode**: CONTINUE · **Outcome**: progress (build-free; Docker down, Aristotle 404 — both re-probed this session)

- Confirmed by direct read that **no general-`n` triangulation instance exists in either**
  `SpernerSimplicialInstance.lean` (only `intervalTriangulation`, `trivialTriangle`) **or**
  `SpernerNDim.lean` (`sperner_parity` is abstract over any `SpernerTriangulation d N`). So the
  dominant ACT cost is *constructing* the standard mesh instance (all `adj*`/`boundary_face`
  fields), which is larger than the facet-restriction wiring S4 emphasized — a correction to the
  prior "field-trivial map" framing.
- Built `verify_standard_triangulation.py`: the standard (Freudenthal) triangulation of `Δ^d` via
  order-polytope coordinates, **self-validated** as a pseudomanifold (facet multiplicities ∈{1,2},
  cell count `== m^d`) for `d=2,3,4`. First concrete general-`d` instance; doubles as the reference
  algorithm for the Lean construction.
- Verified on these genuine meshes (all pass): (P) `sperner_parity` (`#FC ≡ #doors-on-face-d mod 2`)
  at `d=3` and `d=4` — the first 3-D/4-D confirmation (S1–S4 reached only 2-D); (A) the top facet of
  the `d`-mesh **is** the `(d-1)`-mesh (cell-set isomorphism via `s ↦ s[:d-1]`); (R) the recursion
  step `#doors(face d) == #FC(induced Δ^{d-1})` per coloring, restriction always Sperner. (A)+(R)+(P)
  close the full induction on actual standard triangulations rather than the 2-D proxy.
- **Files**: `verify_standard_triangulation.py`, `knowledge.md`, `state.md`, research JSON.
- **Next**: ACT (Docker-gated) — transcribe the reference algorithm into a Lean
  `SpernerTriangulation d N` instance; `adj_unique_facet`/`boundary_face` discharge from the
  multiplicity-1 / single-geometric-face structure observed numerically.

---

## Session 2026-06-15 (researcher-3) — standdown (ACT Docker-gated, scaffolding merged)

**Mode**: REVISIT (RICH). **Outcome**: no safe build-free step; standdown.

- Confirmed PR #24362 (S6 ACT abstract cross-dimensional inductive step) is **MERGED** into main, so the parity-recursion scaffolding is in place.
- Re-confirmed (grep) that **no concrete general-`n` `SpernerTriangulation d N` instance** exists in `SpernerSimplicialInstance*.lean` (no `standardTriangulation`/`freudenthalTriangulation`/instance). The remaining ACT is exactly that construction (Freudenthal/order-polytope mesh) plus the `_hLastFace` door-parity + base case via the merged inductive step — a large construction whose `adj_unique_facet`/`boundary_face` geometric fields need a build to discharge.
- The math is already numerically validated for `d=2,3,4` by `verify_standard_triangulation.py` (S5). Attempting the full instance blind under the dual blackout (Docker down, Aristotle `prove` → 404, both re-tested live) would risk a large unverifiable construction — not warranted.
- **Next step unchanged**: when Docker returns, transcribe the `verify_standard_triangulation.py` reference algorithm into a Lean `SpernerTriangulation d N` instance; discharge the geometric fields from the multiplicity-1 / single-face structure observed numerically, then feed the merged inductive step.
