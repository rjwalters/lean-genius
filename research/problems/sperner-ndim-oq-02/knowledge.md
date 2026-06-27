# sperner-ndim-oq-02: Boundary-Door Oddness by Dimensional Induction

## Problem Summary

**Goal**: Prove `SpernerGrid.boundary_doors_odd`: for the concrete Freudenthal grid
triangulation, the count of "boundary doors" (pairs (s, k) with `adj(s,k) = none`
and `IsDoor(c, gridComplex, s, k)`) is odd, for any Sperner coloring c.

This lemma is the key input to `CellComplex.sperner`, which then gives `sperner_grid`.

---

## Session 2026-04-22 (Session 1) - Critical Architectural Finding

**Mode**: FRESH
**Outcome**: BLOCKED — `boundary_doors_odd` is provably FALSE as stated.

### What I Did

1. Read `SpernerGrid.lean` thoroughly to understand the sorry structure (5 sorries)
2. Analyzed the abstract Sperner theorem in `SpernerMathlib4.lean`
3. Worked through a concrete counterexample for d=1, N=1

### Key Finding: `boundary_doors_odd` Is FALSE

**Counterexample**: d=1, N=1, unique Sperner coloring c(1,0)=0, c(0,1)=1.

The `gridComplex 1 1` has **2 GridSimplices** (not 1):
- S1: `miss=0, incDir(0)=1, verts(0)=(1,0), verts(1)=(0,1)`
- S2: `miss=1, incDir(0)=0, verts(0)=(0,1), verts(1)=(1,0)`

Both are valid (satisfy all `GridSimplex` axioms). They represent the **same geometric
edge** [(1,0),(0,1)] in **opposite orientations**.

**All 4 boundary pairs** (S1,k=0), (S1,k=1), (S2,k=0), (S2,k=1) have `adj = none`
(for N=1, all facets are boundary). Door check:
- (S1, k=1): c(verts 0) = c(1,0) = 0. **IS a door.** ✓
- (S1, k=0): c(verts 1) = c(0,1) = 1 ≠ 0. NOT a door.
- (S2, k=0): c(verts 1) = c(1,0) = 0. **IS a door.** ✓
- (S2, k=1): c(verts 0) = c(0,1) = 1 ≠ 0. NOT a door.

**Boundary door count = 2 (EVEN)**. The theorem claims Odd. **FALSE.**

### Root Cause

The `GridSimplex` structure uses ORIENTED simplices with a fixed "miss" direction.
Each geometric simplex appears **twice** in `gridComplex` — once per orientation:
- Orientation 1: `(miss=m1, incDir=σ1, verts=v₀→...→v_d)`
- Orientation 2: `(miss=m2, incDir=σ2, verts=v_d→...→v₀)` (reversed)

Consequence: both panchromatic count and boundary door count are ALWAYS EVEN.
The `sperner_parity` theorem still holds (both even ≡ both even mod 2), but
`CellComplex.sperner` (which needs ODD boundary doors) cannot be applied.

### Verification via `sperner_parity`

For d=1, N=1: panchromatic count = 2 (both S1 and S2 are panchromatic, since both
have vertex set {(1,0),(0,1)} with colors {0,1}). Boundary door count = 2. 
2 ≡ 2 (mod 2) ✓ — `sperner_parity` is consistent, but boundary ≠ odd.

### What IS Correct

- `sperner_parity`: panchromatic count ≡ boundary door count (mod 2) — **TRUE** (proved in SpernerMathlib4)
- `boundary_doors_odd` as stated in SpernerGrid.lean — **FALSE** (false for d ≥ 1)
- `sperner_grid` (conclusion): **TRUE** (panchromatic simplices do exist, count ≥ 2)

### The Fix Required

`boundary_doors_odd` cannot be proved as stated. The proof of `sperner_grid`
needs one of these alternatives:

**Option A: Canonical-orientation sub-complex**
- Define H ⊆ gridComplex using only "canonical" oriented simplices (one per geometric simplex)
- For d=1: choose the simplex with smaller miss coordinate
- H has boundary door count = (# geometric boundary doors) = ODD
- Apply `CellComplex.sperner` to H, conclude panchromatic in H → panchromatic in gridComplex

**Option B: Direct "reversal pairs" argument**
- Every GridSimplex s has a "reverse" s' (same vertex set, opposite orientation)
- s' is always a distinct valid GridSimplex
- panchromatic count in gridComplex = 2 × (# geometric panchromatic) = 2 × (odd) ≥ 2
- Requires proving the geometric count is odd via a separate argument

**Option C: Use SpernerNDim abstract structure**
- SpernerNDim.lean already has a working abstract Sperner theorem
- Define a `SpernerTriangulation` instance for the Freudenthal grid (with UNORIENTED simplices)
- Apply the existing abstract theorem

**Recommendation**: Option C is cleanest since the infrastructure in SpernerNDim.lean
already handles the parity argument correctly (using unoriented abstract simplices).

### Files Modified

None — pure analysis session.

### Other Sorries in SpernerGrid.lean

Beyond the false `boundary_doors_odd`, there are 2 other provable sorries:
1. `gridAdj_symm` (line 1154): adjacency symmetry — PROVABLE by case analysis
2. `gridAdj_vertex` (line 1163): shared vertices — PROVABLE for interior case at least
3. `boundary_verts_on_face` (line 1239): also appears incorrect (used only for `boundary_doors_odd` chain, which is now known-false)

### Next Steps

1. **Architectural decision**: Choose Option A, B, or C above
2. If Option C: define `SpernerTriangulation` instance for Freudenthal grid and apply SpernerNDim.sperner
3. Optionally prove `gridAdj_symm` and `gridAdj_vertex` (useful for any gridComplex application)
4. Remove or replace `boundary_doors_odd` and `boundary_verts_on_face` with correct formulations

---

## Session 2026-06-27 (Session 2) — Option C locked + inductive decomposition

**Mode**: ORIENT (build on Session 1). **Outcome**: ANALYSIS — confirmed scope,
produced the concrete inductive proof structure the next session can execute.
No verified Lean written this session (rationale below).

### Re-survey of current code state

Since Session 1 the `SpernerGrid.lean` file was refactored. Current `sorry` count = 2:

| Line | Decl | Status |
|------|------|--------|
| 164  | `CellComplex.sperner` | intentionally `sorry`'d — duplicate of `SpernerMathlib4.sperner`, kept so the file builds standalone. NOT our target. |
| 1740 | `boundary_doors_odd` | the OQ target — `sorry` with a full counterexample comment block (d=1,N=1 → count 2, EVEN). Still FALSE as stated. |

The two earlier "provable" auxiliary sorries (`gridAdj_symm`, `gridAdj_vertex`,
`boundary_verts_on_face`) are no longer present as sorries — already resolved or
removed in the refactor. So the ONLY mathematical gap is the false
`boundary_doors_odd` and its consumer `sperner_grid` (line 1757).

### The abstract framework already gives us the finish line (Option C confirmed)

`SpernerNDim.lean` is **complete, 0 sorries, 669 lines**. Relevant API:

- `structure SpernerTriangulation (d N : ℕ)` (line 99) — **8 fields**:
  `Simplex`, `simplex_decidableEq`, `simplex_fintype`, `vertices`,
  `vertices_injective`, `adj`, `adj_symm`, `adj_vertices`, `adj_ne`,
  `adj_unique_facet`, `boundary_face`.
- `theorem sperner_ndim (c) (K : SpernerTriangulation d N) (hc : IsSperner c)`
  `(hbdry : Odd #{(s,k) | isDoorAt c K s k ∧ K.adj s k = none ∧ k = Fin.last d})`
  `: ∃ s, IsFC c K s` (line 654). **This is exactly what `sperner_grid` needs.**

So Option C = "construct a `SpernerTriangulation d N` instance for the unoriented
Freudenthal grid, supply the `hbdry` oddness, apply `sperner_ndim`." Two real
deliverables remain: the **instance** (Phase 1) and the **`hbdry` oddness by
induction on d** (Phase 2). Phase 2 is literally the OQ title
("Boundary-Door Oddness by Dimensional Induction").

### Coordinate-system note (important gotcha for the bridge)

The abstract framework uses `SpernerNDim.Vertex d N` = `{coords : Fin d → ℕ // ∑ ≤ N}`
(Kuhn cube-corner coordinates, implicit last bary coord = N − ∑).
`SpernerGrid` uses `BaryPoint d N` = `{coords : Fin (d+1) → ℕ // ∑ = N}`
(full barycentric). These are **canonically isomorphic**:
`BaryPoint d N ≃ Vertex d N` via `bary ↦ (i ↦ bary.coords i.castSucc)` (drop last)
and `vtx ↦ (append (N − ∑ vtx) as last coord)`. Proving this `Equiv` (≈30–50 lines,
self-contained, no hard adjacency) is the cleanest standalone first PR and lets the
entire `SpernerNDim` framework be reused over `BaryPoint` without re-deriving it.

### Phase 2 — the inductive door-oddness, worked out precisely

Target: `Odd #{(s,k) | isDoorAt c K s k ∧ K.adj s k = none ∧ k = Fin.last d}`
for the Freudenthal instance `K` and any Sperner `c`. **Induction on d.**

**Last-face doors ↔ panchromatic (d−1)-simplices.** Decode the three conjuncts
for a pair `(s, k)` with `k = Fin.last d`:
- `K.adj s (Fin.last d) = none` ⟹ (by the `boundary_face` field) every vertex
  `vertices s j` with `j ≠ last` satisfies `onFace · (Fin.last d)`, i.e. lies on
  **face d** (last bary coord 0 / `∑ coords = N`). So the facet is one of the
  `d`-vertex simplices sitting inside face d.
- The d vertices on face d are exactly a top-dimensional simplex of the induced
  triangulation **of face d**, which is itself the Freudenthal grid of the
  **(d−1)-simplex** with the same parameter N (this is the OQ's stated geometric
  fact: "the face-d restriction of the Freudenthal triangulation is a
  lower-dimensional Freudenthal grid").
- `isDoorAt c K s (Fin.last d)` ⟹ those d vertices carry **all** colors
  `{Fin.castSucc j : j : Fin d} = {0,…,d−1}`. Color d cannot appear there: by
  `IsSperner`, any vertex `onFace (Fin.last d)` has `c v ≠ Fin.last d`. Hence the
  restricted coloring `c' : Coloring (d−1) N` is well-defined into `Fin d`, is
  Sperner, and the facet is **panchromatic** (`IsFC c' K'`) for the (d−1)-grid `K'`.

This correspondence is a **bijection** between
`{last-face boundary doors of the d-grid}` and `{IsFC simplices of the (d−1)-grid K'}`.
Therefore
`#{last-face doors of K} = #{IsFC of K'}`.

**Close by induction.** By `sperner_parity c' K' (Sperner c')` at dimension d−1,
`#{IsFC of K'} ≡ #{last-face doors of K'} (mod 2)`, and by the inductive hypothesis
the latter is **odd**. Hence `#{last-face doors of K}` is odd.

**Base case d = 0.** `Fin (d+1) = Fin 1`; the door color set `{0,…,d−1}` is empty,
so `isDoorAt` is vacuously true and `Fin.last 0 = 0`. The 0-grid has exactly one
simplex with one boundary facet ⟹ count = 1, odd. ✓

(Equivalently one can run the induction directly through `sperner_ndim` at d−1 to
get an FC simplex and `sperner_parity` for the count; the parity version above is
what feeds `hbdry`.)

### Phase 1 — the instance, field-by-field plan

Construct `freudenthal d N : SpernerTriangulation d N` (Kuhn/Freudenthal
triangulation, **unoriented**, one simplex per geometric cell — this is what kills
the orientation-doubling bug from Session 1):

- `Simplex` := a Kuhn cell = (base lattice point `b`) + (permutation π of `Fin d`
  giving the order in which unit coordinates are incremented). Vertices are the
  monotone chain `b = v₀ ⊂ v₁ ⊂ … ⊂ v_d` where `v_{m} = b + ∑_{i<m} e_{π(i)}`.
  Encode so that **each geometric d-cell has exactly one representative** (do NOT
  carry a free `miss`/orientation flag — that was the Session-1 bug).
- `vertices`, `vertices_injective` — chain is strictly increasing ⟹ injective.
- `adj` — facet `k` (drop vertex `v_k`) pairs with the neighbour obtained by the
  standard Kuhn pivot (swap adjacent transposition / step base point); `none` iff
  the pivot leaves the simplex (geometric boundary).
- `adj_symm`, `adj_ne`, `adj_unique_facet` — standard Kuhn-pivot involution facts.
- `adj_vertices` — pivot preserves the shared facet's vertex set.
- `boundary_face` — the crux linking `adj = none` to `onFace`: a dropped facet is on
  the boundary exactly when its d vertices share a zero/saturated coordinate, i.e.
  lie on a face of the big simplex. This field is what Phase 2 consumes.

Estimated size: Phase 1 ≈ 250–400 lines, Phase 2 ≈ 150–250 lines. Multi-session.
Recommend landing the `BaryPoint ≃ Vertex` Equiv first (small, verifiable), then
Phase 1, then Phase 2.

### Why no verified Lean this session

1. The OQ target is provably FALSE as stated (Session 1); the real work is the
   Phase-1 instance + Phase-2 induction above, which is a multi-session,
   ~400–650-line build that must be machine-checked to have value (the role
   explicitly discourages adding unverifiable scaffolding).
2. Build infrastructure was degraded at session time: root filesystem at 97%
   (~420 MiB free) with two ~5-hour-old `lean-build-*` docker containers still
   running. Triggering a fresh Mathlib docker build under those conditions risks
   filling the disk; new Lean could not be safely verified. Producing the precise
   decomposition above is the honest increment until infra recovers.

### Revised Next Steps (supersede Session 1's list)

1. **(small, do first)** Prove `BaryPoint d N ≃ Vertex d N` in a bridge file;
   verify it builds. Self-contained, no adjacency.
2. **(Phase 1)** Define `freudenthal d N : SpernerTriangulation d N` (unoriented
   Kuhn cells, one per geometric simplex); discharge the 8 structure fields.
3. **(Phase 2)** Prove last-face-door-oddness by induction on d using the
   door ↔ panchromatic bijection above; feed it to `sperner_ndim`.
4. Replace `SpernerGrid.boundary_doors_odd`/`sperner_grid` to route through the new
   instance (or restate `sperner_grid` directly via `sperner_ndim` over `BaryPoint`).
5. Delete the false `boundary_doors_odd`/`boundary_verts_on_face` once `sperner_grid`
   no longer depends on them.

**Status flag**: not BLOCKED (path is concrete and the abstract finish line exists),
but **large + infra-gated**. Treat as a staged build for a session with healthy
build infra; start with step 1.
