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

---

## Session 2026-06-27 (Session 3) — Step 0 delivered: BaryPoint ≃ Vertex bridge

**Mode**: ORIENT (execute Session-2 step 0). **Outcome**: WROTE the coordinate
bridge as `proofs/Proofs/SpernerNDimOQ02.lean`. **UNVERIFIED** (build host down:
root FS 98% with ~324 MiB free and dropping, stale `lean-build-*` containers,
`SpernerGrid.olean` not cached → a fresh SpernerGrid+Mathlib build risks ENOSPC).
Proofs hand-checked; no `sorry`, no new `axiom`.

### What was built (`SpernerNDimOQ02.lean`, namespace `SpernerNDimOQ02`)

The two coordinate systems are canonically isomorphic and this file proves it:

- `SpernerNDim.Vertex d N` = `{coords : Fin d → ℕ // ∑ ≤ N}` (Kuhn; implicit last
  bary coord `N − ∑`).
- `SpernerGrid.BaryPoint d N` = `{coords : Fin (d+1) → ℕ // ∑ = N}` (full bary).

Declarations:
- `toVertex : BaryPoint d N → Vertex d N` — drop last coord
  (`coords i := b.coords i.castSucc`); validity from `Fin.sum_univ_castSucc`.
- `toBary : Vertex d N → BaryPoint d N` — append slack
  (`coords := Fin.snoc v.coords (N − ∑ v.coords)`); `sum_eq` via
  `Fin.snoc_castSucc`/`Fin.snoc_last`.
- coord simp lemmas `toVertex_coords`, `toBary_coords_castSucc`,
  `toBary_coords_last`.
- `toBary_toVertex` / `toVertex_toBary` — the two round-trips (the BaryPoint
  round-trip splits on `Fin.lastCases`; the last coordinate is recovered from
  `∑ = N`).
- `baryEquivVertex d N : BaryPoint d N ≃ Vertex d N` — **the bridge**, plus
  `_apply` / `_symm_apply` simp lemmas.
- `onFace_toVertex : onFace (toVertex b) k ↔ b.onFace k` — face correspondence
  (`k < d`: both say "k-th coord = 0"; `k = last`: `∑ = N ↔ b_last = 0`).
- `isSperner_iff` — the bridge transports the Sperner boundary condition
  (`SpernerNDim.IsSperner c ↔ SpernerGrid.IsSperner (c ∘ toVertex)`).

This is exactly Session-2 "step 0" and unlocks reuse of the whole `SpernerNDim`
framework over `BaryPoint` without re-deriving it. PR opened (UNVERIFIED).

### Key Lean facts used (for the next session)
- `Fin.sum_univ_castSucc : ∑ i:Fin (n+1), f i = ∑ i:Fin n, f i.castSucc + f (Fin.last n)`.
- `Fin.snoc_castSucc`, `Fin.snoc_last` (both `@[simp]`).
- `cases i using Fin.lastCases with | last => | cast j =>`.
- `omega` discharges the `↔` between linear coordinate equations (used in
  `onFace_toVertex` last-face branch).

### Remaining work (unchanged from Session 2, now starting at Phase 1)
- **Phase 1**: `freudenthal d N : SpernerTriangulation d N` (unoriented Kuhn
  cells, one per geometric cell — no orientation flag). The `baryEquivVertex`
  bridge lets the instance's `vertices` field land in `Vertex d N` directly.
- **Phase 2**: last-face-door-oddness by induction on d (door ↔ panchromatic
  (d−1)-simplex bijection); feed `hbdry` to `sperner_ndim`.
- Reroute `sperner_grid`; retire false `boundary_doors_odd`/`boundary_verts_on_face`.
- **Verify** `SpernerNDimOQ02.lean` once build infra recovers (it is currently
  UNVERIFIED).

---

## Session 2026-06-27 (Session 4) — Phase 1 design: the *unoriented* triangulation

**Mode**: CONTINUE (researcher-7). **Infra**: both verify channels DOWN — build
host critically degraded (root FS 99%, ~167 MiB free and falling, 9 stale
`lean-build-*` containers hung "Up 6 hours"); Aristotle jobs expiring
(`NOT_FOUND`). No build attempted (ENOSPC would crash the host). Deliverable is
design + two safe `Equiv`-derived lemmas (`toVertex_injective`,
`toBary_injective` in `SpernerNDimOQ02.lean`) that the Phase-1 `vertices_injective`
field consumes.

### The crux, restated precisely: why `GridSimplex` double-counts

`SpernerGrid.GridSimplex d N` is an **oriented chain** representation: it stores
`verts : Fin (d+1) → BaryPoint` *in chain order*, an `incDir : Fin d → Fin (d+1)`,
and a `miss : Fin (d+1)`. The geometric object it denotes is the **vertex set**
`{verts 0, …, verts d}`, but a single geometric Freudenthal cell admits *several*
`(verts, incDir, miss)` encodings.

Worked d=1 case (the one that falsifies `boundary_doors_odd`): a geometric edge
`{p, q}` with `q = p + e_i − e_j` has **two** `GridSimplex` encodings —
`(base = p, incDir ≡ i, miss = j)` (chain `p → q`) and
`(base = q, incDir ≡ j, miss = i)` (chain `q → p`). Both are valid `GridSimplex`
values with the same vertex set. The oriented `gridAdj` then treats "cannot do a
boundary flip in *this* orientation" as `adj = none`, so each geometric boundary
facet is counted with the *wrong multiplicity* (the two encodings disagree on
which facet is a boundary door). Hence `boundary_doors_odd` is FALSE for the
`GridSimplex`/`gridAdj` pair, as documented in `SpernerGrid.lean` lines 49–86.

### Phase-1 fix: build the abstract `SpernerTriangulation` over *unordered* cells

`SpernerNDim.SpernerTriangulation d N` (the abstract, 0-sorry framework, line 99)
asks for: `Simplex` (with `DecidableEq` + `Fintype`), `vertices : Simplex →
Fin (d+1) → Vertex d N` (injective per simplex), and an adjacency `adj : Simplex →
Fin (d+1) → Option (Simplex × Fin (d+1))` satisfying `adj_symm`, `adj_vertices`,
`adj_ne`, `adj_unique_facet`, `boundary_face`. Crucially **the abstract framework
never assumes an orientation** — adjacency is a partial involution on
(simplex, dropped-facet) pairs. So the cure is to instantiate it with **one cell
per geometric simplex** and a **dual-graph** (facet-sharing) adjacency.

**Representation decision — canonical `GridSimplex` representative.**
Rather than a fresh `Finset (BaryPoint d N)` subtype (which forces re-proving a
canonical vertex order and a fresh `Fintype`), reuse `GridSimplex` but quotient
out the encoding redundancy by a **canonicality predicate** `IsCanon`:

```
def IsCanon (s : GridSimplex d N) : Prop := s.miss = canonMiss s   -- pick ONE rep
Simplex := { s : GridSimplex d N // IsCanon s }
```

`canonMiss` must select a single encoding per vertex set. A clean choice: the
representative whose chain is **monotone for the lex order on `BaryPoint`** — i.e.
`verts` is strictly increasing in lex, equivalently `miss` is the coordinate that
is positive at the lex-greatest vertex and `incDir` lists the remaining
directions in increasing order. Two facts make this well-defined and unique:
1. A Freudenthal cell's `d+1` vertices are pairwise distinct (`verts_injective`,
   already proven) and **totally ordered** along the chain, so the lex-minimal
   vertex is a unique base.
2. Given the base and the cell's vertex set, `incDir`/`miss` are forced.

(Subtype gives `DecidableEq` for free; `Fintype` for the subtype follows from
`gridSimplexFintype` via `Subtype.fintype` with `IsCanon` decidable.)

**`vertices` field.** `vertices ⟨s, _⟩ k := SpernerNDimOQ02.toVertex (s.verts k)`.
`vertices_injective` = `SpernerNDimOQ02.toVertex_injective ∘ s.verts_injective`
(both now available; `verts_injective` is `GridSimplex.verts_injective`, line 376).

**`adj` field — dual graph (the unoriented core).** For a canonical cell `s` and a
dropped vertex `k`, the facet `F = (vertices s) '' (univ.erase k)` is a set of `d`
barycentric points. Define `adj s k` by searching the (finite) `Simplex` type for
the *unique other* canonical cell `s'` containing `F` as a facet, returning
`some (s', k')` where `k'` is the vertex of `s'` not in `F`; `none` if no such
`s'` exists (boundary facet). Because we now have **one cell per geometry**:
- `adj_symm`: the relation "`s, s'` share facet `F`" is symmetric by construction.
- `adj_unique_facet`: two distinct dropped facets of `s` are distinct point-sets
  (vertices injective ⇒ erasing different `k` gives different images), so they
  cannot both match the same neighbour via the same `s'`. Geometric uniqueness
  ("two `d`-simplices share ≤ one `(d−1)`-face") holds because a shared `d`-set
  determines the cell.
- `adj_ne`: `s ≠ s'` since a non-boundary facet's two cells differ on the dropped
  vertex (they lie on opposite sides of `F`).
- `adj_vertices`: immediate — both images equal `F` by the search predicate.
- `boundary_face`: when no neighbour exists, the `d` retained vertices all lie on
  one geometric face of `Δ_N`; under the bridge this is the Kuhn `onFace`
  condition, transported by `SpernerNDimOQ02.onFace_toVertex`.

This makes the **facet-sharing adjacency a genuine partial involution on
(cell, facet) pairs**, which is exactly what `SpernerNDim`'s parity machinery
(`even_card_fpf_invol`, `interior_doors_even`, `sperner_parity`) needs — and it is
*orientation-free*, so the d=1 double-count cannot recur.

### Phase-2 hand-off (unchanged, now well-posed)

With `freudenthal d N : SpernerTriangulation d N` in hand, `boundary_doors_eq_face_d`
(line 585) already isolates boundary doors to the last face `k = d`. The remaining
content is last-face-door-oddness by induction on `d` via the
door ↔ panchromatic-`(d−1)`-simplex bijection (Session-2 plan). Then apply
`sperner_ndim` (line 654) and transport the Sperner hypothesis across the bridge
with `SpernerNDimOQ02.isSperner_iff`, retiring the false `boundary_doors_odd` /
`boundary_verts_on_face`.

### Concrete next-session checklist (build-gated)

1. Define `canonMiss`/`IsCanon` and prove `IsCanon` decidable + a uniqueness lemma
   (each geometric cell has exactly one canonical encoding).
2. `Simplex`, `DecidableEq`, `Fintype` (subtype boilerplate).
3. `vertices` + `vertices_injective` (one-liners from `toVertex_injective`).
4. `adj` via finite search; discharge the 5 adjacency fields + `boundary_face`.
5. Verify the whole stack once infra recovers, then wire Phase 2.

### Lean facts banked this session
- `(e : α ≃ β).injective` / `e.symm.injective` give `toVertex`/`toBary`
  injectivity with no unfolding (added as named lemmas).
- `GridSimplex.verts_injective` (line 376) + `gridSimplexFintype` (line 283) +
  `gridSimplexDecEq` (line 266) are the reusable handles for the `Simplex` subtype.
- `Subtype.fintype` needs `DecidablePred IsCanon`; keep `canonMiss` computable.

---

## Session 2026-06-27 (Session 5) — design correction from reading `GridSimplex` source

**Mode**: CONTINUE (researcher-7). **Infra**: HARD OUTAGE — root FS at 99%
(~200 MiB free and fluctuating *down*); 9 hung `lean-build-*` containers "Up 6
hours" (corrupt containerd, same as Sessions 3–4). The disk is so full that even
`bash` command **stdout capture** fails with `ENOSPC` — so *no* command that
produces output can run (neither docker nor the `lean env` local fallback). No
build/verify attempted; doing so is impossible and risks crashing the host.
No code written this session (unverifiable hard proofs on a near-full host = false
progress + host risk). Deliverable is read-only source confirmation + one design
correction.

### Confirmed against actual source (`SpernerGrid.lean`)
- `GridSimplex d N` fields are exactly `verts : Fin (d+1) → BaryPoint d N`,
  `incDir : Fin d → Fin (d+1)`, `miss : Fin (d+1)` (+ proof fields
  `miss_ne_inc`, `step_inc`, `step_dec`, `step_same`, `inc_injective`).
  Defn at `SpernerGrid.lean:241`.
- `gridSimplexDecEq` (`:266`) and `gridSimplexFintype` (`:283`, **noncomputable**,
  via `Fintype.ofInjective` on `(verts, incDir, miss)`) confirmed present.
  ⚠️ NOTE: `gridSimplexFintype` is `noncomputable`, so a `Subtype.fintype` built
  on it is noncomputable too — fine for the abstract framework (which only needs
  `Fintype`, not `DecidableEq`-driven computation), but the `adj` finite-search
  must use `Finset.univ.filter`/`Finset.choose` over this `Fintype`, not `decide`.

### Design correction (saves the next session effort)
The Session-4 plan weighed two `Simplex` representations: (A) `{s : GridSimplex //
IsCanon s}` subtype, vs (B) a `Finset (BaryPoint d N)` of cell vertex-sets.
**Reading the source shows the choice does not remove the hard obligation**: both
representations still owe a *canonical vertex ordering* for the
`vertices : Simplex → Fin (d+1) → Vertex` field (a `Finset` has no order, and the
subtype's `verts` order is encoding-dependent). The chain order IS the crux either
way — there is no free lunch. **Recommendation: keep representation (A)** (subtype),
because `GridSimplex.verts` already gives the order *and* the Freudenthal proof
fields (`step_inc`/`step_dec`/`step_same`) for free; (B) would force re-deriving all
of these on the raw `Finset`.
- The canonicalization is well-posed because each Freudenthal cell's `d+1`
  vertices are **totally ordered along the unique mass-transfer chain** from the
  lex-minimal base: `verts_injective` (`:376`) gives distinctness, and `step_dec`
  forces the `miss` coordinate to be strictly decreasing along the chain, so the
  chain direction is geometrically determined once the base is fixed as the
  lex-minimal vertex. Hence `IsCanon s := (s.verts 0 is lex-≤ every other vertex)`
  is a clean, computable canonicality predicate — simpler than the Session-4
  "`miss = canonMiss s`" formulation, and it avoids inverting geometry→`miss`.
- Concrete next step (build-gated, unchanged priority): define
  `IsCanon s := ∀ k, lexLE (s.verts 0) (s.verts k)` with `lexLE` the lattice lex
  order on `BaryPoint` (Fin→ℕ); prove decidable (finite ∀) and
  per-geometry-unique (lex has a unique minimum; base + chain ⇒ full encoding).
