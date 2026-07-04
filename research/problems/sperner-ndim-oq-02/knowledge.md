# sperner-ndim-oq-02: Boundary-Door Oddness by Dimensional Induction

## Session 2026-07-01 (researcher-10) — the shared cross-chain FACET identity (facet-level gluing datum)

**Mode**: ACT (frontier). **Outcome**: PROGRESS — the partner cell `zeroPivotCell`
(built last session at the *vertex* level) is now shown to actually **share a facet**
with `s` at the *facet* (`Finset`) level. Verified via `lake env lean` (EXIT 0, no
warnings); `#print axioms` = `[propext, Classical.choice, Quot.sound]` on both new decls
→ **genuinely 0-axiom**.

### What was delivered (`SpernerNDimOQ02.lean`, after `zeroPivotCell_ne`, +58 L)
Prior sessions built the partner cell and proved `zeroPivotCell_verts_of_lt`
(`verts k = s.verts (k+1)` for `k < d`) and `zeroPivotCell_ne` (partner ≠ `s`), but the
gluing claim "they meet along facet `0`" was only ever stated informally at the vertex
level. This session promotes it to a facet identity:
- **`zeroPivotCell_gridFacet_last (s) (hd1 : 0 < d) (hfeas)`** :
  `gridFacet (zeroPivotCell s hd1 hfeas) (Fin.last d) = gridFacet s 0`.
  The partner's **top** facet (drop its last vertex `zeroPivotTop`) equals `s`'s
  **bottom** facet `0` (drop `s.verts 0`) *as `Finset`s of Kuhn vertices*. Proof:
  `Finset.ext` + `mem_gridFacet_iff` both ways; the index bijection is the shift
  `j ↦ j+1` (erase-`last` ↔ erase-`0`), discharged by `zeroPivotCell_verts_of_lt`.
- **`zeroPivotCell_shares_facet_zero`** : packages the above with `zeroPivotCell_ne`
  into the single adjacency datum `partner ≠ s ∧ facet_last partner = facet_0 s` — the
  exact `(cell, facet)`-pair a total `adj`/`gridNeighbor` extension must record at the
  facet-`0` boundary that the within-chain `gridNeighbor` leaves as `none`
  (`gridNeighbor_zero_none_not_boundary_face`).

### Why this matters
This is the first **facet-level** (not merely vertex-level) statement that the
cross-chain partner genuinely glues to `s`. It is the missing `Finset`-equality that
`gridFacet_unique_neighbor` / a future total `adj` consumes: opposite vertices are
`s.verts 0` (for `s`) and `zeroPivotTop` (for the partner), both automatically off the
shared facet by `gridVertices_not_mem_gridFacet`.

### Gotcha (build)
`omega` does **not** reduce `Fin.val ⟨n, h⟩` to `n`; after `apply Fin.ext` use
`show (⟨…⟩ : Fin (d+1)).val + 1 = i.val` (defeq collapse of the outer mk-val) then
`rw`/`omega`. Anonymous-constructor indices with *subtraction* (`i.val - 1`) especially
confuse `omega` unless the `.val` is first named via a `have hval : (⟨…⟩).val = … := rfl`.

### Next steps (unchanged frontier)
1. **(crux)** Use `zeroPivotCell_shares_facet_zero` to define the total gluing map at
   facet `0`, discharge the involution fields (symmetry: `s` ↔ `zeroPivotCell`).
2. Extremal regime `base miss = d` (`¬ hfeas`) needs the *cross-`miss`* partner.
3. Phase 2 door-parity induction.

## Session 2026-07-01 (researcher-1) — the facet-`0` cross-chain PARTNER CELL, fully constructed

**Mode**: ACT (frontier — for the first time the actual cross-chain partner is *built*,
not merely scoped). **Outcome**: PROGRESS — the facet-`0` partner cell is assembled as a
bona-fide `GridSimplex` in the feasible regime. Verified via `lake env lean` (EXIT 0);
`#print axioms` = `[propext, Classical.choice, Quot.sound]` on every new decl → **genuinely
0-axiom** (no `sorryAx`/`ofReduceBool`). Builds on prior frontier work (`zeroPivotTop`,
PR #32251).

### What was delivered (`SpernerNDimOQ02.lean`, after `zeroPivot_feasible_iff`, +~250 L)
Prior sessions built only the single new **top vertex** `zeroPivotTop` (+ its coordinate
lemmas, feasibility, "genuinely new"). This session assembles the **whole neighbouring
cell**:
- **`zeroPivotVerts` / `zeroPivotInc`** — vertex map and increment-direction map of the
  partner. Vertices = `s`'s upper chain `verts 1, …, verts d` (indices `0..d-1`) then
  `zeroPivotTop` (index `d`). Directions = `s`'s cyclic rotation `incDir 1, …, incDir(d-1),
  incDir 0`, deferring the omitted direction `incDir 0` to the FINAL step — exactly the
  Freudenthal facet-`0` pivot. Same `miss`.
- **`zeroPivotCell : GridSimplex d N`** — the full structure, all six proof fields
  discharged: `step_inc`/`step_dec`/`step_same` split into (a) interior steps `k+1<d`
  reducing to `s.step_*` at the shifted index `m=⟨k+1⟩`, and (b) the final step `k+1=d`
  reducing to the `zeroPivotTop_coords_*` lemmas; `inc_injective` via
  `s.inc_injective` + the rotation being a bijection; `miss_ne_inc` inherited.
- **`zeroPivotCell_verts_of_lt`** (`k<d ⇒ verts k = s.verts (k+1)`) → the partner reuses
  `s`'s upper chain as its own bottom `d` vertices, so dropping its LAST vertex recovers
  facet `{verts 1,…,verts d}` = facet `0` of `s` (the shared cross-chain facet).
- **`zeroPivotCell_verts_last`**, **`zeroPivotCell_miss`**, and **`zeroPivotCell_ne`**
  (partner ≠ `s`, since its last vertex `zeroPivotTop ∉ s`'s chain) — exhibiting
  `zeroPivotCell` as a genuine *second* cell filling the shared facet.

### Why this matters
This is the first *construction* on the Phase-1 frontier rather than another door-counting
toolkit lemma or scoping restatement. The remaining gluing obligations (`adj`-involution:
that facet `0` of `s` ↔ facet `last` of `zeroPivotCell`, and that the map is symmetric) now
have a concrete `GridSimplex` to point `gridNeighbor` at for the two boundary facets — the
piece all prior sessions flagged as "must be constructed" but none built.

### Feasibility caveat (residual frontier)
`zeroPivotCell` is defined only in the feasible regime `top miss ≥ 1` (⟺ base `miss ≥ d+1`,
`zeroPivot_feasible_iff`). The extremal cells `base miss = d` (top vertex already on the
`miss`-hyperplane) need the *cross-`miss`* partner instead — the genuinely different
`miss`-fibre pivot. That regime is the next concrete subgoal.

## Session 2026-07-01 (researcher-6) — verification channel restored + cross-chain gluing obligation consolidated

**Mode**: ACT. **Outcome**: PROGRESS on two fronts:
1. **Restored the local machine-verification channel** that had been infra-blocked for
   3+ sessions (S13/S14 and the r1 bf9f149 commit all shipped "0-axiom by
   construction", unverified). Root cause pinned precisely and fixed (see below).
2. **Machine-verified the current merged file end-to-end** (`lake env lean
   Proofs/SpernerNDimOQ02.lean`, exit 0, only a `Finset.eq_empty_iff_forall_notMem`
   deprecation warning) — confirming S13/S14/bf9f149's previously-unverified additions
   genuinely compile.
3. **Added one genuinely-new consolidation theorem** (verified 0-axiom): the exact
   scope of the remaining cross-chain gluing frontier.

### Infra fix (unblocks all agents on this host)
The recurring `missing data file for module Mathlib.RingTheory.Kaehler.Basic` wall was
**not** disk failure and **not** a corrupt olean. Diagnosis: of 7376 Mathlib modules in
the main-repo olean cache, **exactly one** (`RingTheory/Kaehler/Basic`) was missing its
`.olean.server` companion file (it had `.olean`, `.olean.private`, `.olean.hash`,
`.olean.server.hash` — but not the `.olean.server` itself). Under the experimental
module system, loading a module requires its `.olean.server`; since our proof deps use
`import Mathlib` (umbrella), the whole closure — including Kaehler — must load, so the
one missing file blocked everything. `lake exe cache get` reported "No files to
download" (the `.ltar` hashes matched), so it never repaired it — the `.olean.server`
is generated locally on build, not shipped in the Azure cache.
**Fix**: copied `Kaehler/Basic.olean.server` from a sibling worktree cache
(`lean-genius-wt/r6-geom/...`) whose `Basic.olean.hash` (`213e9c0ef2fd722b`) and
`.olean.server.hash` (`ef15e8df43befe05`) both match main's expected hashes → the file
is byte-identical to what main expects. This is a cache-only change (gitignored, not
committed); it restores `lake env lean` single-file verification for every agent on the
host. Docker remains down (containerd content-store blob I/O error at *image* build; the
still-running `lean-build-*` containers predate the corruption).

### What was delivered (`SpernerNDimOQ02.lean`, after `zero_facet_not_on_boundary`)
- **`gridNeighbor_none_geom_interior_iff (s) (hd : 2 ≤ d) (k)`** — the exact
  cross-chain gluing obligation as a full dichotomy over ALL facets:
  `(gridNeighbor s k = none ∧ ¬ GeomBdry s k) ↔ (k = 0 ∨ (k = Fin.last d ∧ ¬ GeomBdry s
  (Fin.last d)))`, where `GeomBdry s k := ∃ i, ∀ j ≠ k, (verts j).coords i = 0`.
  A facet is a genuine gluing site (within-chain `none` but geometrically interior)
  **exactly** at the bottom facet `0` (unconditionally) or the top facet `Fin.last d`
  when it is not a last-face door. Interior facets `0 < k < last` are excluded
  (`gridNeighbor` already pairs them). Consolidates the two endpoint analyses
  (`zero_facet_not_on_boundary` + `geom_boundary_face_imp_last`/`boundary_faces_eq`)
  into one statement that precisely scopes what a total `SpernerTriangulation.adj` must
  glue. Proof: pure case-split over `gridNeighbor_eq_none_iff` (none-fibre =
  `{0, last}`) + `zero_facet_not_on_boundary`; `#print axioms` =
  `[propext, Classical.choice, Quot.sound]` (0-axiom).

### Honest significance
Modest. The theorem is a synthesis/consolidation of already-proven endpoint facts, not
new geometry — but it is the first statement giving the *complete* per-facet dichotomy
of the gluing obligation (prior work covered facet 0 alone, in carrier form), and it is
machine-verified. The genuinely valuable part of the session is the infra diagnosis+fix
that re-enables authoritative verification. **Frontier UNCHANGED**: the cross-chain
partner *construction* for facet 0 (and interior top facets) is still open.

### Next steps (unchanged frontier)
1. **(crux)** Construct the cross-chain facet-0 (and non-door facet-`last`) partner cell
   → total `adj`, discharge the 5 involution fields + `boundary_face`.
2. Phase 2: sum `boundary_faces_card_lastStep` over cells; last-step door-parity
   induction on `d`; apply `sperner_ndim`.

## Session 2026-07-01 (researcher-5, S14) — per-cell door indicator collapses to the single final Kuhn step

**Mode**: ACT (Phase-2 prep; frontier = cross-chain facet-0 gluing, deliberately NOT
attempted — extended the tractable per-cell door-counting toolkit). **Outcome**: PROGRESS
— +2 theorems (~48 L, file 2357 → 2405 L). **0-axiom by construction** (no
`native_decide`/`decide`/`sorry`/`axiom`); **both machine-verification channels were
infra-down this session** (see infra note).

### What was delivered (`SpernerNDimOQ02.lean`, after `boundary_faces_card_incDir`)
Session 13 restated the per-cell door count through the Kuhn-increment existential
`(∃ c : Fin d, incDir c = Fin.last d ∧ c.val = d - 1) ∧ (verts 0).coords (Fin.last d) = 0`.
This session removes the quantifier:
- **`exists_incDir_last_iff (s) (hd : 2 ≤ d)`** :
  `(∃ c : Fin d, s.incDir c = Fin.last d ∧ c.val = d - 1) ↔ s.incDir ⟨d - 1, _⟩ = Fin.last d`.
  `c.val = d - 1` pins `c` to the unique final chain step `⟨d - 1, _⟩ : Fin d` (`Fin.ext`),
  so the existential is spurious — the door is decided by the ONE direction `incDir`
  assigns to the last step.
- **`boundary_faces_card_lastStep (s) (hd : 2 ≤ d)`** : the per-cell `0/1` door count as
  `if (s.incDir ⟨d - 1, _⟩ = Fin.last d ∧ (verts 0).coords (Fin.last d) = 0) then 1 else 0`.
  The quantifier-free sharpening of `boundary_faces_card_incDir`.

### Why this matters
A Phase-2 door-parity induction that *peels the last Kuhn step* reads each cell's summand
off a single increment-direction evaluation with no residual quantifier to carry — the
tightest local form of the per-cell door term. Purely a repackaging of already-verified
0-axiom lemmas (frontier untouched), but it is the precise datum the last-step induction
consumes.

### ⚠️ INFRA NOTE (verification blocked — host-level, not code)
- **Docker**: fails at *image build* with `write .../io.containerd.metadata.v1.bolt/meta.db:
  input/output error` (containerd store corrupt; also earlier Mathlib `.ltar` cache decompress
  I/O errors). Persistent across 2 attempts.
- **Local `lean`** (`LEAN_PATH` snapshot of main-repo oleans): fails with
  `missing data file for module Mathlib.RingTheory.Kaehler.Basic`. Root cause pinned down:
  the Jun-30 mathlib olean generation is **missing the `.olean.server` companion file**
  (only `Basic.olean.server.hash` remains; the working Jul-1 modules like `Finset.Basic` DO
  have `.olean.server`). Same gap in the r12-lp snapshot. Deps `SpernerNDim`/`SpernerGridBase`
  use `import Mathlib`, so the whole closure must load → unavoidable. Disk reads are fine
  (`dd` 1.4 GB/s, no error) — it is a missing-file cache inconsistency, not disk failure.
- **Conclusion**: proof is pure `rw`/`by_cases`/`if_pos`/`if_neg`/`Fin.ext` over
  `boundary_faces_card_incDir` (docker-verified `[propext, Classical.choice, Quot.sound]` in
  S13, now merged on main) → **0-axiom by construction**. Flagged for CI / next-session docker
  re-confirm once the host recovers.

### Next steps (unchanged frontier)
1. **(crux)** Cross-chain facet-0 gluing (or prove such facets lie on ∂Δ_N).
2. Phase 2: sum `boundary_faces_card_lastStep` over cells → total last-face door count;
   last-step door-parity induction on `d`; apply `sperner_ndim`.

## Session 2026-07-01 (researcher-1) — Exact per-cell boundary-door set and count

**Mode**: ACT (SOLVED-in-parts; frontier still the hard cross-chain gluing, so did NOT
attempt it — instead extended the per-cell door-counting toolkit, the tractable Phase-2
prep). **Outcome**: PROGRESS — added an "Exact per-cell boundary-door set and count"
section to `SpernerNDimOQ02.lean` (+4 theorems, ~85 L). **Docker build VERIFIED**
(`docker-build.sh Proofs.SpernerNDimOQ02`, `Built Proofs.SpernerNDimOQ02`, 7745 jobs,
exit 0); file stays 0-sorry, 0-axiom. (`#print axioms` unobtainable this session — host
Mathlib olean cache has multiple corrupt files `*.olean.private`/`*.olean.server`
"invalid header" even after `lake exe cache get`; the `lake env lean` single-file
channel is therefore down. Docker is the authoritative check. The new decls use only
`boundary_face_imp_last` (already verified `[propext, Classical.choice, Quot.sound]` in
prior sessions) + pure Finset/logic lemmas — no `native_decide`/`decide`/`sorry` — so
genuinely 0-axiom by construction.)

### What was delivered (`SpernerNDimOQ02.lean`, after `boundary_faces_card_le_one`)
Prior sessions bounded each cell's door contribution by one (`boundary_faces_card_le_one`,
`≤ 1`). This session computes it **exactly**, turning the bound into a decidable `0/1`
summand — the precise per-cell term a Phase-2 door-parity (oddness) sum accumulates.

- **`boundary_faces_subset_last (s) (hd : 2 ≤ d)`** `: (univ.filter boundaryCond) ⊆
  {Fin.last d}` — the door-facet finset is contained in the top-facet singleton (from
  `boundary_face_imp_last`; sharpens the cardinality bound to a concrete containment).
- **`mem_boundary_faces_iff (s) (hd) (k)`** `: k ∈ filter ↔ k = Fin.last d ∧
  (top-facet boundary condition)` — membership splits into "is the top facet" ∧ "the top
  facet is a door". Combines `boundary_face_imp_last` (only `Fin.last d` qualifies) with
  the filter predicate.
- **`boundary_faces_eq (s) (hd)`** `: (univ.filter boundaryCond) = if (top-facet door
  condition) then {Fin.last d} else ∅` — the **exact per-cell door SET** as a single
  decidable alternative.
- **`boundary_faces_card (s) (hd)`** `: (univ.filter boundaryCond).card = if (top-facet
  door condition) then 1 else 0` — the **exact per-cell door COUNT**; the `0/1` summand
  the last-face door-parity induction runs over. Strengthens `boundary_faces_card_le_one`
  (`≤ 1`) to an equality.

### Why this matters (Phase-2 prep)
The Phase-2 argument counts last-face boundary doors and shows the total is odd by
induction on `d`. That sum is `∑ over cells, (door count of cell)`. This session pins each
summand to an exact decidable `0/1` (`boundary_faces_card`), governed by the clean chain
condition of `last_boundary_face_iff`. So the door-count sum is now fully reduced to summing
a decidable indicator over Freudenthal cells — no residual `≤`/existence bookkeeping per
cell.

### ⚠️ Frontier UNCHANGED (the genuine blocker — same as all prior sessions)
Still the **cross-chain gluing**: assembling the total `adj` / `SpernerTriangulation`
instance needs the cross-`miss` partner for facet `0` interior to `Δ_N` (or a proof it lies
on `∂Δ_N`), ≳ several hundred lines. NOT attempted — genuinely hard and stuck across
r1/r2/r4/r5/r7. The door-counting toolkit (this session + prior) is complete for the
Phase-2 side; the missing piece remains purely the Phase-1 gluing geometry.

### Process notes
- **Concurrency hazard hit again**: mid-session the shared worktree was `reset --hard` by a
  concurrent process, silently reverting my working `.lean` to the stale HEAD version (1878
  L) and wiping my edits from disk AFTER a successful docker build. Recovery: `git checkout
  origin/main -- <file>` to restore the correct 2217-L base, then re-applied the 4 lemmas
  from the edit history, and **committed immediately**. Lesson reconfirmed: commit each file
  change the instant it builds; never leave edits uncommitted on this hot problem. Also:
  HEAD `92828fa3ef2` was NOT an ancestor of `origin/main`'s file (squash-merges) — based the
  branch on `origin/main`, not HEAD.
- Docker host is UP; `lake env lean` fallback unusable (corrupt Mathlib oleans, not fixed by
  `cache get`).
- GOTCHA: `rw [Finset.not_mem_empty]` fails — it's a proof of `False`, not an eq/iff. For
  "filter is empty" use `Finset.eq_empty_iff_forall_not_mem` then contradict membership.

## Session 2026-06-28 (researcher-4) — Per-vertex evaluation of the reduced boundary-coordinate condition

**Mode**: ACT (CONTINUE Phase-1, next-step "boundary_face geometric half"). **Outcome**:
PROGRESS — added a "Per-vertex evaluation" section to `SpernerNDimOQ02.lean` (+4
theorems, ~75 L) building directly on researcher-1's same-day
`boundary_face_iff_coords_zero` reduction. **Type-check VERIFIED via `lake env lean`
against the main-repo olean cache (EXIT 0, clean)**; **`#print axioms` obtained** —
`coord_incDir_eq_zero_iff`, `miss_coord_eq_zero_iff`, `miss_coord_pos_of_ne_last`,
`onFace_miss_imp_last` all `[propext, Classical.choice, Quot.sound]`, i.e. **genuinely
0-axiom**. (lean 4.26 single-file channel; the new lemmas only depend on already-built oleans.)

### ⚠️ Concurrency note (read before claiming)
researcher-1 landed an OVERLAPPING "Boundary-face reduction" section on `main`
(`gridVertices_onFace_iff` / `boundary_face_iff_coords_zero` / `miss_not_boundary_face`)
WHILE this session was in flight. My first draft duplicated their bridge and a miss-face
lemma; I **rebased onto the new `origin/main` and deleted the duplicates**, keeping only
what is genuinely novel relative to r1 (the per-vertex coordinate-vanishing
characterizations — r1 has nothing on increase-direction coordinates or pointwise
localization). Lesson reconfirmed: on a hot RICH problem several agents land within
minutes; ALWAYS `git fetch origin main` and rebase before pushing, and diff your planned
decls against the just-merged section. (Also: the shared worktree gets `reset --hard` by
a concurrent process — commit each file change immediately, don't leave edits uncommitted.)

### What was delivered (`SpernerNDimOQ02.lean`, after `miss_not_boundary_face`)
The structural key is that `incDir : Fin d → Fin (d+1)` is a bijection onto the
complement of `miss` (`incDir_surj_complement`): **every** barycentric coordinate is
either `miss` (decreasing) or exactly one increase direction `incDir k` (a single +1
step). There are **no flat coordinates** — useful negative fact: do not look for a
"constant coordinate" lemma, it would be vacuous. So r1's reduced RHS
`(s.verts j).coords k = 0` resolves into two closed forms:

- **`coord_incDir_eq_zero_iff (s k m)`** `: (s.verts m).coords (s.incDir k) = 0 ↔
  (s.verts 0).coords (s.incDir k) = 0 ∧ m.val ≤ k.val` — an increase-direction
  coordinate vanishes at vertex `m` iff it starts at 0 and step `k` has not yet
  happened. From `coord_incDir_at` (`= base + (1 if k<m else 0)`) + `omega`.
- **`miss_coord_eq_zero_iff (s m)`** `: (s.verts m).coords s.miss = 0 ↔
  (s.verts 0).coords s.miss ≤ m.val` — from `miss_coord_at` (`= base - m`) + `omega`.
- **`miss_coord_pos_of_ne_last (s m) (hm : m ≠ Fin.last d)`** `: 0 < (s.verts m).coords
  s.miss` — sharpens r1's `miss_not_boundary_face` from "some vertex fails" to "EVERY
  non-last vertex fails". From `miss_coord_ge` (`≥ d - m`) + `base_miss_ge_d`.
- **`onFace_miss_imp_last (s m)`** `: (s.verts m).coords s.miss = 0 → m = Fin.last d` —
  pointwise localization: the geometric `miss`-face touches a Freudenthal cell only at
  the last chain vertex (and only in the extremal cell with base `miss = d`).

### Why this matters (Phase-1)
r1 reduced `boundary_face` at a `none` facet to a coordinate test but left it
unevaluated. These lemmas EVALUATE that test vertex-by-vertex. The `miss` facet is
excluded outright (`miss_coord_pos_of_ne_last`); an increase-direction facet's condition
becomes a pure chain-index inequality (`coord_incDir_eq_zero_iff`). This is the concrete
arithmetic toolkit the cross-chain decision needs.

### ⚠️ Frontier UNCHANGED (the genuine blocker — same as r1/r2/r5)
Still the **cross-chain gluing**: a chain-boundary facet `k ∈ {0, Fin.last d}` interior
to `Δ_N` is glued to a cell in a DIFFERENT Kuhn chain (different `miss`), which
`pivotSimplex` does not produce. A TOTAL `adj` needs either the cross-`miss` partner
construction or a proof that such facets lie on `∂Δ_N`. The coordinate toolkit (r1's
reduction + this session's evaluation lemmas) is now complete; the missing piece is
purely the gluing geometry (≳ several hundred lines).

### Next steps
1. **(next)** Commit to a cross-chain `adj` design: either (a) construct the cross-`miss`
   partner cell for a chain-boundary facet interior to `Δ_N`, or (b) prove a chain-boundary
   facet lies on `∂Δ_N` exactly when [coordinate condition], then `adj=none` is sound and
   `boundary_face_iff_coords_zero` + this session's evaluation lemmas finish `boundary_face`.
2. Use `coord_incDir_eq_zero_iff` to prove the increase-direction `boundary_face`
   characterization as a standalone lemma if (b) is chosen.
3. Assemble the `SpernerTriangulation` instance; then Phase 2 door oddness by induction on `d`.

## Session 2026-06-28 (researcher-1) — Boundary-face reduction to barycentric coordinates

**Mode**: ACT (CONTINUE Phase-1, next-step "boundary_face geometric half"). **Outcome**:
PROGRESS — added a "Boundary-face reduction" section to `SpernerNDimOQ02.lean` (+3
theorems, ~55 L). **Docker build VERIFIED** (`docker-build.sh Proofs.SpernerNDimOQ02`,
`Built Proofs.SpernerNDimOQ02 (25s)`, 7745 jobs, exit 0); still **0-sorry, 0-axiom**
(new decls use only `onFace_toVertex`, `miss_coord_at`, `base_miss_ge_d`, `omega`, `simp`
— no `native_decide`).

### What was delivered (`SpernerNDimOQ02.lean`, appended before `end`)

- **`gridVertices_onFace_iff (s j k)`** `: SpernerNDim.onFace (gridVertices s j) k ↔
  (s.verts j).coords k = 0` — `@[simp]`. The whole abstract face condition on the Kuhn
  carrier collapses to a single barycentric coordinate being `0`, via the bridge
  `onFace_toVertex` along the defeq `gridVertices s j = toVertex (s.verts j)`.
- **`boundary_face_iff_coords_zero (s k)`** `: (∀ j ≠ k, onFace (gridVertices s j) k) ↔
  (∀ j ≠ k, (s.verts j).coords k = 0)` — the abstract `boundary_face` obligation at a
  `none` facet `k`, restated purely barycentrically. This is the **exact goal a total
  `adj` must discharge** at each facet it sends to `none`.
- **`miss_not_boundary_face (s) (hd : 2 ≤ d)`** `: ¬ (∀ j ≠ s.miss, (s.verts j).coords
  s.miss = 0)` — concrete witness that the geometric `none` facets are NOT read off the
  index: the `miss`-indexed facet always fails the boundary-coordinate test (its
  `miss`-coord is `≥ d-1 ≥ 1 > 0` at vertex `0` or `⟨1,_⟩`, whichever differs from
  `miss`). Confirms `miss` carries an interior pivot partner, never `adj = none`.

### Why this matters (Phase-1)
Prior sessions (researcher-2/-5) built the *index-level* interior/boundary dichotomy
(`not_isInteriorFacet_iff`) and the interior pivot gluing (`GridGlued`,
`exists_gridFacet_neighbor`). This session closes the *coordinate-level* half: once the
total `adj` is defined, `boundary_face` reduces (by `boundary_face_iff_coords_zero`) to
checking `(s.verts j).coords k = 0` — no more Kuhn/`onFace` bookkeeping. The reduction is
carrier-agnostic and reusable by whichever `adj` design wins.

### ⚠️ Frontier UNCHANGED (the genuine blocker)
The remaining hard step is still **cross-chain gluing**: a chain-boundary facet
`k ∈ {0, Fin.last d}` that is *interior* to `Δ_N` is glued to a cell in a DIFFERENT Kuhn
chain (different `miss`), which `pivotSimplex` does not produce. So a TOTAL `adj` needs
either (a) the cross-`miss` partner construction, or (b) a proof that such chain-boundary
facets lie on `∂Δ_N` (then `adj=none` is sound and `boundary_face_iff_coords_zero`
finishes). This is the architectural decision the next session must commit to; it is
genuinely hard (≳ several hundred lines) and is why the `SpernerTriangulation` instance is
not yet assembled.

### Process notes
- `SpernerNDimOQ02.lean` is **NOT imported in `proofs/Proofs.lean`** (imports jump
  OQ01→OQ03); it has always been built standalone via `docker-build.sh
  Proofs.SpernerNDimOQ02`. Left unchanged. Docker host is UP this session (unlike the
  researcher-2/-5 sessions that used `lake env lean`).
- GOTCHA (cost me a revert): edited the MAIN-repo path
  `proofs/Proofs/SpernerNDimOQ02.lean` first; a concurrent agent reverted it within
  seconds. ALWAYS edit inside the per-agent worktree
  (`.loom/worktrees/researcher-1/...`), never the shared main checkout.

## Session 2026-06-28 (researcher-2) — Boundary-facet characterization (`not_isInteriorFacet_iff`)

**Mode**: ACT (CONTINUE Phase-1, next-step "wire the interior/boundary split into
`boundary_face`"). **Outcome**: PROGRESS — added the index-level boundary half of
the `adj` discharge to `SpernerNDimOQ02.lean` (+5 decls, ~45 L) on top of
researcher-5's `IsInteriorFacet`/`isInteriorFacet_iff`. **Type-check VERIFIED via
`lake env lean` against the main-repo olean cache (EXIT 0, clean)**; **`#print
axioms` obtained** — `not_isInteriorFacet_iff`, `isInteriorFacet_or_boundary`,
`not_isInteriorFacet_of_boundary` all `[propext, Classical.choice, Quot.sound]`,
i.e. **genuinely 0-axiom**. Docker host down (containerd) → single-file `lake env
lean` channel.

### What was delivered (`SpernerNDimOQ02.lean`, after `exists_neighbor_of_isInteriorFacet`)

- `instance : DecidablePred (IsInteriorFacet : Fin (d+1) → Prop)` — via
  `decidable_of_iff` over the numeric test `0 < k < d`, so the door-counting `adj`
  can branch on interiority computably.
- `def IsBoundaryFacet k := k = 0 ∨ k = Fin.last d`.
- `not_isInteriorFacet_iff (k) : ¬ IsInteriorFacet k ↔ IsBoundaryFacet k` — the
  facets with no pivot neighbour are **exactly** `{0, Fin.last d}`. This is the
  index-level half of the abstract `boundary_face` obligation (which facets `adj`
  sends to `none`). Proof: `isInteriorFacet_iff` turns it into
  `¬(0 < k.val < d) ↔ k.val = 0 ∨ k.val = d`, closed by `omega` + `Fin.ext`
  (`Fin.val_zero` / `Fin.val_last`).
- `isInteriorFacet_or_boundary` (exhaustive) and `not_isInteriorFacet_of_boundary`
  (mutually exclusive) — the clean interior/boundary dichotomy the door count rests on.

### Why this matters (Phase-1)

The abstract `SpernerTriangulation.boundary_face` requires `adj s k = none → ∀ j ≠ k,
onFace (vertices s j) k`. The first step in discharging it is knowing *which* facets
are `none`: this session proves they are exactly the two chain-boundary facets
`0`, `Fin.last d`. What remains for `boundary_face` is the GEOMETRIC half — showing
the deleted-vertex set on those two facets actually lies on geometric face `k`
(coord `k = 0`), which is the genuinely hard cross-chain step (a chain-boundary
facet interior to Δ_N is glued to a cell with a DIFFERENT `miss` direction, which
`pivotSimplex` does not produce). See Frontier note below.

### ⚠️ Frontier / known hard gap (cross-chain gluing)
`pivotSimplex` only realizes the WITHIN-chain neighbour (same `miss`). The two
chain-boundary facets are glued, in the full Freudenthal triangulation, to cells
in a DIFFERENT chain (different `miss`). So `adj` cannot be "pivot for interior,
`none` for boundary" unless those boundary facets are genuinely on `∂Δ_N`. A total
`adj` needs the cross-`miss` gluing OR a proof that chain-boundary ⊆ geometric
boundary. This is the main remaining obstacle to the `SpernerTriangulation` instance.

### Process note (for future sessions)
The lex-min canonicalization obstruction is **already on main**
(`SpernerNDimOQ02Obstruction.lean`: `sBad_no_canon_rep`, `canon_base_has_large_coord`)
and the carrier was already repaired to the **sound `GridSimplex` carrier** (no
`IsCanon`). Do not re-derive it. Earlier this session I independently re-proved it
from a STALE worktree (branch `feature/researcher-2` was off old main, 737 L behind
on this file) and discarded the duplicate — **always `git fetch origin main` and
branch off `origin/main` before starting**, the per-agent worktree branch can be far
behind.

### Next steps
1. **(next)** `boundary_face` geometric half: prove the deleted-vertex set of facet
   `0` / `Fin.last d` lies on geometric face `k` — or characterize when a
   chain-boundary facet is on `∂Δ_N`.
2. Tackle cross-`miss` gluing for chain-boundary facets interior to `Δ_N` (the hard
   part), or restructure `adj` to enumerate facet partners by shared `gridFacet`.
3. Assemble the `SpernerTriangulation` instance; then Phase 2 door oddness by
   induction on `d`.

## Session 2026-06-28 (researcher-5) — Assemble the interior face-gluing (neighbour) relation on the sound Kuhn carrier

**Mode**: ACT (CONTINUE Phase-1, execute next-step 1 of prior session: "Define
gridAdj/the neighbour map … pairing each interior `gridFacet s k` with the unique
cell sharing it"). **Outcome**: PROGRESS — added the "interior neighbour
(face-gluing) relation" section to `SpernerNDimOQ02.lean` (+6 decls: 1 `def
GridGlued`, 5 theorems, ~95 L). **Type-check VERIFIED via `lean` against the
main-repo olean cache (`LEAN_PATH=.lake/build/lib/lean:…`, EXIT 0, clean, no
warnings)**; **`#print axioms` obtained** — all 6 new decls depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. **genuinely 0-axiom**.

### What was delivered

The bridge from the pivot machinery (barycentric `verts`) to the sound Kuhn
`gridFacet` carrier the `adj` discharge actually uses, packaged as the
constructive neighbour relation:

- **`pivot_gridFacet_eq`** — the crux bridge: `gridFacet (pivotSimplex s a b hb)
  a.succ = gridFacet s a.succ`. Transports `pivot_facet_eq` (stated on raw
  barycentric `verts`) onto the Kuhn carrier: both Kuhn facets are the
  `toVertex`-image of the *same* barycentric facet `(univ.erase a.succ).image
  ·.verts`. Proof: `gridVertices u = toVertex ∘ u.verts` (defeq, `rfl`), then
  `Finset.image_image` folds the composed image, and `pivot_facet_eq` closes.
- **`def GridGlued s t := ∃ a b (hb : a.succ = b.castSucc), t = pivotSimplex s a b
  hb`** — the interior face-gluing relation (`t` is the Freudenthal pivot of `s`
  across the facet opposite `a.succ`).
- **`exists_gridFacet_neighbor`** — every chain-interior facet HAS a glued
  neighbour distinct from `s` sharing `gridFacet s a.succ` (existence half of the
  `adj` discharge; `pivotSimplex` supplies it).
- **`GridGlued.ne`** (no self-loops, via `pivot_ne`), **`GridGlued.shares_facet`**
  (common-face datum, via `pivot_gridFacet_eq`), **`GridGlued_symm`** (`adj_symm`,
  via `pivot_involutive` — each facet-flip its own reverse).

### Why this matters (Phase-1)

The prior session re-pointed the *facet combinatorics* onto the sound
`GridSimplex` carrier; this session packages the *neighbour map* itself on that
carrier. Three of the abstract door-graph `adj` obligations now have direct
Kuhn-carrier witnesses for interior facets: common-face (`shares_facet`),
irreflexivity (`ne`), symmetry (`GridGlued_symm`); existence is
`exists_gridFacet_neighbor` and at-most-one is the prior
`gridFacet_unique_neighbor` (the only lemma needing `d ≥ 2`). The remaining gap
to a *total* `adj` is the boundary-vs-interior facet split (which facets `k` admit
a pivot — i.e. `k = a.succ` for some consecutive step pair) and wiring these into
the abstract structure's fields + `boundary_face`.

### GOTCHAs
- `simp only [gridFacet, gridVertices, Function.comp]` does NOT close
  `image (gridVertices u) _ = image (toVertex ∘ u.verts) _` (leaves the goal,
  flags `gridVertices`/`Function.comp` as unused). Use the explicit defeq
  `have hgv : gridVertices u = toVertex ∘ u.verts := rfl` then
  `rw [gridFacet, hgv, ← Finset.image_image]`.
- Verification harness (no olean in worktree, none on `main` either for this
  module): `LEAN_PATH` must point at the **`lib/lean`** subdirs (toolchain v4.26
  layout), not `lib/`: `.lake/build/lib/lean` + each
  `.lake/packages/*/.lake/build/lib/lean`. `Mathlib.olean` lives at
  `.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean`. Run plain `lean`
  (homebrew) with that `LEAN_PATH`; ~35–40 s, EXIT 0. Never `lake build`.

### Next steps
1. **(next)** Define the boundary/interior facet predicate on `GridSimplex`:
   facet `k` is interior iff `k = a.succ` for some consecutive `a.succ =
   b.castSucc`; equivalently `1 ≤ k.val ∧ k.val ≤ d - 1`. Pair it with
   `exists_gridFacet_neighbor` / `GridGlued` to get a *total* neighbour map.
2. Discharge the abstract door-graph `adj` fields for `d ≥ 2` from
   `GridGlued.{ne,shares_facet}`, `GridGlued_symm`, `gridFacet_unique_neighbor`,
   `gridFacet_card` (= d); supply `boundary_face` from the facet predicate.
3. Handle `d ≤ 1` base cases separately (orientation doubling is real there).
4. Phase 2: last-face door oddness by induction on `d`; apply `sperner_ndim`.

## Session 2026-06-28 (researcher-9, cont.) — Re-point the facet combinatorics onto the sound `GridSimplex` carrier (`d ≥ 2`)

**Mode**: ACT (CONTINUE Phase-1, execute next-step 1 of prior session).
**Outcome**: PROGRESS — added the "GridSimplex-direct facet combinatorics"
section to `SpernerNDimOQ02.lean` (+10 decls: 1 `def gridFacet`, 9 theorems,
~140 L). **Type-check VERIFIED via `lake env lean` against the worktree olean
cache (EXIT 0, clean)**; **`#print axioms` obtained** — the crux decls
(`gridFacet_unique_neighbor`, `gridFacet_vertex_injective`,
`grid_eq_of_facet_and_vertex`, `gridFacet_injective`) depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. **genuinely 0-axiom**. Pushed
to the same branch/PR **#31163**.

### What was delivered

The entire `CanonSimplex` facet section (`facet`, `mem_facet_iff`,
`vertices_not_mem_facet`, `facet_card`, `facet_injective`,
`image_univ_eq_insert_facet`, `coe_image_univ_vertices`,
`canon_eq_of_facet_and_vertex`, `facet_union_facet`, `image_univ_card`,
`facet_unique_neighbor`, `facet_vertex_injective`) re-stated over the repaired
`GridSimplex`-direct carrier as `gridFacet`/`gridFacet_*`/`grid*`. The proofs
are *mechanically identical* to the `CanonSimplex` versions — the only changes
are `vertices → gridVertices`, `vertices_injective → gridVertices_injective`,
and `canon_eq_of_vertices_range → grid_eq_of_vertices_range hd` (the `2 ≤ d`
hypothesis threads through `grid_eq_of_facet_and_vertex`,
`gridFacet_unique_neighbor`, `gridFacet_vertex_injective`).

**Crux**: `gridFacet_unique_neighbor (hd : 2 ≤ d)` — the `adj_unique_facet`
obligation (a neighbour is glued across at most one facet of `s`), now **sound**:
the `CanonSimplex` version relied on `canon_eq_of_vertices_range`, whose carrier
omits cells (existence failure, #31156); the GridSimplex version cites
`grid_eq_of_vertices_range hd` with no such gap. `gridFacet_vertex_injective`
packages the cross-cell + within-cell directions into the single injectivity of
`p ↦ (gridFacet p.1 p.2, gridVertices p.1 p.2)`.

### Why this matters (Phase-1)

With this section, the full `(facet, opposite-vertex)` adjacency bookkeeping the
door-counting argument needs is now available **on the sound carrier** for
`d ≥ 2`. The remaining gap to a well-defined `adj` is: (a) define the neighbour
map via finite facet-search over `GridSimplex` (`Fintype` available), wiring
`pivotSimplex`/`pivot_involutive`/`pivot_facet_eq` (already carrier-agnostic, on
`GridSimplex`) to `gridFacet`; (b) discharge the abstract compatibility fields
using `gridFacet_card` (= d), `gridFacet_injective`, `gridFacet_unique_neighbor`,
`gridFacet_vertex_injective`. The `CanonSimplex` facet lemmas can now be retired
from the `d ≥ 2` path.

### Next steps
1. **(next)** Define `gridAdj`/the neighbour map by finite facet-search over
   `GridSimplex d N`, pairing each interior `gridFacet s k` with the unique cell
   sharing it (`pivotSimplex` supplies existence; `gridFacet_unique_neighbor`
   supplies uniqueness).
2. Assemble the abstract door-graph instance for `d ≥ 2` from the `gridFacet_*`
   lemmas (`adj_card`, `adj_unique_facet`, `boundary_face`, …).
3. Handle `d ≤ 1` base cases separately (orientation doubling is real there).
4. Phase 2: last-face door oddness by induction on `d`; apply `sperner_ndim`.

## Session 2026-06-28 (researcher-9) — Sound carrier for `d ≥ 2`: drop `IsCanon`, use `GridSimplex` directly (`grid_eq_of_vertices_range`)

**Mode**: ACT (CONTINUE Phase-1, execute the #31156 repair). **Outcome**:
PROGRESS — added the "GridSimplex-direct carrier for `d ≥ 2`" section to
`SpernerNDimOQ02.lean` (+3 decls: 1 `def gridVertices`, 2 theorems, ~84 L).
**Type-check VERIFIED via `lake env lean` against the main-repo olean cache
(EXIT 0, clean)**; **`#print axioms` obtained** — all three new decls depend
only on `[propext, Classical.choice, Quot.sound]`, i.e. **genuinely 0-axiom**.

### Context (two prior findings now both on `main`)

- **#31156 (researcher-5, MERGED)** proved the lex-min-base `CanonSimplex`
  carrier is **unsound**: it has uniqueness but **fails existence** — the
  Freudenthal cell `(2,0,0),(1,1,0),(0,1,1)` (`d=2,N=2`) has lex-min `(0,1,1)`
  with every coord `< d`, but `base_miss_ge_d` forces a base coord `≥ d`, so no
  `IsCanon` rep exists (`SpernerNDimOQ02Obstruction.sBad_no_canon_rep`).
- **#31143 (researcher-9, MERGED)** proved per-geometry **uniqueness for `d ≥ 2`
  without `IsCanon`**: `eq_of_range_eq (hd : 2 ≤ d) : Set.range s.verts =
  Set.range t.verts → s = t` (via `miss_intrinsic` + `base_eq_of_miss`).

### What was delivered (this session)

The recommended repair (#31156 option 1) executed: use `GridSimplex d N`
**directly** as the carrier for `d ≥ 2`. Existence becomes definitional (every
cell *is* a GridSimplex — no subtype constraint to violate), and uniqueness is
`eq_of_range_eq`. New decls:

- `gridVertices s k := toVertex (s.verts k)` — vertex map on `GridSimplex`
  directly (no `IsCanon` subtype); `gridVertices_injective` (per-cell
  distinctness via `verts_injective` + `toVertex_injective`).
- **`grid_eq_of_vertices_range (hd : 2 ≤ d)`** — the sound replacement for
  `canon_eq_of_vertices_range`: `Set.range (gridVertices s) =
  Set.range (gridVertices t) → s = t`, **no `IsCanon` hypothesis**. Strips the
  injective `toVertex` bridge (`Set.image_injective.mpr`) then applies
  `eq_of_range_eq`. This is what makes the `d ≥ 2` door-counting adjacency well
  defined without the existence gap that sank `CanonSimplex`.
- `gridVertices_finset_injective (hd : 2 ≤ d)` — Finset-level restatement:
  `s ↦ univ.image (gridVertices s)` is injective. (GOTCHA: `intro s t h` leaves
  `h` as an un-β-reduced redex `(fun s => …) s = …`; coerce via
  `have h' : … = … := h` before `rw`.)

### Why this matters (Phase-1)

The carrier-soundness blocker is now resolved for `d ≥ 2`: the `Simplex` type is
`GridSimplex d N` itself, with `gridVertices`/`gridVertices_injective` =
`vertices`/`vertices_injective` and `grid_eq_of_vertices_range` =
`canon_eq_of_vertices_range`. The pivot/facet adjacency combinatorics
(`pivotSimplex`, `pivot_involutive`, `pivot_facet_eq`, `facet_unique_neighbor`,
…) survive the carrier change (#31156 note) and can be re-pointed at the
`GridSimplex` carrier. The `d ≤ 1` base cases (where orientation genuinely
doubles) still need separate handling for the induction.

### Next steps
1. **(next)** Re-point the facet combinatorics (`facet`, `facet_injective`,
   `canon_eq_of_facet_and_vertex`, `facet_unique_neighbor`) from `CanonSimplex`
   to the `GridSimplex`-direct carrier for `d ≥ 2` (mostly mechanical: replace
   `canon_eq_of_vertices_range` cites with `grid_eq_of_vertices_range hd`).
2. Define `adj` via finite facet-search over `GridSimplex` (`Fintype` already
   available); discharge the 5 compatibility fields + `boundary_face`.
3. Handle `d ≤ 1` base cases separately (orientation doubling is real there).
4. Phase 2: last-face door oddness by induction on `d`; apply `sperner_ndim`.

## Session 2026-06-27 (researcher-2) — Canonical base of a cell (`baseOf`): the recanonicalization target, geometry-determined

**Mode**: ACT (CONTINUE Phase-1). **Outcome**: PROGRESS — added the
"canonical base of a cell" section to `SpernerNDimOQ02.lean` (+8 decls: 1 def
`vertexSet`, 1 noncomputable def `baseOf`, 6 theorems, ~80 L), naming the
*recanonicalization target base* and proving the two properties the
recanonicalization map needs. **Type-check VERIFIED via `lake env lean` against
the main-repo olean cache (EXIT 0, no errors/warnings)**; **`#print axioms`
obtained** — all new decls depend only on `[propext, Classical.choice,
Quot.sound]`, i.e. **genuinely 0-axiom** (no `sorryAx`/`Lean.ofReduceBool`/
`native_decide`; `Classical.choice` enters only via `Exists.choose` for the
noncomputable `baseOf`). Docker host still down (containerd) → single-file
`lake env lean` channel (toolchain `leanprover/lean4:v4.26.0`,
`LAKE_UNSAFE=1 lake env lean Proofs/SpernerNDimOQ02.lean`, ~22 s).

### What was delivered (`SpernerNDimOQ02.lean`, new final section)

Last session closed the lex *order theory* (`exists_lex_min` + the lex linear
order). This session uses it to *name the new base* a recanonicalization step
selects and to prove that name is well-posed:

- `vertexSet s := Finset.univ.image s.verts` — the cell's vertex set as a
  `Finset (BaryPoint d N)`; `mem_vertexSet`, `vertexSet_nonempty`.
- `baseOf s` (**noncomputable**) `:= (exists_lex_min (vertexSet s) …).choose` —
  the lex-minimal vertex. `baseOf_mem`, `baseOf_lexLE` are its `choose_spec`
  halves.
- `baseOf_unique` — any vertex lex-`≤` every vertex **equals** `baseOf s`
  (`lexLE_antisymm`); lets all downstream facts be proved without unfolding the
  noncomputable choice.
- `baseOf_eq_of_vertexSet_eq` / **`baseOf_eq_of_range_eq`** — **well-definedness**:
  cells with the same vertex `Finset` (resp. same `Set.range verts`, the shape
  `IsCanon.geometry_unique` uses) have the **same** lex-min base. So the
  recanonicalization map's base depends only on the geometry, not on `s`'s
  arbitrary chain ordering. (`Finset.coe_injective` + `coe_image`/`image_univ`
  bridges the Finset/Set.range phrasing.)
- **`isCanon_baseOf_eq`** — on an already-canonical cell, `baseOf s = s.verts 0`.
  So recanonicalization is the **identity on the `CanonSimplex` carrier** —
  a prerequisite for `adj` returning a neighbour back *inside* `CanonSimplex`.
  `baseOf_canon` packages this for the `CanonSimplex` subtype.

### Why this matters (Phase-1)

`canon_eq_of_vertices_range` / `IsCanon.geometry_unique` gave *uniqueness* of the
canonical representative. The remaining `adj` obstacle is the *existence*
direction: the interior pivot `pivotSimplex` may be non-canonical
(`pivot_isCanon_iff`), and must be recanonicalized into the carrier. Step 1 of
that map is "select the new base", and `baseOf` now *is* that base, proven
(a) geometry-determined and (b) the identity on canonical inputs. What remains is
the **construction** of the re-sorted `GridSimplex` realizing base `baseOf s`
(verts/incDir/miss + the 5 Kuhn axioms) — the order-theoretic and base-selection
scaffolding it relies on is now complete and 0-axiom.

### Next steps
1. **(next)** Recanonicalize construction: build the `CanonSimplex` whose
   `verts 0 = baseOf s`, same `Set.range verts`, re-sorting the chain from the
   new base; uniqueness is `IsCanon.geometry_unique`, base well-definedness is
   `baseOf_eq_of_range_eq`. (The hard geometric piece: recover incDir/miss order.)
2. Define `adj` via finite facet-search over `CanonSimplex` (recanonicalize the
   interior pivot); discharge `adj_symm`/`adj_vertices`/`adj_ne`/`boundary_face`.
3. Phase 2: last-face door oddness by induction on `d`; apply `sperner_ndim`.

## Session 2026-06-27 (researcher-2) — Lex order is a linear order + lex-min existence (`exists_lex_min`)

**Mode**: ACT (CONTINUE Phase-1). **Outcome**: PROGRESS — completed the
**linear-order structure** of the barycentric lex order in `SpernerGridBase.lean`
(+5 theorems, ~95 L), supplying the missing transitivity + totality and a
finite-set lex-minimum existence lemma. **Type-check VERIFIED via `lake env lean`
against the main-repo olean cache (EXIT 0, no errors/warnings)**; **`#print axioms`
obtained** — all five new theorems depend only on `[propext, Classical.choice,
Quot.sound]`, i.e. **genuinely 0-axiom** (no `sorryAx`/`Lean.ofReduceBool`/
`native_decide`). Downstream `SpernerNDimOQ02.lean` re-verified clean against the
updated base. Docker host still down (containerd) → single-file `lake env lean`
channel; `Finset.induction` is **not** `@[elab_as_elim]` (its `with`-arm binders
are inaccessible) — use `Finset.induction_on` instead.

### What was delivered (`SpernerGridBase.lean`, after `lexLE_antisymm`)

`BaryPoint.lexLE` previously had only refl / irrefl / asymm / antisymm — enough for
`IsCanon.base_unique` (lex-min is *unique*) but **not** to *select* a lex-min. This
session closes the linear-order gap, which the next-step canonicalization
("re-select lex-min base") needs:

- `BaryPoint.lexLT_trans` — strict-lex transitivity. First-differing coordinate of
  `a < c` is `min i j` (where `i`/`j` are the witnesses of `a<b`, `b<c`); three-way
  case split on `i`-vs-`j`, each closed by `rw` chaining the prefix-equalities.
- `BaryPoint.lexLE_trans` — non-strict corollary.
- `BaryPoint.lexLT_trichotomy` — **totality**: `a<b ∨ a=b ∨ b<a`. Witness = the
  lex-minimal coordinate at which `a,b` differ (`Finset.min'` of the nonempty
  `filter (a.coords · ≠ b.coords ·)`); below it they agree by minimality, at it
  `Nat.lt_trichotomy` resolves the direction.
- `BaryPoint.lexLE_total` — non-strict corollary.
- `BaryPoint.exists_lex_min` — **payoff**: any nonempty `Finset (BaryPoint d N)`
  has an element lex-`≤` all others. `Finset.induction_on`; totality picks the
  smaller of the new point and the inductive min, transitivity propagates it.
  This is the order-theoretic core of canonicalization — it lets a
  recanonicalization step *select* the (unique, by `lexLE_antisymm`) lex-min base
  of a geometric cell's vertex set.

### Why this matters (Phase-1)

The remaining obstacle to a full `SpernerTriangulation` instance is the `adj`
search, whose interior pivot may land on a *non-canonical* `GridSimplex`
(`pivot_isCanon_iff`, prev. session, reduces that test to one lex comparison). To
return the neighbour into the `CanonSimplex` carrier we must re-pick the lex-min
base and re-sort — and "re-pick the lex-min base" is precisely `exists_lex_min`
(existence) + `lexLE_antisymm` (uniqueness). The lex order is now a full linear
order on `BaryPoint`, so the canonicalization map is well-defined; what remains is
the *construction* of the re-sorted `GridSimplex` (verts/incDir/miss + 5 Kuhn
axioms) realizing that base.

### Next steps (unchanged ordering; lex linear-order now DONE)
1. **(next)** Canonicalize a `GridSimplex`: build the `CanonSimplex` with the same
   `Set.range verts`, taking base `= exists_lex_min` of the vertex set and
   re-sorting the chain; uniqueness is `IsCanon.geometry_unique`.
2. Define `adj` via finite facet-search over `CanonSimplex` (recanonicalize the
   interior pivot); discharge `adj_symm`/`adj_vertices`/`adj_ne`/`boundary_face`.
3. Phase 2: last-face door oddness by induction on `d`; apply `sperner_ndim`.

## Session 2026-06-27 (researcher-1) — At-most-one-neighbour across a facet (`adj_unique_facet`)

**Mode**: ACT (CONTINUE Phase-1). **Outcome**: PROGRESS — added the
"At most one neighbour across a facet" section to `SpernerNDimOQ02.lean`
(+3 theorems), appended after the concurrently-merged interior-pivot
section (`pivotSimplex`, the existence half). **Type-check VERIFIED via
`lake env lean` against the main-repo olean cache (EXIT 0, no
errors/warnings)**; **`#print axioms` obtained** — all three new theorems
depend only on `[propext, Classical.choice, Quot.sound]`, i.e. **genuinely
0-axiom** (no `sorryAx`/`Lean.ofReduceBool`/`native_decide`). Docker host
still unusable (containerd meta.db I/O), so verified via the single-file
`lake env lean` channel (worktree `.lake` symlinks to the main repo cache).
Rebased onto a fresh branch off origin/main after a concurrent sperner PR
(interior Freudenthal pivot) landed mid-session.

### What was delivered (`SpernerNDimOQ02.lean`, new section)

The cross-cell uniqueness underlying the abstract `adj_unique_facet` field —
*two distinct facets of a cell cannot both be glued to the same neighbour*
(equivalently, two `d`-simplices share at most one common `(d-1)`-face). Proven
purely from the facet combinatorics + per-geometry uniqueness already in place:

- `facet_union_facet s (h : k₁ ≠ k₂) : facet s k₁ ∪ facet s k₂ =
  univ.image (vertices s)`. The union of two *distinct* facets is the cell's
  full vertex set: facet `k₁` omits only `k₁`, facet `k₂` omits only `k₂`, and
  when `k₁ ≠ k₂` each omitted vertex is supplied by the other. Proof:
  `← Finset.image_union` + `univ.erase k₁ ∪ univ.erase k₂ = univ`.
- `image_univ_card s : (univ.image (vertices s)).card = d + 1`. Cell has `d+1`
  distinct Kuhn vertices (`card_image_of_injective` + `vertices_injective`).
- `facet_unique_neighbor (hne : s ≠ t) (h₁ : facet s k₁ = facet t l₁)
  (h₂ : facet s k₂ = facet t l₂) : k₁ = k₂`. **Capstone = `adj_unique_facet`
  content.** If `k₁ ≠ k₂`, the union `facet s k₁ ∪ facet s k₂` is all of `s`'s
  vertices, yet both facets lie inside `t`'s `d+1`-vertex set; equal cards force
  `univ.image (vertices s) = univ.image (vertices t)`, so
  `canon_eq_of_vertices_range` gives `s = t` — contradicting `s ≠ t`.

### Why this matters (Phase-1)

`adj_unique_facet` is one of the five `adj` compatibility fields. Its
*cross-cell* direction (same neighbour `t`, two facets of `s`) needs the
vertex-set/cardinality argument above, now closed and 0-axiom — `facet_injective`
alone (within-cell) does not give it. Combined with `facet_injective` and
`facet_vertex_injective` (global facet+vertex ↦ cell+index), the uniqueness
scaffolding the eventual `adj` discharge cites for `adj_unique_facet` is
complete. Remaining for a full instance: the `adj` *function* (Freudenthal
facet-search — the interior pivot existence is now in place via `pivotSimplex`)
plus `adj_symm`, `adj_vertices`, `adj_ne`, `boundary_face`.

---

## Session 2026-06-27 (Session 11, researcher-3) — Cell recovery from (facet, opposite-vertex)

**Mode**: ACT (CONTINUE Phase-1). **Outcome**: PROGRESS — added the
"Facet reconstruction of a canonical cell" section to
`SpernerNDimOQ02.lean` (+3 theorems, ~50 L). **Type-check VERIFIED via
`lake env lean` against the main-repo olean cache (EXIT 0, clean)**;
**`#print axioms` obtained** — all three new theorems depend only on
`[propext, Classical.choice, Quot.sound]`, i.e. **genuinely 0-axiom**
(no `sorryAx`/`Lean.ofReduceBool`/`native_decide`). Docker host was DOWN
again (containerd `meta.db` I/O error) so verified via the `lake env lean`
single-file channel.

### What was delivered (`SpernerNDimOQ02.lean`, new section)

The within-cell facet algebra (`facet_injective`, `facet_card`,
`not_mem_facet_iff`) was already closed in Session ≤10. This session adds
the **cross-cell** coherence that makes the `adj` payload well defined —
`adj` stores, per interior facet, the neighbour cell *and its opposite
vertex index*, so a cell must be recoverable from one `(facet, opposite
vertex)` pair:

- `image_univ_eq_insert_facet s k : univ.image (vertices s)
  = insert (vertices s k) (facet s k)`. The full `d+1`-vertex set is the
  `d`-vertex facet plus the deleted vertex. Proof: `univ = insert k
  (univ.erase k)` (`Finset.insert_erase`) pushed through `vertices s`
  (`Finset.image_insert`). One-liner.
- `coe_image_univ_vertices s : ↑(univ.image (vertices s)) =
  Set.range (vertices s)`. Finset→Set bridge (`Finset.coe_image`,
  `coe_univ`, `Set.image_univ`) so the facet algebra can feed
  `canon_eq_of_vertices_range`.
- `canon_eq_of_facet_and_vertex (hface : facet s k = facet t l)
  (hvert : vertices s k = vertices t l) : s = t`. **Capstone.** A canonical
  cell is determined by any ONE facet together with its opposite vertex:
  both cells then have the same full vertex set (facet ∪ {opposite}), and
  `canon_eq_of_vertices_range` (Session ≤10) collapses that to cell
  equality. This is the cross-cell companion of `facet_injective` and the
  exact statement showing the `(facet, opposite-vertex)` data `adj` keeps
  is unambiguous.

### Why this matters (Phase-1)

The vertex/geometry half of the `SpernerTriangulation` carrier is now
essentially complete: carrier (`CanonSimplex`), `vertices`,
`vertices_injective`, per-geometry uniqueness (`canon_eq_of_vertices_range`),
full facet combinatorics, AND cell-recovery-from-facet. The ONLY remaining
obligations for a full instance are the adjacency field `adj` itself (the
Freudenthal facet-pivot / neighbour construction) and its compatibility
fields `adj_symm`/`adj_vertices`/`adj_ne`/`adj_unique_facet`/`boundary_face`.
`canon_eq_of_facet_and_vertex` + `facet_injective` are precisely the
uniqueness lemmas the eventual `adj` discharge will cite.

### Next steps (unchanged ordering; cell-recovery now DONE)
1. ~~`CanonSimplex` carrier + `vertices` + `vertices_injective`~~ DONE.
2. ~~facet combinatorics + cross-cell cell-recovery~~ **DONE this session.**
3. **(next)** Define `adj` via finite facet-search: for cell `s`, facet `k`,
   search `univ : Finset (CanonSimplex)` for a `t ≠ s` with a facet equal to
   `facet s k`; return `some (t, l)` with `l` the (unique, by
   `facet_injective`) matching index, else `none`. Then discharge the 5
   compatibility fields — `adj_unique_facet` falls out of `facet_injective`,
   `adj_ne`/`adj_vertices` are immediate from the search predicate, `adj_symm`
   needs the search to be symmetric, and `boundary_face` is the genuinely
   geometric obligation (a facet with no neighbour lies on `∂Δ_N`).
4. Phase 2: last-face-door-oddness by induction; apply `sperner_ndim`.

---

## Session 2026-06-27 (Session 10, researcher-3) — Per-geometry uniqueness COMPLETE

**Mode**: ACT (CONTINUE Phase-1; execute the Session-9 "next deliverable").
**Outcome**: PROGRESS — added SECTION IX to `SpernerGridBase.lean`: `miss`/`incDir`
recovery and the capstone `IsCanon.geometry_unique`. **Type-check VERIFIED (EXIT 0,
clean)**; **`#print axioms` obtained this session** (host load ~13, no SIGSEGV) —
all four new theorems depend only on `[propext, Classical.choice, Quot.sound]`, i.e.
**genuinely 0-axiom** (no `sorryAx`/`Lean.ofReduceBool`/`native_decide`).

### What was delivered (`SpernerGridBase.lean`, SECTION IX, +~120 L)

Per-geometry uniqueness is now a theorem. The three recovery lemmas are each
*more general than needed* (they take only the shared data they actually use, not
`IsCanon`), and compose with the Session-8 reconstruction theorem:

- `GridSimplex.miss_unique (hbase : verts 0 =) (hset : range verts =) : s.miss = t.miss`.
  `miss` is the unique coordinate at which some cell vertex dips strictly below the
  base. Proof: `d=0` is `Fin 1` (`Fin.ext`/`omega`); for `d≥1`, `t.verts (last)` has
  `t.miss`-coord `base − d < base` (`last_coord_miss` + `base_miss_ge_d`), lies in the
  shared set, so equals some `s.verts m`; if `t.miss ≠ s.miss` then `t.miss = s.incDir k`
  (`incDir_surj_complement`) and `coord_incDir_at` forces that coord `≥ base` — contra.
- `GridSimplex.verts_eq (hbase) (hmiss) (hset) : s.verts = t.verts`. With `miss`+base
  fixed, vertex `m` is the unique cell vertex whose `miss`-coord is `base − m`
  (`miss_coord_at`, injective since `base-coord ≥ d`); so `t.verts m = s.verts m' ⟹
  m = m'` (omega) ⟹ `s.verts = t.verts` (`congrArg ∘ Fin.ext`).
- `GridSimplex.incDir_eq (hverts : s.verts = t.verts) : s.incDir = t.incDir`. **Needs
  only the shared vertex function** (NOT `miss` — the per-simplex `step_dec`/`step_same`
  dichotomy is read off each simplex's own fields). At step `k`, `t.incDir k` increases
  the coord; on the s-side that coord is either `s.miss` (decreases, `step_dec` — contra)
  or unchanged (`step_same` — contra), so `t.incDir k = s.incDir k`.
- `IsCanon.geometry_unique (hs ht : IsCanon) (hset) : s = t`. Capstone:
  `base_unique → miss_unique → verts_eq → incDir_eq → eq_of_base_miss_incDir`.

### Why this matters (Phase-1)

`IsCanon.geometry_unique` is exactly the orientation-free "one representative per
geometric cell" property that the Phase-1 `Simplex := {s : GridSimplex // IsCanon s}`
carrier needs: it kills the Session-1 orientation double-count
(`boundary_doors_odd` counterexample) at the type level. The full chain
`base → miss → verts → incDir → reconstruction` is now closed and 0-axiom.

### Next steps (unchanged ordering; uniqueness now DONE)
1. ~~`miss`/`incDir` recovery ⟹ `geometry_unique`~~ **DONE this session.**
2. **(next)** `Simplex := {s : GridSimplex // IsCanon s}`; `vertices` (toVertex ∘ verts),
   `vertices_injective` (one-liner via `verts_injective`). `geometry_unique` is now the
   tool that makes `Subtype` equality of canonical cells reduce to vertex-set equality.
3. `adj` finite facet-search; 5 adjacency fields + `boundary_face`.
4. Phase 2: last-face-door-oddness by induction; apply `sperner_ndim`.

---

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

---

## Session 2026-06-27 (Session 6, researcher-12) — Step 0 VERIFIED 0-axiom + broken-`SpernerGrid` decoupling

**Mode**: ORIENT (verify Session-3's merged bridge). **Outcome**: the step-0
coordinate bridge is now **machine-verified, 0-axiom**, and was **made buildable**
by factoring out a clean dependency. Docker remained corrupt (containerd
`meta.db` I/O error — dead containers can't even be removed); verification used the
local single-file fallback `LAKE_UNSAFE=1 ./bin/lake env lean` against the main
repo's cached oleans (disk swung 99%↔45% as other agents built/cleaned).

### Finding 1 — `SpernerNDimOQ02.lean` proofs are correct (0-axiom)

All declarations type-check with **no errors, no sorries**. `#print axioms` for
`baryEquivVertex`, `onFace_toVertex`, `isSperner_iff`, `toVertex_injective`,
`toBary_injective` lists only `[propext, Classical.choice, Quot.sound]` (the
ordinary foundational three, which do **not** count under the Axiom Integrity
Policy). No `Lean.ofReduceBool`, no `sorryAx`. → **status: verified, 0-axiom.**

Verified two ways: (a) a standalone harness importing only the *cached*
`SpernerNDim` with the three needed `SpernerGrid` primitives inlined verbatim
(incl. the `@[ext]` on `BaryPoint` — dropping it was the only repro hiccup, since
`BaryPoint.ext` is the auto-generated extensionality lemma); then (b) the **real**
file end-to-end against actual imports (see Finding 2). Both EXIT 0, clean.

### Finding 2 — `SpernerGrid.lean` is un-buildable on `main` (15+ real errors)

Building `SpernerGrid.lean` (its olean was never cached) surfaced **genuine
compile errors**, not just its 2 documented sorries: `omega could not prove`
(@679, 1204, 1222, 1305, 1323, 1350, 1425, 1429), a **syntax error**
`unexpected token '='` @1372, `rewrite failed` (@1359, 1439, 1490, 1502),
type mismatches (@1224, 1326, 1432), `No goals` (@1466, 1556), and
`Unknown identifier hs'` (@1510, 1590). They span the `gridAdj` / `boundaryFlip`
/ boundary-doors machinery (lines ~679–1740) — much of it the exact code Option C
intends to delete. These errors were masked indefinitely by the chronic
"build host down" status. **Consequence**: the merged bridge `import`ed
`Proofs.SpernerGrid`, so the bridge could not actually build despite its own
proofs being correct.

This is *not* a gallery-integrity false claim: `SpernerGrid.lean` is an
`additionalFile` companion of the `sperner-mathlib4` entry, whose verified
*primary* is the separate `SpernerMathlib4.lean`. But the committed file is
broken and should be repaired or retired (mechanic / a later Phase of this OQ).

### Fix delivered — `SpernerGridBase.lean` (clean primitives)

The bridge needs only the three *clean* primitives from `SpernerGrid` SECTION II
(lines 172–223, all before the first error @679): the `@[ext] structure BaryPoint`
(+ its `DecidableEq` / `Fintype` instances), `BaryPoint.onFace`, and `IsSperner`.
Factored these **byte-for-byte** into a new self-contained
`proofs/Proofs/SpernerGridBase.lean` (namespace `SpernerGrid`, `import Mathlib`,
0 sorry / 0 axiom) and re-pointed `SpernerNDimOQ02.lean`'s import
(`import Proofs.SpernerGrid` → `import Proofs.SpernerGridBase`). Result:

- `SpernerGridBase.lean` builds clean (28s).
- `SpernerNDimOQ02.lean` builds clean against real imports (cached `SpernerNDim`
  + new `SpernerGridBase`), 0-axiom (49s). **No stubs, gold-standard verify.**

This *also* unblocks **Phase 1**: the forthcoming `freudenthal d N :
SpernerTriangulation d N` instance can build against the stable, verified
`SpernerGridBase` primitives without ever touching the broken grid-adjacency
proofs. (Single-source-of-truth consolidation — having `SpernerGrid.lean` itself
import `SpernerGridBase` and drop its duplicate defs — is a follow-up deferred
until that file is repaired/retired, to avoid churn/conflicts while it is broken.)

### Recipe notes (for next session)
- Local verify when docker is corrupt: `cd <MAIN repo>/proofs` (has ~8674 cached
  oleans; the worktree's gitignored `.lake` has none), `cp` worktree source in,
  `LAKE_UNSAFE=1 ./bin/lake env lean -o .lake/build/lib/lean/Proofs/X.olean Proofs/X.lean`
  to *persist* a dependency olean, then `… env lean Proofs/Dependent.lean` to check
  the dependent (no `-o` = type-check only). Restore main tree afterward
  (`git checkout` the edited file, `rm` the untracked new one); the olean is safe
  to retain as cache. `#print axioms` works from a `/tmp` copy via the same
  `lake env` LEAN_PATH.
- `BaryPoint`/`Vertex` are both `@[ext]`; reproductions that omit the attribute
  fail with `unknown constant …BaryPoint.ext`.
- Disk is the real gate, not docker: a heavy build can transiently ENOSPC even at
  ~400 MiB free. Single-file checks importing cached oleans are ~30–60s and safe
  when disk ≳ 1 GiB.

> **NOTE (Session 7 merge, researcher-7):** researcher-7 independently made the same
> discovery and fix this day, naming its extraction `SpernerGridBary.lean`. On merge
> the duplicate was retired in favour of the canonical `SpernerGridBase.lean` above;
> all Session-7 files were repointed at `SpernerGridBase`.

## Session 2026-06-27 (Session 7) — Phase-1 cell foundation landed + VERIFIED

**Mode**: ACT. **Infra**: Docker still corrupt; standalone `lake env lean` fallback
works (root FS 47%, healthy). Recipe (`-o` MUST target `.lake/build/lib/lean/Proofs/`,
the dir with the cached gallery oleans — see Session 6 gotcha):
```
cd proofs
LAKE_UNSAFE=1 ./bin/lake env lean Proofs/SpernerGridCell.lean \
  -o .lake/build/lib/lean/Proofs/SpernerGridCell.olean
LAKE_UNSAFE=1 ./bin/lake env lean Proofs/SpernerNDimOQ02Cell.lean \
  -o .lake/build/lib/lean/Proofs/SpernerNDimOQ02Cell.olean
```

### Delivered (both files build clean, 0 sorry / 0 extra axiom)

`Proofs/SpernerGridCell.lean` — clean extraction of `SpernerGrid.lean` SECTIONS
III–V onto the compiling `SpernerGridBase.BaryPoint` foundation. Contents:
`GridSimplex` structure (oriented chain: `verts`/`incDir`/`miss` + the 5 step proof
fields), `gridSimplexDecEq`, `gridSimplexFintype` (noncomputable), and the chain
lemmas `incDir_stable`, `incDir_const_after`, `verts_succ_ne`, **`verts_injective`**,
`vertex_set_card`, `miss_coord_at`, `base_miss_ge_d`, `miss_coord_ge`,
**`incDir_surj_complement`** (every non-`miss` direction is hit by `incDir`), plus
`BaryPoint.transfer` + its 3 coord lemmas (the mass-transfer primitive an adjacency
flip will use). All reproduced strictly *before* the broken `gridAdj` block (lines
~600+ of the parent), namespace `SpernerGrid`, import-disjoint from the broken file.

`Proofs/SpernerNDimOQ02Cell.lean` — the orientation-free pieces of the eventual
`SpernerTriangulation` instance:
- `cellVertices s := fun k => toVertex (s.verts k)` and **`cellVertices_injective`**
  `= toVertex_injective.comp s.verts_injective` — the `vertices` / `vertices_injective`
  fields.
- `onFace_cellVertices` — `onFace (cellVertices s i) k ↔ (s.verts i).onFace k`, an
  alias of `onFace_toVertex`; this is what `boundary_face` will consume.
- Canonicality scaffold: `BaryPoint.lexLe a b` (`a = b ∨ ∃ first-differing coord
  where a < b`, decidable over `Fin (d+1)`), `IsCanon s := ∀ k, (s.verts 0).lexLe
  (s.verts k)` (chain base is lex-least; **`DecidablePred IsCanon`** via
  `unfold IsCanon; infer_instance` — `decidable_of_iff _ Iff.rfl` does NOT unfold the
  finite ∀ and fails to synthesize), the `CanonCell` subtype with `DecidableEq`
  (`Subtype.instDecidableEq`) and noncomputable `Fintype` (`Subtype.fintype`, since
  `gridSimplexFintype` is noncomputable), and `canonVertices`/`canonVertices_injective`.

`#print axioms` on `cellVertices_injective`, `onFace_cellVertices`,
`canonVertices_injective`, `GridSimplex.verts_injective`,
`GridSimplex.incDir_surj_complement` → all `[propext, Classical.choice, Quot.sound]`.

### Remaining for Phase 1 (next session, build-gated)

1. **`adj : CanonCell → Fin (d+1) → Option (CanonCell × Fin (d+1))`** — facet-sharing
   dual graph. For cell `s`, dropped vertex `k`, the facet is the `d`-point set
   `(univ.erase k).image s.verts`; search `Finset.univ : Finset (CanonCell)` for the
   unique other canon cell sharing that facet (via `Finset.filter`/`Finset.choose`
   over the noncomputable `Fintype`, NOT `decide`), returning its complementary vertex
   index, else `none`. The `transfer` primitive (already extracted) constructs the
   reflected vertex when one exists.
2. Discharge `adj_symm` (relation symmetric by construction), `adj_vertices`
   (both images = the shared facet by the search predicate), `adj_ne` (the two cells
   differ on the dropped vertex), `adj_unique_facet` (distinct dropped `k` give
   distinct facet point-sets since `verts` injective), `boundary_face` (no neighbour ⇒
   the `d` retained barycentric points share a face coord ⇒ Kuhn `onFace` via
   `onFace_cellVertices`).
3. **`IsCanon` per-geometry uniqueness** — each geometric cell has exactly one
   canonical encoding (lex has a unique minimum; base + the `miss`-decreasing chain
   force `incDir`/`miss`). Needed so `adj`'s "unique other cell" is well-defined and
   the parity count is by geometry, not by encoding.
4. Assemble `freudenthal d N : SpernerTriangulation d N` (8 fields; `Simplex`/`DecEq`/
   `Fintype`/`vertices`/`vertices_injective` already in hand — 3 of 8 done), apply
   `sperner_ndim`, transport with `isSperner_iff`. Ship as a standalone n-dim Sperner
   result over `BaryPoint` (the original reroute of `SpernerGrid.sperner_grid` stays
   gated on that broken file compiling).

### Re-verification after merge with main (#30779 → SpernerGridBase)

After main landed the canonical clean foundation `SpernerGridBase.lean` (#30779),
the Session-7 files were rebased off the retired `SpernerGridBary.lean` onto
`SpernerGridBase` and **re-verified from scratch** (deleted stale oleans, rebuilt
against the main repo's cached `SpernerGridBase`/`SpernerNDim` oleans via
`LAKE_UNSAFE=1 ./bin/lake env lean`):

- `Proofs/SpernerGridCell.lean` — EXIT 0 (one `<;>` style-linter warning only).
- `Proofs/SpernerNDimOQ02Cell.lean` — EXIT 0.
- `#print axioms` on `cellVertices_injective`, `onFace_cellVertices`,
  `canonVertices_injective`, `GridSimplex.verts_injective`,
  `GridSimplex.incDir_surj_complement`, `GridSimplex.miss_coord_ge` → all
  `[propext, Classical.choice, Quot.sound]`. 0 sorry, 0 extra axiom, post-merge.

GOTCHA encountered: the main repo had a **stale** `SpernerNDimOQ02.olean` built
when that file still imported `SpernerGridBary`; building the cell bridge against it
failed with `environment already contains 'SpernerGrid.baryPointFintype.match_1'
from Proofs.SpernerGridBase` (two modules defining the same `SpernerGrid.*`). Fix:
delete and rebuild `SpernerNDimOQ02.olean` from current (SpernerGridBase-importing)
source before building dependents. Lesson: after a foundation rename, purge every
transitive dependent's cached olean, not just the renamed file's.

---

## Session 2026-06-27 (Session 7) — Phase-1 foundation extracted + reconstruction lemmas

**Mode**: ACT (researcher-12). **Outcome**: PROGRESS — verified, 0-axiom.
**Infra**: docker still corrupt (4 stale `lean-build-*` containers "Up 7 hours");
disk recovered to 47% (~14 GiB free). Used the local `LAKE_UNSAFE=1 ./bin/lake env
lean` single-file fallback against the main repo's cached oleans.

### What was delivered (extends `proofs/Proofs/SpernerGridBase.lean`, now 460 L)

The bridge work (Session 6) extracted only `BaryPoint`/`onFace`/`IsSperner`. But
the Phase-1 instance also needs the **`GridSimplex` foundation**, which was still
trapped in the broken `SpernerGrid.lean` (un-importable). This session factored
the *entire clean region* of `SpernerGrid` (SECTIONS III–V, lines 241–513 — all
before the first compile error @679) into `SpernerGridBase.lean`:

- `structure GridSimplex` (+ `gridSimplexDecEq`, `gridSimplexFintype`) — the
  Simplex carrier with `DecidableEq`/`Fintype` the Phase-1 `Simplex :=
  {s : GridSimplex // IsCanon s}` subtype reuses.
- `incDir_stable`, `incDir_const_after`, `verts_succ_ne`, **`verts_injective`**
  (the `vertices_injective` field), `vertex_set_card`.
- coordinate trackers `miss_coord_at`, `base_miss_ge_d`, `miss_coord_ge`,
  `incDir_surj_complement`.

All copied **byte-for-byte** from the already-checked originals, so no new proof
risk; the value is purely *de-coupling* — Phase-1 can now build its instance over
a clean base with zero dependence on the broken adjacency machinery.

### New lemmas (genuinely new, not extraction) — SECTION VI

Toward the canonical-representative predicate `IsCanon` and the facet-sharing
adjacency, the key fact is that **a cell is fully determined by
`(verts 0, miss, incDir)`**. Proved the coordinate-reconstruction backbone:

- `GridSimplex.incDir_const_before` — mirror of `incDir_const_after`: coord
  `incDir k` is constant (= its base value) at every vertex `m ≤ k.castSucc`.
- `GridSimplex.last_coord_non_miss` — every non-miss coord `j` satisfies
  `(verts last).coords j = (verts 0).coords j + 1` (incremented exactly once).
- `GridSimplex.last_coord_miss` — `(verts last).coords miss = (verts 0).coords
  miss − d` (decremented every step).

Together: `verts last = verts 0 + 𝟙_{≠miss} − d·e_miss`, i.e. the last vertex (and
by the same tracking every vertex) is an explicit function of the base + miss.
This is what makes `canonMiss`/`IsCanon` well-posed next session.

### Verification (gold-standard, no stubs)

`SpernerGridBase.lean` (460 L) builds clean end-to-end (EXIT 0) against real
cached imports; `SpernerNDimOQ02.lean` (the bridge) still builds clean against the
extended base. `#print axioms` on `verts_injective`, `last_coord_non_miss`,
`last_coord_miss`, `incDir_const_before` = `{propext, Classical.choice, Quot.sound}`
only → **verified, 0-axiom**. Main repo working tree restored clean afterward.

### Encoding-uniqueness analysis (sharpens the Phase-1 `IsCanon` design)

Confirmed the GridSimplex-rep needs canonicalization (cannot be skipped): a
facet-sharing dual graph over *all* GridSimplices breaks `adj_unique_facet` /
well-definedness, because a cell `s` and its reverse `s'` share the *same vertex
set* hence the same facets — the "find the other cell containing facet F" search
is ambiguous. So one-cell-per-geometry is mandatory. The cube-Kuhn trick (base =
lex-min vertex ⇒ unique `(base, perm)` by construction) does **not** transfer: the
corner-simplex `{x ≥ 0, ∑ ≤ N}` is not a union of full Kuhn cubes (cells near the
`∑ = N` face would stick out), which is exactly why the bary `+e_a − e_b` model is
used. Hence a separate `IsCanon` predicate over `GridSimplex` is the right tool.
With `last_coord_*` in hand, a clean `canonMiss` choice: the representative whose
chain is monotone for the lex order on `BaryPoint` (equivalently `verts 0` is the
lex-minimal vertex and `incDir` lists the non-miss directions in increasing
order). Uniqueness per geometry follows from `verts_injective` + the reconstruction
lemmas (base + miss + the increasing incDir determine all vertices).

### Next steps (unchanged ordering, now better-equipped)

1. Define `canonMiss`/`IsCanon` (decidable) + per-geometry uniqueness, using
   `last_coord_non_miss`/`last_coord_miss` + `verts_injective`.
2. `Simplex := {s : GridSimplex // IsCanon s}`; `vertices := toVertex ∘ verts`,
   `vertices_injective` from `toVertex_injective ∘ verts_injective`.
3. `adj` via finite facet-search; discharge the 5 adjacency fields + `boundary_face`
   (transport `onFace` via `SpernerNDimOQ02.onFace_toVertex`).
4. Phase 2: last-face-door-oddness by induction; apply `sperner_ndim`.
5. Retire false `boundary_doors_odd`/`boundary_verts_on_face`.

---

## Session 2026-06-27 (Session 8, researcher-3) — Reconstruction theorem (Phase-1 backbone)

**Mode**: ACT (CONTINUE Phase-1). **Outcome**: PROGRESS — added the general
per-vertex coordinate formula and the **reconstruction theorem** to
`SpernerGridBase.lean` (now SECTION VII). **Type-check VERIFIED (EXIT 0)** of the
full file with the additions; **0-axiom by construction**. The `#print axioms`
confirmation was environmentally blocked (see Infra) but the proofs demonstrably
elaborate and the bridge file built against them.

### What was delivered (`proofs/Proofs/SpernerGridBase.lean`, SECTION VII, +70 L)

Sessions 6–7 pinned only the LAST vertex (`last_coord_non_miss`,
`last_coord_miss`). The canonical-representative uniqueness needs every vertex
fixed. Two new theorems close that:

- `GridSimplex.coord_incDir_at (s) (k m)`:
  `(verts m).coords (incDir k) = (verts 0).coords (incDir k) + (if k.val < m.val then 1 else 0)`.
  The general non-miss-coordinate formula at an arbitrary vertex `m` (specializes
  to `last_coord_non_miss` at `m = last`). Proof: `by_cases k.val < m.val`; the
  `<` branch chains `incDir_const_after` + `step_inc` + `incDir_const_before`, the
  `≥` branch is `incDir_const_before` alone. `Fin.le_def`/`Fin.val_succ`/
  `Fin.coe_castSucc` + `omega` discharge the index arithmetic.

- `GridSimplex.eq_of_base_miss_incDir (s t)`:
  `verts 0 = ∧ miss = ∧ incDir = ⟹ s = t`. **The reconstruction theorem.**
  Proof: `funext m; apply BaryPoint.ext; funext j`; split `j = miss`
  (use `miss_coord_at` both sides) vs `j ≠ miss` (use `incDir_surj_complement`
  to get `k` with `incDir k = j`, then `coord_incDir_at` both sides); finish the
  structure equality by `cases s; cases t; subst …; rfl` (mirrors `gridSimplexDecEq`).

**Why this matters (Phase-1 unblock).** Per Sessions 4–5 the `Simplex` carrier is
`{s : GridSimplex // IsCanon s}` with one canonical encoding per geometric cell.
The hard obligation is **per-geometry uniqueness** (two canonical cells with the
same vertex set are equal). With `eq_of_base_miss_incDir`, uniqueness now reduces
to "same vertex set ⟹ same `(verts 0, miss, incDir)`" — i.e. the geometric
lex-min-base argument no longer has to also re-derive the chain coordinate-by-
coordinate; the reconstruction theorem supplies that half outright.

### Verification status (honest)

- **Type-check**: `LAKE_UNSAFE=1 ./bin/lake env lean Proofs/SpernerGridBase.lean`
  → **EXIT 0, clean** (with SECTION VII present). Confirmed early in session.
- **Bridge**: `SpernerNDimOQ02.lean` built **EXIT 0** importing the olean built
  from the SECTION-VII source (same session, before host degraded).
- **`#print axioms`**: NOT obtained this session. The host degraded mid-session
  (load avg ~10–21 from concurrent agent builds); olean *writes* (`-o`) and
  fresh full-Mathlib *re-elaborations* began crashing with SIGSEGV/SIGBUS
  (exit 138/139, **empty logs — no Lean diagnostics**, i.e. environmental, not
  proof errors). 5+ retry attempts all crashed identically.
- **0-axiom by construction**: the two proofs use only `omega`, `rw`, `simp only`,
  `funext`, `by_cases`, `obtain`, `cases`, `subst`, `apply BaryPoint.ext`, `exact`
  — no `sorry`, no `axiom`, no `decide`/`native_decide`. They build solely on
  SECTION VI lemmas already verified `{propext, Classical.choice, Quot.sound}`-only
  in Session 7. So the additions cannot introduce `Lean.ofReduceBool`/`sorryAx`.

### Gotcha (concurrency)
- A concurrent agent `git checkout`-reverted MAIN's `proofs/Proofs/SpernerGridBase.lean`
  mid-session (my staged copy → back to HEAD), so a subsequent olean rebuild
  produced a no-SECTION-VII olean and `#print axioms` reported unknownIdentifier.
  The edit is safe in the WORKTREE; re-cp before any verify. Source of truth =
  worktree, never main's working tree (other agents reset it).

### Next steps (unchanged ordering)
1. **(next)** Define `IsCanon`/`lexLE` (lex order on `BaryPoint`, decidable) and
   prove per-geometry uniqueness via `eq_of_base_miss_incDir` (now available).
2. `Simplex := {s : GridSimplex // IsCanon s}`; `vertices`/`vertices_injective`.
3. `adj` finite facet-search; 5 adjacency fields + `boundary_face`.
4. Phase 2: last-face-door-oddness by induction; apply `sperner_ndim`.
5. Re-run `#print axioms` on SECTION VII once host recovers (expected
   `{propext, Classical.choice, Quot.sound}` only).

---

## Session 2026-06-27 (Session 9, researcher-3) — Lex order + IsCanon + base-uniqueness

**Mode**: ACT (CONTINUE Phase-1, build on Session-8 reconstruction theorem).
**Outcome**: PROGRESS — added SECTION VIII to `SpernerGridBase.lean`: the
lexicographic order on `BaryPoint`, the canonical-representative predicate
`IsCanon`, their decidability instances, and **base-uniqueness** (two canonical
cells with the same vertex set share `verts 0`). **Type-check VERIFIED (EXIT 0)**
of the full file; **0-axiom by construction** (`#print axioms` environmentally
blocked — see Infra).

### What was delivered (`SpernerGridBase.lean`, SECTION VIII, +~110 L)

The `Simplex` carrier for the Phase-1 `SpernerTriangulation` instance is
`{s : GridSimplex // IsCanon s}` — one canonical chain per geometric cell, which
kills the Session-1 orientation double-count. This session built the
canonicalization machinery:

- `BaryPoint.lexLT` / `BaryPoint.lexLE` — first-differing-coordinate lex order on
  `Fin (d+1) → ℕ` (defined directly as `∃ i, (∀ j < i, aⱼ = bⱼ) ∧ aᵢ < bᵢ`, not
  via `Pi.Lex`, to keep decidability a one-liner `inferInstanceAs`).
- `Decidable` instances for both (bounded `∃`/`∀` over `Fin`).
- `lexLE_refl`, `lexLT_irrefl`, `lexLT_asymm` (trichotomy on the two witness
  indices `i`, `i'`; `omega` closes each branch via the prefix-equality), and
  `lexLE_antisymm`.
- `IsCanon s := ∀ k, (s.verts 0).lexLE (s.verts k)` (base is lex-min over the
  chain) + its `Decidable` instance.
- `IsCanon.base_unique` — **the deliverable**: `IsCanon s → IsCanon t →
  Set.range s.verts = Set.range t.verts → s.verts 0 = t.verts 0`. Proof:
  `t.verts 0 ∈ range t = range s` ⟹ `s.verts 0 ≤ t.verts 0` (by `IsCanon s`);
  symmetric; `lexLE_antisymm` closes.

### Why this matters (Phase-1)

Per-geometry uniqueness ("two canonical cells with the same vertex set are
equal") factors as: (a) same base `verts 0` — **done this session**; (b) same
`miss`; (c) same `incDir`; then `eq_of_base_miss_incDir` (Session 8) finishes.
The base is now pinned by the lex-min argument outright.

### The miss/incDir recovery argument (worked out, for next session)

With base `b = verts 0` fixed and vertex set `V` fixed:
- **miss is forced.** Along the chain, coord `miss` strictly *decreases*
  (`step_dec`/`miss_coord_at`: `(verts m).coords miss = b.coords miss − m`), while
  every non-miss coord is *non-decreasing* (`incDir` coords go +1 once, untouched
  coords stay). So `v₁ = b − e_miss + e_{incDir 0}` is below `b` at coordinate
  `miss` **and only there**. Hence: for the unique non-base vertex `w ∈ V` adjacent
  to `b` (or any non-base vertex), `miss` = the unique coordinate `j` with
  `w.coords j < b.coords j`. Two canonical cells with same base + same `V` must
  therefore agree on `miss`. (Lean handle: `miss_coord_at` + `coord_incDir_at`
  give the sign of every coordinate change; `incDir_surj_complement` says the
  non-miss coords are exactly `range incDir`, each +1.)
- **incDir is forced.** Given same base + same miss, order `V` by *decreasing*
  `miss`-coordinate: that recovers the chain `v₀,…,v_d` (miss coord = `b−m` is
  injective in `m`). Then `incDir k` = the unique coordinate that increases from
  `v_k` to `v_{k+1}` (`step_inc` + `step_same`). Same chain ⟹ same `incDir`.
- Then `eq_of_base_miss_incDir` gives `s = t`. **Full per-geometry uniqueness.**

### Verification status (honest)

- **Type-check**: `LAKE_UNSAFE=1 ./bin/lake env lean Proofs/SpernerGridBase.lean`
  → **EXIT 0, clean** with SECTION VIII present.
- **olean build** (`-o`): **EXIT 0** (cached against real Mathlib oleans).
- **`#print axioms`**: NOT obtained — the import-harness re-elaboration crashed
  SIGSEGV (exit 139, **empty logs**, 3+ retries) under host load avg ~17 from
  concurrent agent builds. Environmental, not a proof error (same pattern as
  Session 8). 0-axiom **by construction**: the new proofs use only `rintro`,
  `rcases`, `omega`, `Or.inl/inr`, `exact`, `rw`, `inferInstanceAs`, `.elim`,
  `lt_irrefl`, `lt_trichotomy` — no `sorry`/`axiom`/`decide`/`native_decide` — and
  build solely on SECTION VI–VII lemmas already `{propext, Classical.choice,
  Quot.sound}`-only in Sessions 7–8.

### Next steps (unchanged ordering, base-uniqueness now done)
1. **(next)** Prove `miss`/`incDir` recovery (argument above) ⟹
   `IsCanon.geometry_unique : IsCanon s → IsCanon t → range s.verts =
   range t.verts → s = t`.
2. `Simplex := {s : GridSimplex // IsCanon s}`; `vertices`/`vertices_injective`
   (one-liners via `toVertex_injective ∘ verts_injective`).
3. `adj` finite facet-search; 5 adjacency fields + `boundary_face`.
4. Phase 2: last-face-door-oddness by induction; apply `sperner_ndim`.
5. Re-run `#print axioms` on SECTION VIII once host load recovers.

## Session 2026-06-27 (Session 10, researcher-8) — Facet combinatorics + infra-blocked re-verification

**Mode**: REVISIT/CONTINUE (Phase-1 carrier, building on the merged
`canon_eq_of_vertices_range` from #30819).
**Outcome**: PROGRESS (code) + HONESTY CORRECTION (status). Added the facet
combinatorics of `CanonSimplex` to `proofs/Proofs/SpernerNDimOQ02.lean`
(+79 L, lines 231–310), and **corrected the prior session's "VERIFIED 0-axiom"
overclaim** after a Docker re-verification this session failed on host infra.

### What was delivered (`SpernerNDimOQ02.lean`, new SECTION "Facet structure")

These are the within-cell building blocks the abstract `adj` field's
`adj_vertices`/`adj_unique_facet` obligations cite, defined independently of how
`adj` is eventually built:

- `facet s k := (univ.erase k).image (vertices s)` — the `k`-th `(d-1)`-face
  vertex set (delete vertex `k`, push through the Kuhn bridge).
- `mem_facet_iff` — `v ∈ facet s k ↔ ∃ j ≠ k, vertices s j = v`.
- `vertices_not_mem_facet` — `vertices s k ∉ facet s k` (deleted vertex is the
  unique vertex absent from its own facet; via `vertices_injective`).
- `facet_card` — every facet has exactly `d` vertices
  (`card_image_of_injective` + `card_erase_of_mem`).
- `facet_injective` — **the `d+1` facets of one cell are distinct** = the
  within-cell half of `adj_unique_facet` (a neighbour glues across ≤ 1 facet).
- `not_mem_facet_iff` — `vertices s j ∉ facet s k ↔ j = k` (facet + cell
  determine the removed index).

All proofs use only `simp`/`rw`/`omega`/`rintro`/`by_contra`/`exact` and
`Finset`/`Function.Injective` lemmas on top of the already-verified
`vertices`/`vertices_injective`/`CanonSimplex` layer — **0 sorries, 0 `axiom`,
no `decide`/`native_decide`** (0-axiom by construction).

### Verification status (HONEST)

- **Docker build (this session, researcher-8)**: `./proofs/scripts/docker-build.sh
  Proofs.SpernerNDimOQ02` → **EXIT 125, infra failure**. Logs show repeated
  `thread panicked at src/tar.rs:201 … Os { code: 5, … "I/O error" }` and
  `Error waiting for container: write …/io.containerd.metadata.v1.bolt/meta.db:
  input/output error` while **decompressing 7727 Mathlib oleans**. Root cause:
  Docker VM disk/containerd storage exhausted (host root FS at **1.7 GiB free**,
  **6 concurrent `lean-build` containers** from other agents).
- **Local single-file fallback unavailable**: `SpernerGridBase.olean` not built
  in this worktree and the local Mathlib olean cache is **incomplete** (5760
  oleans, `Mathlib/Tactic.olean` missing), so a safe bounded `lean` elaboration
  cannot resolve imports. (`lake build` is forbidden per CLAUDE.md.)
- **No safe remediation taken**: did NOT `docker prune` — 6 peer builds were
  mid-flight; pruning would destroy other agents' work.
- A prior session's notes claimed a clean Docker build; that **could not be
  reproduced this session**, so the increment is recorded as **UNVERIFIED**,
  0-axiom *by construction*, pending a clean machine-check + `#print axioms`.

### Files modified
- `proofs/Proofs/SpernerNDimOQ02.lean` (+79 L: facet section)
- `src/data/research/problems/sperner-ndim-oq-02.json` (honest status, blockers,
  nextAction, nextSteps)

### Next steps
1. **RE-VERIFY FIRST**: once host disk/Docker recovers, run the docker build +
   `#print axioms` to confirm the facet section is `{propext, Classical.choice,
   Quot.sound}`-only.
2. Then build `adj` (finite facet-search over `CanonSimplex`): the unique
   neighbour sharing facet `k`, or `none` on the boundary.
3. Discharge the 5 adjacency fields + `boundary_face`: `adj_unique_facet` from
   `facet_injective` (within-cell) + `canon_eq_of_vertices_range` (cross-cell);
   `boundary_face` via `onFace_toVertex`.
4. Phase 2: last-face-door-oddness by induction on `d`; apply `sperner_ndim`.

## Session 2026-06-27 (Session 11, researcher-8) — Phase-1 facet section VERIFIED 0-axiom

**Mode**: ACT (researcher-8; execute Session-10's #1 next step: "RE-VERIFY FIRST").
**Outcome**: VERIFIED — the Session-10 facet combinatorics (committed UNVERIFIED on
`main` via #30873) now **build clean and are genuinely 0-axiom**. The prior two
sessions' "UNVERIFIED — infra-blocked" status is **cleared**.

### Verification (gold-standard, no stubs)

Docker remained hard-blocked — `./proofs/scripts/docker-build.sh
Proofs.SpernerNDimOQ02` failed **EXIT 1** at *image inspect/build* with
`write …/io.containerd.metadata.v1.bolt/meta.db: input/output error`. This is
**containerd metadata corruption**, NOT disk (host had 8.4 GiB free; 6 peer
`lean-build` containers running). Did **not** restart/prune Docker — that would
kill the peers' in-flight builds.

Verified instead via the **local single-file fallback**, which this session was
able to *repair*: the main repo's Mathlib olean cache was incomplete (5760/7382
oleans, **root `Mathlib.olean` missing** → no import of `Proofs.SpernerNDim`
could load). Ran `LAKE_UNSAFE=1 lake exe cache get` (download-only, allowed by the
`bin/lake` wrapper; **not** `lake build`) under a disk guard (abort if host free
< 3 GiB — never tripped, ended at 7.2 GiB). Result: cache completed to **7382
oleans + root present**. Then:

1. Rebuilt `SpernerGridBase.olean` from current source — **EXIT 0, clean**.
2. `lake env lean Proofs/SpernerNDimOQ02.lean` (worktree facet version) —
   **EXIT 0, no diagnostics, no sorries**.
3. `#print axioms` on all 8 facet/Phase-1 lemmas (`facet`, `mem_facet_iff`,
   `vertices_not_mem_facet`, `facet_card`, `facet_injective`, `not_mem_facet_iff`,
   `canon_eq_of_vertices_range`, `vertices_injective`) →
   **`[propext, Classical.choice, Quot.sound]` only** for every one. No
   `Lean.ofReduceBool`, no `sorryAx`, no `native_decide`. → **genuinely 0-axiom**
   under the Axiom Integrity Policy.

### GOTCHA banked (cost a false-failure this session)

A **stale dependency olean** masquerades as a proof error. The cached
`SpernerGridBase.olean` (mtime 10:08) predated SECTION IX, so the first
`lake env lean` on the facet file failed with
`unknownIdentifier SpernerGrid.IsCanon` / `…IsCanon.geometry_unique` and four
cascade `uses 'sorry'` *warnings* — all spurious. Rebuilding `SpernerGridBase.olean`
from current source (its `.lean` mtime was newer than its `.olean`) fixed it
outright. **Lesson**: when a single-file `lake env lean` check reports unknown
identifiers for symbols you know exist in an imported file, rebuild that import's
olean before trusting the failure — don't assume the source is wrong.

### Reusable infra win

`lake exe cache get` repaired the host's local Mathlib olean cache to complete
(7382 + root). The single-file `lake env lean` fallback is now available again for
any agent on this host while Docker's containerd stays corrupt.

### State after this session

- `proofs/Proofs/SpernerNDimOQ02.lean` on `main` (== verified bytes, confirmed by
  `diff`) is **VERIFIED, 0-axiom, 0-sorry** through the entire Phase-1 carrier +
  facet combinatorics. No code change needed — this session is a **status
  correction** (knowledge.md + meta.json), not new Lean.
- Problem remains **in-progress**: the OQ target (`boundary_doors_odd` / last-face
  door oddness) is still open; only the Phase-1 carrier/facet infrastructure is done.

### Next steps (unchanged ordering; re-verify now DONE)
1. ~~RE-VERIFY the facet section (build + `#print axioms`)~~ **DONE this session
   (0-axiom).**
2. **(next)** `adj` via finite facet-search over `CanonSimplex`: the unique other
   canonical cell sharing facet `k`, or `none` on the boundary. Discharge
   `adj_vertices` from the facet defs, `adj_unique_facet` from `facet_injective`
   (within-cell) + `canon_eq_of_vertices_range` (cross-cell), `boundary_face` via
   `onFace_toVertex`. ~300–500 L.
3. Phase 2: last-face-door-oddness by induction on `d`; apply `sperner_ndim`.
4. Retire false `boundary_doors_odd`/`boundary_verts_on_face`.

## Session 2026-06-27 (Session 12, researcher-7) — Barycentric facet algebra bridge

**Deliverable (VERIFIED, 0-axiom, 0-sorry).** Added a *barycentric facet*
layer to `proofs/Proofs/SpernerNDimOQ02.lean`, transporting the Kuhn-side
facet algebra to the concrete `BaryPoint` side where the eventual `adj`
(Freudenthal pivot) actually lives. The pivot replaces vertex `k` by the
neighbour from swapping two consecutive `incDir` increments — a barycentric
operation — so `adj_vertices`/`adj_unique_facet` are most naturally
discharged by computing facet equalities over `BaryPoint`s and transporting
them across the injective bridge `toVertex`.

New declarations (all 0-axiom: `#print axioms` = `[propext, Classical.choice,
Quot.sound]` only):

- `baryFacet s k := (univ.erase k).image s.1.verts` — the `d`-vertex
  `Finset (BaryPoint d N)` deleted-vertex set, *before* the Kuhn bridge.
- `mem_baryFacet_iff` — membership ⇔ "a cell vertex other than `k`".
- `facet_eq_image_baryFacet` — `facet s k = (baryFacet s k).image toVertex`
  (the Kuhn facet is literally the image of the barycentric facet; proof is
  `rw [facet, baryFacet, Finset.image_image]; rfl` exploiting
  `vertices = toVertex ∘ verts`).
- `baryFacet_card = d`, `verts_not_mem_baryFacet`, `baryFacet_injective`
  (within-cell uniqueness — barycentric half of `adj_unique_facet`).
- `facet_eq_iff_baryFacet_eq` — **Kuhn-facet equality ⇔ barycentric-facet
  equality**, via `Finset.image_injective toVertex_injective`. This is the
  transport that lets a barycentric pivot computation discharge the abstract
  `adj_vertices` (`facet s k = facet s' k'`).
- `canon_eq_of_baryFacet_and_vertex` — barycentric restatement of
  `canon_eq_of_facet_and_vertex` (cell determined by one barycentric facet +
  its opposite barycentric vertex), the coherence the pivot cites in its own
  language.

**Verification.** Docker image build still blocked (containerd `meta.db`
I/O error); used the single-file `lake env lean` fallback against the
worktree olean cache (dep oleans `SpernerNDim`/`SpernerGridBase` present
under `.lake/build/lib/lean/Proofs/`). `EXIT 0`, clean; `#print axioms` on
all five new theorems shows `[propext, Classical.choice, Quot.sound]` only —
no `sorryAx`, no `Lean.ofReduceBool`. **Genuinely 0-axiom.**

**State after this session.** Phase-1 carrier + Kuhn facet combinatorics +
cell-recovery + **barycentric facet bridge** all VERIFIED 0-axiom. The OQ
target (`boundary_doors_odd` / last-face door oddness) remains open. Only the
`adj` pivot function + its 5 compatibility fields + `boundary_face` remain
for a full `SpernerTriangulation` instance.

### Next steps (unchanged target, bridge now in place)
1. **(next)** Construct the interior-facet pivot at the `GridSimplex` level:
   for interior `k`, the neighbour with `incDir' = incDir ∘ swap(k-1, k)`,
   same `miss`, vertex `k` replaced by the swapped pivot point. Prove it
   shares `baryFacet … k` (now expressible via `facet_eq_iff_baryFacet_eq`).
2. Boundary detection: which facets are on the geometric boundary
   (`adj = none`), feeding `boundary_face` via `onFace_toVertex`.
3. Assemble `adj` over `CanonSimplex` + discharge the 5 fields.
4. Phase 2: last-face-door-oddness by induction on `d`; apply `sperner_ndim`.
## Session 2026-06-27 (researcher-2) — facet/opposite-vertex global coherence + `adj` recon

**Mode**: ACT then SURVEY. **Outcome**: small verified increment (0-axiom) + actionable
reconnaissance that re-sizes the remaining `adj` build.

### What I Did (verified, 0-axiom)
Added `facet_vertex_injective`: the map `(s, k) ↦ (facet s k, vertices s k)` is injective on
`CanonSimplex d N × Fin (d+1)`. This packages the facet section's two halves into the single
global-injectivity fact the door-counting adjacency reasons with — cross-cell
`canon_eq_of_facet_and_vertex` collapses `s = t`, then within-cell `facet_injective` collapses
`k = l`. Consequence: the `(facet, opposite-vertex)` payload an `adj` entry stores names at most
one `(cell, facet)` slot (no gluing/orientation ambiguity). Offline-verified
`LAKE_UNSAFE=1 lake env lean Proofs/SpernerNDimOQ02.lean` EXIT 0; `#print axioms` →
`[propext, Classical.choice, Quot.sound]` only. File 360→378 lines, 19→20 theorems, 6 defs,
0 sorries, 0 axioms.

### Reconnaissance: where the geometric `adj` construction actually lives (IMPORTANT)
The genuine next step (`adj : CanonSimplex → Fin(d+1) → Option(CanonSimplex × Fin(d+1))` +
its 5 fields + `boundary_face`) needs the actual Freudenthal cell-flip. That flip machinery
**already exists in `proofs/Proofs/SpernerGrid.lean`** (NOT SpernerGridBase): `GridSimplex.interiorFlip`
(L574), `boundaryFlip0` (L819), `boundaryFlipLast` (L968), dispatched by `gridAdj` (L1113).
BUT its header (SpernerGrid.lean L78–86) documents a **known correctness bug**: `gridAdj` treats
"can't do boundary flip" as "geometric boundary", which is WRONG when the adjacent simplex has a
different `miss` direction (cross-miss neighbours). The fix "requires extending GridSimplex to
track cross-miss neighbors, or restricting to d=0". This is exactly why Option-C builds `adj`
freshly over `CanonSimplex` rather than reusing `gridAdj`.

**Re-sized estimate**: completing `adj` over `CanonSimplex` is a genuine multi-session
DEEP-DIVE/BUILD (the flip + cross-miss handling + 5 field discharges + boundary induction,
realistically >500 L) — too large to responsibly complete+verify in one offline session. The
facet-combinatorics scaffolding the discharge will cite is now COMPLETE (facet_injective,
canon_eq_of_facet_and_vertex, facet_vertex_injective, not_mem_facet_iff, image_univ_eq_insert_facet,
onFace_toVertex). The missing input is purely the *geometric* neighbour-existence map.

### Next steps (re-ordered with the recon)
1. **(crux)** Decide adj source: (a) salvage SpernerGrid.lean's `interiorFlip`/`boundaryFlip*`
   by adding cross-miss tracking, then lift across the `toVertex` bridge to `CanonSimplex`; OR
   (b) define the flip directly on `CanonSimplex` via the Kuhn coordinate reflection. Path (b)
   avoids inheriting the gridAdj bug but re-derives the flip.
2. Discharge `adj_symm`/`adj_vertices`/`adj_ne`/`adj_unique_facet` from the facet scaffolding
   (mostly present) + `boundary_face` via `onFace_toVertex`.
3. Phase 2: last-face-door-oddness induction on `d`; apply `sperner_ndim`.

### Build env note
Docker still meta.db I/O-corrupt (containerd), but the host Mathlib olean cache is COMPLETE
on this worktree (7382 + root Mathlib.olean present; SpernerGridBase/SpernerNDim oleans present)
so `LAKE_UNSAFE=1 ./bin/lake env lean Proofs/SpernerNDimOQ02.lean` works EXIT 0. (Source mtimes
newer than oleans but functionally adequate — build clean, no stale-olean unknownIdentifier.)

## Session 2026-06-27 (researcher-2, Session 8) — interior-pivot canonicality criterion

**Mode**: ACT. **Outcome**: small verified increment (0-axiom) toward the CanonSimplex `adj`.

### What I Did (verified, 0-axiom)
The interior Freudenthal pivot `pivotSimplex s a b hb` (already in the file: shares the
facet opposite `a.succ`, moves the opposite vertex) lives on raw `GridSimplex`. The
genuine remaining blocker is lifting it to `CanonSimplex` — and the obstruction is that
the pivot need NOT be canonical (`IsCanon s := ∀k, (s.verts 0).lexLE (s.verts k)`; the
moved vertex can drop below the base). I isolated exactly that obstruction:
- `pivot_base_eq`: the interior pivot **fixes the lex-base** `verts 0`. It only updates
  `verts a.succ`, and `a.succ ≠ 0`, so `Function.update_of_ne (Fin.succ_ne_zero a).symm`.
- `pivot_isCanon_iff`: given `s` canonical, `IsCanon (pivotSimplex s a b hb) ↔
  (s.verts 0).lexLE (pivotPoint s a b ...)`. Every unchanged vertex already dominates
  the (shared) base via `hs`, so the `d+1` canonicality conditions collapse to the
  **single** comparison on the one moved vertex.

### Why it matters
This is precisely the recanonicalization test the CanonSimplex-level `adj` construction
must run: the interior pivot already lands on the canonical representative of its
geometric cell iff that one lex inequality holds; otherwise `adj` must re-sort to the
lex-min base. It converts "is the pivot the canonical cell?" from a `d+1`-fold check
into one decidable comparison.

### Gotchas / API
- `IsCanon` is in `SpernerGrid` namespace (`SpernerGridBase.lean:609`), `lexLE` is
  `BaryPoint.lexLE` (dot notation on `verts k` works). `Fin.succ_ne_zero a : a.succ ≠ 0`;
  use `.symm` for `0 ≠ a.succ` in `Function.update_of_ne`.
- The pivot's value field is `pivotPoint s a b (pivot_ab_ne hb)` — match it exactly in
  the `show Function.update s.verts a.succ (pivotPoint …) _ = _` rewrites.

### Verification
Docker host still containerd-corrupt; host `lake env lean Proofs/SpernerNDimOQ02.lean`
EXIT 0, no warnings (dep oleans SpernerNDim/SpernerGridBase present in symlinked `.lake`).
`#print axioms` (inline, fresh `lake env lean` compile then restore): `pivot_isCanon_iff`
and `pivot_base_eq` = `[propext, Classical.choice, Quot.sound]` only. File 738→775 lines,
+2 theorems (33 thm/lemma total), 0 sorries.

### Next steps
1. **(crux, multi-session)** `adj` over `CanonSimplex`: dispatch interior facets to the
   pivot, recanonicalize via `pivot_isCanon_iff` (re-sort vertices to lex-min base when
   the test fails), return `none` on the geometric boundary. Discharge the 5 fields from
   the existing facet scaffolding (facet_unique_neighbor / facet_injective /
   facet_vertex_injective) + `pivot_facet_eq`/`pivot_opposite_ne`.
2. Phase 2: last-face-door oddness induction on `d`; apply `sperner_ndim`.

## Session 2026-06-27 (researcher-2) — the interior pivot is an involution

**Mode**: ACT. **Outcome**: verified increment (0-axiom) toward CanonSimplex `adj` / `adj_symm`.

### What I Did (verified, 0-axiom)
`pivot_involutive`: the interior Freudenthal pivot is an **involution** —
`pivotSimplex (pivotSimplex s a b hb) a b hb = s`, with the *same* `(a, b, hb)`. This is
the geometric heart of the adjacency symmetry `adj_symm` for chain-interior facets: the
pivot-based neighbour relation is symmetric, each facet-flip its own reverse.

### Proof idea
Two facts combine. (1) The direction permutation `Equiv.swap a b` is its own inverse, so
the doubly-pivoted `incDir` returns to `s.incDir` (`Equiv.swap_apply_self`). (2) The second
`pivotPoint` exactly undoes the first: in the pivoted cell `t` the move directions are
*swapped* (`t.incDir a = s.incDir b`, `t.incDir b = s.incDir a` via `swap_apply_left/right`),
so the back-pivot moves `incDir a` *up* and `incDir b` *down*, reversing the original move.
The whole proof reduces to `pivotPoint t a b = s.verts a.succ` (3-way `by_cases` on `j` vs
`s.incDir a` / `s.incDir b`, each closed by the `pivotPoint_coords_eq_inc{A,B,other}` lemmas
+ `omega` for the `x+1-1=x` natural-subtraction step), then `GridSimplex` field extensionality.

### Gotchas / API
- `GridSimplex` carries no `@[ext]` (only `BaryPoint` does, `SpernerGridBase.lean:38`). Added a
  local `gridSimplex_ext` (`cases s; cases t; cases hv; cases hi; cases hm; rfl` — the Prop
  fields collapse by definitional proof irrelevance). The vertex field uses
  `Function.update_idem` (`update (update f a x) a y = update f a y`) then
  `Function.update_eq_self` (`update f a (f a) = f`).
- `set t := pivotSimplex s a b hb with ht` keeps `t` definitionally transparent: the `show`
  unfoldings of `t.incDir` (`= s.incDir ∘ ⇑(Equiv.swap a b)`) and `t.verts` work, and
  `have htv : t.verts = … := rfl` succeeds.
- To rewrite a `pivotPoint_coords_eq_incB t …` (stated at `t.incDir b`) into a goal indexed by
  `s.incDir a`, first `rw [← hib]` (`hib : t.incDir b = s.incDir a`) to align the coord index.

### Verification
Docker host down; host `v4.26.0` `lake env lean Proofs/SpernerNDimOQ02.lean` → exit 0, no
warnings (dep oleans `SpernerNDim`/`SpernerGridBase` present in the symlinked `.lake`).
`#print axioms SpernerNDimOQ02.pivot_involutive` = `[propext, Classical.choice, Quot.sound]`
(0-axiom). File 775 → 840 lines, 33 → 35 theorems (+ private `gridSimplex_ext`).

### Next steps
1. Lift the involution across recanonicalization (`pivot_isCanon_iff`): when the pivot is not
   canonical, re-sort to the lex-min base (lex linear-order infra) so the symmetric partner
   lives in `CanonSimplex`.
2. Boundary-chain pivots (deleted vertex `0` or `Fin.last`) — the interior/boundary dichotomy.
3. Assemble `adj` over `CanonSimplex`; discharge `adj_symm` via `pivot_involutive` + recanon.
4. Phase 2: last-face door oddness induction on `d`; apply `sperner_ndim`.

## Session 2026-06-28 (researcher-3) — interior/boundary facet predicate

**Mode**: ACT. **Outcome**: verified increment (0-axiom) — the facet split the door-counting `adj` needs.

### What I Did (verified, 0-axiom)
Added the chain-interior facet predicate on Kuhn facet indices and its numeric characterization:
- `IsInteriorFacet (k : Fin (d+1)) : Prop := ∃ a b : Fin d, a.succ = b.castSucc ∧ k = a.succ`
  — `k` is the facet opposite an interior vertex `a.succ` of a consecutive Kuhn step pair.
- `isInteriorFacet_iff : IsInteriorFacet k ↔ 0 < (k:ℕ) ∧ (k:ℕ) < d` — the two extreme
  facets `0` and `Fin.last d` are exactly the geometric boundary.
- `not_isInteriorFacet_zero`, `not_isInteriorFacet_last` — boundary facets are not interior.
- `exists_neighbor_of_isInteriorFacet` — every interior facet carries a glued neighbour
  (wraps `exists_gridFacet_neighbor`), the total existence datum `adj` records at interior facets.

This discharges next-step #1 from the prior (researcher-95989) session: "Define boundary/interior
facet predicate on GridSimplex (facet k interior iff 1≤k≤d-1); pair with exists_gridFacet_neighbor".

### Gotchas / API
- After `apply Fin.ext` on a goal built from `(⟨x,h⟩ : Fin d).succ` / `.castSucc`, `omega` CANNOT
  see through `↑⟨x,h⟩` nor `↑(Fin.succ ⟨x,h⟩)` — it treats them as opaque atoms (`rw [Fin.val_succ,
  Fin.coe_castSucc]` leaves `↑↑⟨k,h⟩` un-reduced). Fix: drop to the defeq numeric goal with
  `show (k:ℕ) - 1 + 1 = (k:ℕ)` (Fin.succ/castSucc of a `Fin.mk` reduce definitionally), then `omega`.
- Forward direction: `congrArg Fin.val hb` then `rw [Fin.val_succ, Fin.coe_castSucc]` gives
  `(a:ℕ)+1 = (b:ℕ)`; combine with `b.isLt` and `omega`.

### Verification
Docker host still unavailable; host `v4.26.0` `lake env lean Proofs/SpernerNDimOQ02.lean` → EXIT 0,
no warnings (dep oleans SpernerNDim/SpernerGridBase in symlinked `.lake`).
`#print axioms isInteriorFacet_iff` and `exists_neighbor_of_isInteriorFacet`
= `[propext, Classical.choice, Quot.sound]` only (0-axiom). File 1455 → 1512 lines, +1 def +4 thms.

### Next steps
1. **(crux)** Define a total neighbour map on `GridSimplex`/`CanonSimplex`: interior facets →
   `exists_neighbor_of_isInteriorFacet`, boundary facets (`0`, `Fin.last d`) → `none`.
2. Discharge the abstract door-graph `adj` fields for `d ≥ 2` from `GridGlued.{ne,shares_facet}`,
   `GridGlued_symm`, `gridFacet_unique_neighbor`, `gridFacet_card`; supply `boundary_face` from
   `not_isInteriorFacet_zero/last`. Handle `d ≤ 1` base cases separately (orientation doubling).
3. Phase 2: last-face door oddness by induction on `d`; apply `sperner_ndim`.

## Session 2026-06-28 (researcher-3) — total door-graph neighbour map

**Mode**: ACT (CONTINUE — executed next-step #1 "Define a total neighbour map on
GridSimplex: interior facets → exists_neighbor_of_isInteriorFacet, boundary → none").
**Outcome**: verified increment, no extra axioms. `SpernerNDimOQ02.lean` 1704→1772 L,
+1 noncomputable def +4 theorems. Single-file `LAKE_UNSAFE=1 ./bin/lake env lean
Proofs/SpernerNDimOQ02.lean` → exit 0, no warnings. `#print axioms` on all four new
theorems = `[propext, Classical.choice, Quot.sound]` (Classical.choice already pervades the
file; no sorryAx, no Lean.ofReduceBool).

### Delivered
- **`gridNeighbor (s) (k) : Option (GridSimplex d N)`** — `if IsInteriorFacet k then
  some (Classical.choose (exists_neighbor_of_isInteriorFacet s hk)) else none`. The concrete
  `adj`-shaped within-chain neighbour datum.
- **`gridNeighbor_eq_none_iff`** — the `none` fibre is *exactly* `{0, Fin.last d}` (via
  `not_isInteriorFacet_iff` / `IsBoundaryFacet`). This is the index-level `boundary_face`
  bookkeeping the door count needs.
- **`gridNeighbor_spec`** — on an interior facet it returns `some t` with
  `GridGlued s t ∧ t ≠ s ∧ gridFacet t k = gridFacet s k` (genuine distinct facet-sharing
  partner), reusing `Classical.choose_spec`.
- **`gridNeighbor_boundary`**, **`gridNeighbor_isSome_iff`** (defined ↔ interior).

### Gotchas
- In `gridNeighbor_eq_none_iff`, after `simp only [dif_neg hk]` the LHS `none = none`
  defeq-reduces to `True`, so `iff_of_true rfl …` fails ("rfl has type ?=? expected True").
  Use `iff_of_true trivial …` (robust to either `none = none` or `True`).
- For `gridNeighbor_isSome_iff`, rewriting through `gridNeighbor_eq_none_iff` leaves
  `¬ IsBoundaryFacet k ↔ IsInteriorFacet k`, NOT `¬ IsInteriorFacet k`, so a further
  `rw [not_isInteriorFacet_iff]` can't fire. Discharge directly with the dichotomy:
  `(isInteriorFacet_or_boundary k).resolve_right h` (→) and
  `fun h hb => not_isInteriorFacet_of_boundary hb h` (←).
- `gridNeighbor` must be `noncomputable` (uses `Classical.choose`).

### Scope honesty
This packages the **within-chain (pivot)** neighbour structure only. The genuine remaining
frontier — a chain-boundary facet `k ∈ {0, Fin.last d}` that is interior to `Δ_N` is glued
*across* Kuhn chains, which `pivotSimplex` does not produce — is unchanged (flagged in the
module header). `gridNeighbor` sends every boundary facet to `none`; turning that into the
true `adj` still needs the cross-chain gluing (or a proof such facets lie on `∂Δ_N`).

### Next steps
1. **(crux, unchanged)** Cross-chain gluing for boundary facets interior to `Δ_N`, OR prove
   such facets lie on `∂Δ_N`; then `boundary_face` via `boundary_face_iff_coords_zero`.
2. Discharge the abstract door-graph `adj` fields for `d ≥ 2` using `gridNeighbor_spec` +
   `GridGlued.{ne,shares_facet}`, `GridGlued_symm`, `gridFacet_unique_neighbor`.
3. Phase 2: last-face door oddness induction on `d`; apply `sperner_ndim`.

## Session 2026-06-30 (researcher-3) — REGRESSION RECOVERY: restore pivot/neighbour/boundary machinery

**Mode**: ACT (recovery). **Outcome**: PROGRESS — recovered ~1300 lines / ~70 verified
declarations that were silently deleted from `main`, and re-integrated them with the newer
bridge section. **PR #31750**, docker-build VERIFIED, 0-sorry / 0-axiom.

### The regression (important — check before extending this file)
`SpernerNDimOQ02.lean` was **1772 lines** after #31443 (per-vertex boundary evaluation) and
#31495 (`gridNeighbor` total door-graph neighbour map). On 2026-06-30 PR **#30947** (the
older *barycentric facet algebra bridge*, a LOW-numbered PR merged LATE) squash-merged from
a base predating that work and **overwrote the file back to 464 lines**, dropping ~70 decls:
`pivotSimplex`, `pivot_involutive`, `pivotPoint`, `GridGlued`, `gridNeighbor`,
`gridNeighbor_spec`, `exists_neighbor_of_isInteriorFacet`, `IsInteriorFacet`/`IsBoundaryFacet`,
`isInteriorFacet_iff`, `boundary_face_iff_coords_zero`, `coord_incDir_eq_zero_iff`,
`miss_coord_eq_zero_iff`, `gridFacet*`, `baseOf*`, etc. The 464-line version kept only the
8 new bridge decls (`baryFacet`, `facet_eq_iff_baryFacet_eq`, `canon_eq_of_baryFacet_and_vertex`, …).

### What was delivered
Rebuilt the file as the UNION: base = 1772-version (`ee81c8ebb30`), then appended the 8 new
bridge decls from the 464-version (`09b7a20b816`). Shared foundational decls (`facet`,
`canon_eq_of_facet_and_vertex`, `CanonSimplex`, `toVertex`) are byte-identical across both,
so the append composes. Result: **1897 L, 110 decls, 0-sorry, 0-axiom**; docker-build clean;
`#print axioms` on restored+new decls = `[propext, Classical.choice, Quot.sound]`.

### How to reproduce the merge (if it regresses again)
`git show ee81c8ebb30:proofs/Proofs/SpernerNDimOQ02.lean` (1772, has gridNeighbor) is the base;
append lines 360–464 of `git show 09b7a20b816:...` (the "Barycentric facet algebra" section)
after dropping the base's trailing `end SpernerNDimOQ02`.

### Frontier UNCHANGED
The genuine blocker is still the **cross-chain gluing**: a chain-boundary facet
`k ∈ {0, Fin.last d}` interior to Δ_N is glued to a cell in a DIFFERENT Kuhn chain (different
`miss`), which `pivotSimplex` does not produce. `gridNeighbor` sends every boundary facet to
`none`. Turning that into the true `adj` needs either the cross-`miss` partner construction or
a proof such facets lie on ∂Δ_N. This recovery does NOT advance that — it re-establishes the
toolkit needed to attack it.

### Next steps
1. **(crux, unchanged)** Cross-chain `adj` for boundary facets interior to Δ_N.
2. Discharge abstract door-graph `adj` fields for `d ≥ 2` from `gridNeighbor_spec` +
   `GridGlued.{ne,shares_facet}`, `GridGlued_symm`, `gridFacet_unique_neighbor`.
3. Phase 2: last-face door oddness induction on `d`; apply `sperner_ndim`.

## Session 2026-06-30 (researcher-1) — Geometric boundary faces localized to the top facet

**Mode**: ACT (CONTINUE Phase-1, next-step "increase-direction boundary_face characterization").
**Outcome**: PROGRESS — ran the per-vertex coordinate evaluation to its conclusion. Added a
"Geometric boundary faces are localized to the top facet" section to `SpernerNDimOQ02.lean`
(**+4 theorems, ~90 L**). **Docker build VERIFIED** (`docker-build.sh Proofs.SpernerNDimOQ02`,
`Built Proofs.SpernerNDimOQ02 (20s)`, 7745 jobs, exit 0); still **0-sorry, 0-axiom** (new decls
use only `coord_incDir_eq_zero_iff`, `miss_not_boundary_face`, `incDir_surj_complement`, `omega`,
`rw`, `simp`, `by_contra` — no `native_decide`). File now **2040 L / 99 theorems** (rebased onto
the #31750-restored + `gridNeighbor_involutive` base).

### What was delivered
- **`incDir_boundary_face_imp_last (s c) (h)`** `: (∀ j ≠ incDir c, (verts j).coords (incDir c) = 0)
  → incDir c = Fin.last d`. The last chain vertex (value `d`), if not the omitted vertex, would
  need `d = (Fin.last d).val ≤ c.val` by `coord_incDir_eq_zero_iff`, impossible for `c : Fin d`.
- **`boundary_face_imp_last (s) (hd : 2 ≤ d) (k) (h)`** `: (∀ j ≠ k, (verts j).coords k = 0)
  → k = Fin.last d`. Unifies both cases: `k = miss` excluded by `miss_not_boundary_face`;
  `k = incDir c` forced to the top by the lemma above (via `incDir_surj_complement`).
- **`gridVertices_boundary_face_imp_last`** — carrier (`SpernerNDim.onFace`) form, the shape a
  total `adj` discharges directly.
- **`zero_not_boundary_face (s) (hd : 2 ≤ d)`** `: ¬ (∀ j ≠ 0, (verts j).coords 0 = 0)`. Facet `0`
  is **never** a geometric boundary face.

### Why this matters (sharpens the frontier, does NOT close it)
`gridNeighbor` sends BOTH index-level boundary facets `{0, Fin.last d}` to `none`
(`gridNeighbor_eq_none_iff`) — a *within-chain* artifact of `pivotSimplex`, not the geometry.
This session proves the **geometric** `none`-fibre of a Freudenthal cell is at most the singleton
`{Fin.last d}`, strictly inside `{0, Fin.last d}`. Consequence: **facet `0` must carry a
cross-chain pivot partner** — it is precisely the facet the cross-Kuhn gluing construction still
has to produce, and it is never a genuine `∂Δ_N` door. This localizes the remaining obligation
from "the 2-element boundary index set" down to "facet `0` interior to `Δ_N`".

### ⚠️ Frontier UNCHANGED (the genuine blocker — same as all prior sessions)
Still the **cross-chain gluing**: constructing the cross-`miss` partner for facet `0` (now
identified as the sole non-top facet without a within-chain partner) — or proving facet `0` of a
`Δ_N`-boundary cell lies on `∂Δ_N`. This session is the coordinate-evaluation payoff that names
*which* facet the gluing must address; the construction itself (≳ several hundred lines) is untouched.

### Next steps
1. **(crux, unchanged)** Cross-`miss` partner for facet `0`, or `0 ∈ ∂Δ_N` proof.
2. Define a total `adj` with geometric none-fibre exactly `{Fin.last d}` on interior cells; then
   `boundary_face` via `gridVertices_boundary_face_imp_last`.
3. Assemble `SpernerTriangulation`; Phase 2 door oddness induction on `d`; apply `sperner_ndim`.

## Session 2026-07-01 (researcher-1) — Geometric ∂Δ_N boundary over ALL coordinates; facet 0 is unconditionally interior

**Mode**: ACT (CONTINUE Phase-1). **Outcome**: PROGRESS — sharpens the frontier
dichotomy with a genuine negative result; does NOT close it. **+3 theorems, ~108 L**
(file 2407 → 2515 L). **0-sorry, 0-axiom by construction** (new decls use only
`coord_incDir_at`, `miss_coord_pos_of_ne_last`, `incDir_surj_complement`,
`gridVertices_onFace_iff`, `omega`, `rw`, `simp only`, `by_cases`, `by_contra` — no
`native_decide`/`decide`).

### What was delivered (`SpernerNDimOQ02.lean`, appended before `end`)
All prior boundary lemmas (`boundary_face_imp_last`, `zero_not_boundary_face`, …) test
the SINGLE coordinate whose index matches the dropped facet index `k`
(`(verts j).coords k = 0`) — that is the obligation a `gridNeighbor`-`none` facet
discharges. But the genuine *geometric* question "does facet `k` lie on `∂Δ_N`?" tests
whether the `d` facet vertices share a common vanishing coordinate `i`, over ANY
`i : Fin (d+1)`, not just `i = k`.

- **`geom_boundary_face_imp_last (s) (hd : 2 ≤ d) (k)`** :
  `(∃ i, ∀ j ≠ k, (verts j).coords i = 0) → k = Fin.last d`. Generalizes
  `boundary_face_imp_last` from the index-matched coordinate to an ARBITRARY coordinate.
  Proof splits `i` via `incDir_surj_complement`: the `miss` case is impossible (some
  non-top vertex `≠ k` has positive `miss`-coord, since `d ≥ 2` leaves `≥ 3` indices);
  an `incDir c` coordinate at `Fin.last d` is `base + 1 > 0` unless the top vertex is
  the dropped one (`coord_incDir_at`, `c.val < d`).
- **`gridVertices_geom_boundary_face_imp_last`** — carrier (`SpernerNDim.onFace`) form.
- **`zero_facet_not_on_boundary (s) (hd : 2 ≤ d)`** :
  `¬ ∃ i, ∀ j ≠ 0, (verts j).coords i = 0`. Facet `0` lies on NO coordinate hyperplane
  — it is UNCONDITIONALLY strictly interior to `Δ_N`.

### Why this matters (sharpens the frontier — a negative result)
Prior session (r1, 06-30) localized the geometric `none`-fibre to `⊆ {Fin.last d}` using
the index-matched tests, and identified facet `0` as the sole non-top facet lacking a
within-chain pivot partner — but left open whether facet `0` might still escape to
`∂Δ_N` (frontier-option (b): "prove facet 0 of a Δ_N-boundary cell lies on ∂Δ_N, so
`adj = none` is sound"). **This session closes option (b): facet `0` is interior against
EVERY coordinate hyperplane, never on `∂Δ_N`.** Therefore a total triangulation `adj`
CANNOT legitimately send facet `0` to `none`; the cross-`miss` partner construction for
facet `0` is *unavoidable* (only frontier-option (a) survives). This does not build that
construction — it proves it is the sole remaining path.

### ⚠️ Frontier UNCHANGED (the genuine blocker — same as all prior sessions)
Still the **cross-chain gluing**: construct the cross-`miss` partner cell for facet `0`
(now proved to be the ONLY option, no `∂Δ_N` escape). ≳ several hundred lines, untouched.

### ⚠️ INFRA NOTE (full machine-verification blocked — host-level, not code)
BOTH channels down this session:
- **Direct `lean`/`lake env lean`**: host Mathlib olean cache is missing exactly ONE
  data file — `Mathlib/RingTheory/Kaehler/Basic.olean.server` (stale Jun-30 olean; all
  7375 other modules' `.server` files regenerated Jul-01 05:53). Any file transitively
  under `import Mathlib` fails at the import line with `missing data file for module
  Mathlib.RingTheory.Kaehler.Basic`. Regenerating it correctly requires lake's exact
  build options (an ad-hoc `lean -Dexperimental.module=true` recompile diverges into
  synthesis errors + `sorry`), and mutating the shared cache would risk hash-mismatch
  for other agents — so NOT attempted.
- **Docker (`docker-build.sh`)**: containerd blob I/O error — `docker image inspect
  lean4-arm64:v4.26.0` and `docker images` both fail reading the image blob (corrupted
  `/var/lib/desktop-containerd`). Cannot start a fresh build container.

**Mitigation**: the non-obvious tactic bookkeeping (the `Fin`/`omega` steps: picking a
non-top vertex `≠ k`, the `incDir` `base+1>0` contradiction, the `0 = Fin.last d`
refutation) was machine-verified in an ISOLATED file importing only `Mathlib.Data.Fin.Basic`
(avoids the Kaehler-poisoned aggregate) with the Sperner lemmas replaced by abstract
hypotheses of identical shape — **compiles exit 0**. That check CAUGHT A REAL BUG
(`hi 0 (fun h => hk0 h.symm)` had the wrong argument order; `hk0 : ¬(0 = k)` already has
type `0 ≠ k`, so it must be `hi 0 hk0`) which was fixed before commit. All cited lemma
signatures were read from source and match the abstract stand-ins exactly.

### Next steps (unchanged crux)
1. **(crux)** Cross-`miss` partner cell for facet `0` — now the SOLE path (option (b)
   formally eliminated by `zero_facet_not_on_boundary`).
2. Define total `adj` with geometric none-fibre exactly `{Fin.last d}` on interior cells.
3. Assemble `SpernerTriangulation`; Phase-2 door oddness induction on `d`.

## Session 2026-07-04 (Session 18, researcher-11) — Facet-0 pivot miss-descent + termination

**Mode**: ACT (CONTINUE Phase-1). **Outcome**: PROGRESS — structural characterization
of the facet-0 pivot dynamics; does NOT close the frontier. **+4 theorems, +66 L.**
**0-sorry, 0-axiom**; `docker-build.sh Proofs.SpernerNDimOQ02` → exit 0, 7745 jobs.
Shipped as **PR #34635** (`research` label). Built on the session-16/17 `zeroPivotCell`
(facet-0 cross-chain partner, merged #34629).

### What I did
The same-`miss` facet-0 partner `zeroPivotCell s` reuses `s`'s upper chain
`verts 1, …, verts d`, so its base vertex is `s.verts 1` — one step down the chain in
the shared `miss` direction. Proved the pivot is a **finite monotone descent in
`base_miss` terminating at the geometric boundary door**:

- `zeroPivotCell_base_miss` — partner base `miss` coord = `base_miss − 1` (`miss_coord_at`).
- `zeroPivotCell_base_miss_lt` — strict descent.
- `zeroPivot_infeasible_iff_base_miss_eq_d` — same-`miss` pivot infeasible ⟺ `base_miss = d`
  (minimal value; `base_miss_ge_d` + `zeroPivot_feasible_iff`). The extremal cell's top
  vertex already sits on the geometric `miss`-face.
- `zeroPivotCell_feasible_iff_base_miss_ge` — partner re-feasible for its own facet-0
  pivot ⟺ `base_miss ≥ d + 2`; each pivot lowers `base_miss` by one until it halts at `d`.

### Why this matters
Exhibits the same-`miss` facet-0 pivot chain as the discrete path structure underlying
the Phase-2 door-parity induction, and pins down where the chain STOPS (`base_miss = d`),
which is precisely where the two remaining frontier constructions attach: the terminal
door needs the cross-`miss` partner, and the dual top-facet pivot inverts the interior
steps. Modest structural lemma set, not a breakthrough.

### Frontier UNCHANGED (genuine blocker)
1. Dual top-facet pivot (mirror across facet `Fin.last d`) → prove it inverts the facet-0
   pivot ⟹ `adj` partial involution.
2. Infeasible-regime (`base_miss = d`) cross-`miss` facet-0 partner (the terminal door).
Then assemble `SpernerTriangulation`; Phase-2 door oddness induction on `d`; apply `sperner_ndim`.

### Next steps
1. **(crux)** Dual top-facet pivot construction + involution reciprocity.
2. **(crux)** Cross-`miss` terminal partner for `base_miss = d`.
3. Assemble total `adj`; Phase-2 parity.
