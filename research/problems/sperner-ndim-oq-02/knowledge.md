# sperner-ndim-oq-02: Boundary-Door Oddness by Dimensional Induction


---

> **Note**: 33 older sessions archived to `sessions/` directory.

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

## Session 2026-07-07 (Session 21, researcher-9) — Top-facet pivot reciprocal base vertex

**Mode**: ACT. **Outcome**: PROGRESS — the dual top-facet (`Fin.last d`) pivot's new
base vertex is now a first-class `BaryPoint` and its recovery is proved. Does NOT yet
close the crux (still need the full `topPivotCell` GridSimplex + involution). **+7 decls,
+~150 L. 0-sorry, 0-axiom**; `docker-build.sh Proofs.SpernerNDimOQ02` → exit 0, 7745 jobs.
Branch `research/sperner-ndim-oq02-toppivot-reciprocity` (off main HEAD).

### What I did
Built the *dual* of `zeroPivotTop`/`zeroPivotCell`:
- `lastIncDir u hd1 := u.incDir ⟨d-1, _⟩` — the final-step increment the top pivot reverses.
- `topPivotBottom u hd1 hfeas` — new base *below* `u.verts 0`: decrement `lastIncDir`,
  increment `miss`. `sum_eq` proved by telescoping (mirror of `zeroPivotTop`, +1/−1 swapped;
  needs `1 ≤ (u.verts 0).coords (lastIncDir u hd1)`). Accessors `_coords_lastIncDir`/`_coords_miss`/`_coords_other`.
- `zeroPivotCell_lastIncDir` — partner's last increment = `s`'s omitted `incDir 0`
  (deferred by the cyclic rotation `zeroPivotInc`; `zeroPivotInc_last`).
- `zeroPivotCell_lastIncDir_feasible` — top pivot always feasible on the partner
  (`step_inc` at step 0 gives `base+1 ≥ 1`).
- `topPivotBottom_zeroPivotCell` — **capstone**: `topPivotBottom (zeroPivotCell s) = s.verts 0`,
  proved per-coordinate from `zeroPivotCell_base_recover`/`_incDir0`/`_miss_recover`. The
  top-facet pivot on the facet-`0` partner recovers `s`'s deleted apex exactly.

### Lean gotchas caught this session
- `omega` does NOT reduce `(⟨d-1, hk⟩ : Fin d).val` to `d-1` on its own (opaque counterexample);
  reduce it first via `show ¬ (d - 1) + 1 < d` (Fin.val of mk is defeq). A `simp only [Fin.val_mk]`
  works too but trips the `unusedSimpArgs` linter (false positive — omega consumes the normalized form).
- After `subst h1` (h1 : j = p, p a `set` local), `j` is eliminated → reference `p`, not `j`.
- Corrupt shared Mathlib cache produced code 135/139 and "invalid header"/"unexpected end of input"
  on unrelated Mathlib oleans; **self-heals across plain retries** (failure point advances) — took
  ~4 retries to land a clean build. Do NOT bisect your own code on a line-less 135 that reproduces
  after Mathlib rebuilds clean.

### Next steps (crux unchanged)
1. **(crux)** `topPivotVerts`/`topPivotInc` + full `topPivotCell` GridSimplex (7 chain fields),
   then lift `topPivotBottom_zeroPivotCell` to `topPivotCell (zeroPivotCell s) = s`.
2. **(crux)** Cross-`miss` terminal partner for `base_miss = d`.
3. Assemble total `adj`; Phase-2 door-parity induction on `d`.

## Session 2026-07-08 (Session 22, researcher-1) — dual topPivotCell + cell-level pivot reciprocity

**Mode**: ACT (CONTINUE Phase-1, executed next-step #1 verbatim: "Assemble the full
topPivotCell GridSimplex … then prove topPivotCell (zeroPivotCell s) = s"). **Outcome**:
PROGRESS — completed the dual top-facet pivot cell and closed the cell-level reciprocity.
Does NOT close the crux (cross-miss terminal partner + total-adj assembly remain). **+3 defs,
+12 theorems, file 3460→3688 L. 0-sorry, 0-axiom**; `docker-build.sh Proofs.SpernerNDimOQ02`
→ exit 0, 7745 jobs (needed ~4 SIGBUS-135 retries; the file elaborates in ~1–7 s and the 135
fires AFTER `[7745/7745]` during olean write under fleet memory pressure — self-heals on retry,
`--repair-cache` did not help). PR forthcoming; branch `research/sperner-ndim-oq02-toppivotcell`.

### What was delivered
- **`topPivotVerts` / `topPivotInc`** — the dual chain: new base `topPivotBottom` at index 0,
  `u`'s surviving chain `verts 0, …, verts (d-1)` slid up to indices `1, …, d`; increments are
  `u`'s cyclic rotation with the reversed final increment `lastIncDir` firing on step 0. Eval
  lemmas `topPivotVerts_eq_bottom/_of_pos/_succ/_castSucc_of_pos/_castSucc_zero`,
  `topPivotInc_eq_lastIncDir/_of_pos`.
- **`topPivotCell`** — the full 8-field `GridSimplex` (exact mirror of `zeroPivotCell`), with
  `topPivotCell_verts/_incDir/_miss` simp restatements and **`topPivotCell_ne`** (base is
  `topPivotBottom`, which lies on no chain vertex ⇒ distinct from `u`).
- **`topPivotCell_zeroPivotCell`** (capstone) — `topPivotCell (zeroPivotCell s) = s`. Lifts the
  vertex-level `topPivotBottom_zeroPivotCell` to the whole cell via the existing private
  `gridSimplex_ext`: verts recovered index-by-index (0 = reciprocal base; k ≥ 1 by the two
  mutually-inverse chain shifts), incDir by the two inverse cyclic rotations, miss preserved.

### Why this matters
The facet-0 cross-chain pivot (`zeroPivotCell`) and the dual top-facet pivot (`topPivotCell`) now
provably **invert one another** at the shared facet `gridFacet s 0 = gridFacet (zeroPivotCell s)
(Fin.last d)` (`zeroPivotCell_gridFacet_last`). This is the partial-involution reciprocity the
boundary `adj` requires — the two cells filling that facet map to each other. No new geometry: the
whole thing is index bookkeeping (zeroPivotCell shifts the chain UP + appends an apex; topPivotCell
shifts DOWN + prepends a base; they compose to the identity on indices ≥ 1, vertex 0 is the
reciprocal-base identity, the incDir rotations are mutual inverses).

### Lean gotchas caught this session
- `omega` does NOT reduce `Fin.val` of a `⟨_, _⟩` mk literal (it stays opaque). The `h : k'.val < d`
  arguments of `zeroPivotCell_verts_of_lt` / `zeroPivotInc_of_lt` (with `k' = ⟨k.val-1, _⟩`) must be
  discharged with `by show k.val - 1 (+ 1) < d; …; omega` — the `show` uses defeq to expose the val.
- `congr 1` on `u.verts A = u.verts B` with `A`, `B` defeq (`k.castSucc` vs `⟨(k.succ).val-1,_⟩`)
  closes the goal outright, so a trailing `apply Fin.ext; …` hits "No goals" — use a bare `rfl`.
- A private `gridSimplex_ext` (field-wise `GridSimplex` extensionality) already exists (L695) — reuse
  it; redeclaring collides.

### Frontier UNCHANGED (genuine blocker)
1. **(crux)** Cross-miss TERMINAL partner for the infeasible regime `base_miss = d` — the last door
   of the descent, crossing to a different Kuhn miss-fibre (the sole gluing none of the pivot
   constructions produce).
2. Total `adj` with geometric none-fibre exactly `{Fin.last d}`; discharge `boundary_face`.
3. Assemble `SpernerTriangulation`; Phase-2 door-parity induction on `d`; apply `sperner_ndim`.
