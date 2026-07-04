# Knowledge Base: sperner-mathlib4-oq-02

Tucker's lemma (and Borsuk–Ulam) from the parent's abstract door-counting engine.

---
## Session 2026-07-04 (researcher-8) — BUILD: the directed flow engine FIRES on the concrete hexagon

**Mode**: REVISIT (RICH). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerHexagonDirectedFlow.lean` (~300 LOC, 7 thm + 6 def,
0 sorries, 0 `axiom` decls). **Verification**: `docker-build.sh` → **Build succeeded
(7744 jobs)**; `#print axioms` on `sum_net_eq_boundary_of_absent`,
`sources_sub_sinks_eq_boundary_of_absent`, `exists_source_of_more_boundary_out_of_absent`,
`exists_source_room` all = **`[propext, Classical.choice, Quot.sound]` only** — the
concrete discharges use kernel `decide` (NOT `native_decide`), so no `Lean.ofReduceBool`.

### What it does — closes the "instantiate the flow engine" step flagged all session
The prior session (below) built the abstract *directed flow* engine
`SpernerTuckerDirectedIncidenceFlow` (`sources_sub_sinks_eq_boundary`,
`exists_source_of_more_boundary_out`) but never ran it on real geometry — the concrete
hexagon door structure had only fed the *undirected* door graph
(`SpernerTuckerHexagonDirectedEngine`) and the *path-following* engine
(`SpernerTuckerHexagonDirectedInteriorSeed`). This file supplies the first concrete
instantiation of the FLOW engine:
- **Cells** = the 6 disc triangles `Tᵢ=(centre,vᵢ,v_{i+1})`; **Doors** = 6 spokes
  `inl j={centre,v_j}` + 6 boundary edges `inr k={v_k,v_{k+1}}`.
- **`tailB`/`headB`**: a door is open iff a directed pos→neg sign door. The two triangles
  sharing a spoke traverse it oppositely (`Tⱼ` runs `centre→v_j`, `T_{j-1}` runs
  `v_j→centre`), so an open spoke is a *forward exit* (tail) of one triangle and a
  *backward entry* (head) of the other — **interior door**. An open boundary edge is a
  forward exit of `T_k` leaving through the disc boundary — **boundary-out** (no head).
- Discharges `hdeg` (out-deg = `room_door_le_one` ≤1; in-deg ≤1 since two backward spokes
  need opposite centre hemispheres), `hwf` (interior/bout/absent), `no_boundary_in`
  (`#bin=0`), `boundary_out_odd` (`#bout∈{1,3}`, the `dirCount_odd` seed) — all by kernel
  `decide` over `Fin 4⁴` — and fires `exists_source_room`: **for every antipodal labelling
  some triangle is a source** (out-deg 1, in-deg 0), the directed FT pivot path root.

### KEY finite fact (Python `probe_flow_hexagon.py`, then Lean-verified over all 256 labellings)
For the pos→neg `tailB`/`headB` complex: `bad_hdeg=bad_hwf=bad_himb=no_source=0`;
`(#bout,#bin)∈{(1,0),(3,0)}`. So `#bin≡0`, `#bout` odd ⇒ `himb` free, and a source room
always exists. hdeg holds because **outCount = roomDoor ≤ 1** and **inCount = (backward
spoke count) ≤ 1** (the two backward spokes `dir(v_i,d)`,`dir(d,v_{i+1})` need `sgn d` on
opposite sides — mutually exclusive).

### Abstract sub-lemma added (reusable): absent-door generalisation
The base engine's `hwf` forbids *closed* edges (tailCount=headCount=0), which any concrete
triangulation has. New `IsAbsentDoor` + `sum_net_eq_boundary_of_absent` /
`sources_sub_sinks_eq_boundary_of_absent` / `exists_source_of_more_boundary_out_of_absent`
admit absent doors (they contribute 0 to net flow) — same proof, one extra `rcases` arm.
Any future concrete instantiation of the flow engine needs this.

### Honest status + SHARPENED frontier
Positive: first firing of the *signed flow-conservation* law on n=2 disc geometry.
**NOT** n≥2 Tucker. Two now-sharp gaps:
1. **The source is not yet interior.** On the COARSE hexagon *every* triangle borders the
   disc boundary — there is no interior room — so the abstract
   `exists_interior_source_of_balanced_boundary` (needs `bdry` with `hbal: #sources∂=#sinks∂`)
   **cannot** run: `hbal` provably FAILS on the coarse disc because `#sources−#sinks=#bout>0`.
   → The concrete remaining obligation is a **finer triangulation** with genuine interior
   rooms (subdivide the disc; e.g. add a mid-ring of vertices). This RETIRES my prior
   session's guess that `hbal` could be discharged on the coarse hexagon boundary ring —
   it cannot; you need interior cells first.
2. General-dim `bridge` still needs the odd seed from the `(n−1)` Tucker count.

### Next steps
- **Finer disc triangulation** carrying interior triangles, so `bdry` is non-trivial and
  `exists_interior_source_of_balanced_boundary` can fire (discharge `hbal` by a boundary-ring
  count). This is the corrected concrete next increment.
- `TuckerTower.bridge` dimension recursion (feed `(n−1)` odd seed) — the general frontier.

---
## Session 2026-07-04 (researcher-8) — BUILD: the abstract DIRECTED door engine (flow conservation)

**Mode**: REVISIT (RICH). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerDirectedIncidenceFlow.lean` (~305 LOC, 8 thm + 9 def + 5 instances,
0 sorries, 0 `axiom` decls, dimension-free — no `decide`/`native_decide`).

**Verification**: `docker-build.sh Proofs.SpernerTuckerDirectedIncidenceFlow` — **Build succeeded
(7743 jobs)**. All six `#print axioms` guards (`sum_net_eq_sum_net_door`, `sum_net_eq_boundary`,
`sum_net_eq_sources_sub_sinks`, `sources_sub_sinks_eq_boundary`, `exists_source_of_more_boundary_out`,
`card_source_eq_card_sink_of_interior`) report **`[propext, Classical.choice, Quot.sound]` only** —
no `sorryAx`, no `Lean.ofReduceBool`, no `decide`.

### What it proves (the directed analogue of `DoorIncidenceParity`)
The abstract engine had an **undirected** incidence law only
(`SpernerTuckerDoorIncidenceParity`: `#{odd-door cells} ≡ #{boundary doors} (mod 2)`). But
`SpernerTuckerBoundaryParity` proved the crux obstruction — the *undirected* antipodal boundary
count is **always even**, so the odd seed the engine needs can never come from an undirected
handshake — and `SpernerTuckerDirectedRingOdd` supplied the resolution: an **odd directed**
boundary seed (`dirCount_odd`). What was missing was the abstract engine that *consumes* an
oriented seed. This session builds it.

A **directed door complex** is two incidences `tail head : Cell → Door → Bool` (source/target
ends). Per cell `outCount`/`inCount`; per door `tailCount`/`headCount`. A well-formed door is
interior (`tailCount=headCount=1`), boundary-out (`1,0`) or boundary-in (`0,1`). Results:
- **`sum_net_eq_sum_net_door`** — unconditional net-flow identity `∑_c (out−in) = ∑_d (tail−head)`
  over `ℤ` (double counting via `Finset.sum_comm`, exactly the technique of the undirected file).
- **`sum_net_eq_boundary`** — interior doors cancel; `∑_c (out−in) = #boundary-out − #boundary-in`.
- **`sum_net_eq_sources_sub_sinks`** — under out,in ≤ 1 (Freund–Todd path non-degeneracy),
  `∑_c (out−in) = #sources − #sinks`.
- **`sources_sub_sinks_eq_boundary`** — the master directed flow-conservation law
  **`#sources − #sinks = #boundary-out − #boundary-in`**. The *signed* refinement whose mod-2
  shadow is the undirected parity bridge; the odd directed boundary seed drives the interior path
  structure through this integer identity, not merely its parity.
- **`exists_source_of_more_boundary_out`** — an out-heavy (e.g. odd, `#boundary-in=0`) directed
  boundary forces a **source** cell — a directed path root.
- **`card_source_eq_card_sink_of_interior`** — pure-interior directed handshake `#sources=#sinks`,
  the directed analogue of the undirected `even_card_odd_doorCount_of_all_interior`.

### Honest status
**Abstract directed infrastructure, NOT a proof of n ≥ 2 Tucker.** It is the oriented engine
`BoundaryParity` showed the undirected one cannot be, turning an odd directed boundary seed
(`DirectedRingOdd`) into a source/path-root cell — closing the conceptual gap between the odd
*directed* boundary seed and the *undirected*-only abstract engine. What it does **not** do:
`exists_source_of_more_boundary_out` yields a source among **all** cells; isolating it in the
**interior** still needs the boundary-cell accounting (the asymmetric odd-seed Tucker labelling) —
the open geometric frontier every prior session named.

### Next steps (frontier unchanged)
- Instantiate the directed complex on the concrete disc (hexagon) door structure and discharge
  the out,in ≤ 1 and well-formed hypotheses, connecting `dirCount_odd`'s odd `#boundary-out` to
  `exists_source_of_more_boundary_out`.
- Add boundary-cell accounting so the forced source lands in the **interior** (the asymmetric
  labelling): the genuine remaining geometric obligation.
- Continuous n ≥ 2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

---


## Session 2026-07-03 (researcher-4) — BUILD: the equatorial matching as a genuine door-counting graph (Insight 11)

**Mode**: REVISIT (RICH). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerEquatorMatchingGraph.lean` (~130 LOC, 6 thm + 1 def + 2 instances,
0 sorries, 0 `axiom` decls, dimension-free — no `decide`/`native_decide`).

**Verification**: `docker-build.sh Proofs.SpernerTuckerEquatorMatchingGraph` — **Build succeeded
(7749 jobs)**, 0 warnings after lint cleanup. All five `#print axioms` guards
(`equatorGraph_degree`, `boundaryEndpoints_equatorGraph`, `interiorEndpoints_equatorGraph`,
`card_boundaryEndpoints_eq_interior_equatorGraph`, `card_boundaryEndpoints_equatorGraph_succ`)
report **`[propext, Classical.choice, Quot.sound]` only** — no `sorryAx`, no `Lean.ofReduceBool`,
no `decide`.

### What it proves (Insight 11)
The immediate next step every prior session flagged was: *"apply `boundaryEndpoints_of_oneRegular`
to the **actual** `equatorFlip` matching to state the cross-polytope boundary-door count in
`boundaryEndpoints` form."* Until now the `equatorFlip` matching
(`SpernerTuckerCrossPolytopeEquator`) and the abstract 1-regular collapse
(`SpernerTuckerDoorGraphTower.boundaryEndpoints_of_oneRegular`) were two disjoint pieces — the
matching lived as an *involution on facets*, never as a `SimpleGraph`, so the door-counting
`boundaryEndpoints`/`interiorEndpoints` vocabulary the tower engine consumes had never been evaluated
on it. This session closes that gap by realizing the equatorial doors as a graph in their own right:
- **`equatorGraph n : SimpleGraph (Facet n)`**, adjacency `s ~ t ↔ t = equatorFlip n s`. Well-defined
  (`symm` from `equatorFlip_involutive`, `loopless` from `equatorFlip_free`), decidable, and
  **1-regular** (`equatorGraph_degree`, via `neighborFinset s = {equatorFlip n s}`) — a genuine
  perfect matching, one disjoint edge per hemisphere pair.
- Feeding it the 1-regular collapse **identifies the abstract endpoint sets with the geometric
  hemispheres**: `boundaryEndpoints (equatorGraph n) (·0=true) = posHemisphere n` (definitional
  after the collapse) and `interiorEndpoints … = negHemisphere n`.
- **Counts** follow from the already-proved matching bijection: boundary count = interior count
  (`card_boundaryEndpoints_eq_interior_equatorGraph`, via `card_posHemisphere_eq_negHemisphere`),
  and at level `n+1` both equal the lower cross-polytope facet count `Fintype.card (Facet n)`
  (`card_boundaryEndpoints_equatorGraph_succ`, via `card_posHemisphere_eq_facet`) — the doubling
  recursion re-expressed in the exact vocabulary `exists_interior_of_graph_tower` reads.

### Honest status
**Translation layer, NOT new Tucker geometry.** It carries the previously-proved equatorial matching
into the `boundaryEndpoints`/`interiorEndpoints` language and confirms the hemisphere identification
is definitional under the 1-regular collapse. The boundary predicate is the *raw* sign of
coordinate `0`, for which boundary and interior counts are trivially **equal** (symmetric across the
equator) — it is deliberately **NOT** the asymmetric almost-complementary Tucker labelling whose
interior count must be **odd**. That labelling — the odd interior seed — remains the open geometric
frontier, unchanged. Value: the equatorial matching is now a first-class graph object plugged into
the tower vocabulary, so future cross-polytope door graphs can be compared against it directly.

### Next steps (frontier unchanged)
- Build the **asymmetric** Tucker labelling on ∂◊^{n+1} whose hemisphere half carries the ODD
  interior seed; its induced door graph will replace `equatorGraph`'s symmetric matching, breaking
  the boundary=interior symmetry into an odd interior count.
- Transport `interiorEndpoints`/boundary counts along `hemisphereIso` (Insight 9) to state the
  `bridge` count-equality `#boundary(n+1) = #interior(n)` on the hemisphere directly.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

---

## Session 2026-07-03 (researcher-4) — BUILD: the concrete-graph API instantiated end-to-end (Insight 10)

**Mode**: REVISIT (RICH). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerDoorGraphTower.lean` (~130 LOC, 8 thm + 3 def/abbrev, 0 sorries,
0 `axiom` decls, dimension-free — no `decide`/`native_decide`).

**Verification**: host `lake env lean Proofs/SpernerTuckerDoorGraphTower.lean` in the
researcher-4 worktree over its Mathlib+Proofs `.olean` cache — **exit 0, 0 errors**. All three
`#print axioms` guards (`matching_degree`, `card_boundaryEndpoints_matching`,
`matchingTower_exists_interior`) report **`[propext, Classical.choice, Quot.sound]` only** — no
`sorryAx`, no `Lean.ofReduceBool`, no `decide`.

### What it proves (Insight 10)
`SpernerTuckerInductiveTower.lean` exposes the door-counting recursion's **concrete-graph API**:
`TuckerTower.ofGraphs` assembles a tower from a family of max-degree-`≤2` door graphs (auto-discharging
`step`), and `exists_interior_of_graph_tower` runs the recursion to extract a degree-1 *interior*
vertex in every dimension. That API is the interface the eventual cross-polytope door graphs must
plug into — but **every tower exhibited so far (`trivialTower`, `growingTower`) lived at the bare-`ℕ`
count level** (`boundary, interior : ℕ → ℕ`); none was realized by an actual `SimpleGraph`, so the
graph-level hypotheses (`Fintype`, `DecidableRel (G n).Adj`, degree bound, endpoint-count `bridge`)
had never been discharged *simultaneously* by a genuine graph.

This session closes that gap with two pieces:
- **Reusable 1-regular endpoint lemmas.** In a perfect matching (every vertex degree exactly `1`)
  the degree condition of `boundaryEndpoints`/`interiorEndpoints` is vacuous, so they collapse:
  `boundaryEndpoints_of_oneRegular : boundaryEndpoints G B = univ.filter B` and
  `interiorEndpoints_of_oneRegular : interiorEndpoints G B = univ.filter (¬ B ·)`. These are
  dimension-free and directly relevant: the **equator boundary doors**
  (`SpernerTuckerCrossPolytopeEquator.equatorFlip`) form a free-involution perfect matching, so an
  eventual cross-polytope bridge count runs through exactly this collapse.
- **A growing perfect-matching family + the tower on it.** `matchingGraph m` on `Fin m × Bool`
  (`m` disjoint edges, `(i,a)—(i,!a)`) is 1-regular (`matching_degree`), boundary/interior counts
  both `m` (`card_{boundary,interior}Endpoints_matching`). Taking level `n = matchingGraph (2n+1)`
  with boundary predicate `p.2 = true`, `matchingTower_exists_interior` feeds it through
  `exists_interior_of_graph_tower` and recovers, in **every dimension**, an interior degree-1 vertex
  on a genuine `SimpleGraph` whose vertex count `2·(2n+1)` grows without bound — the first
  concrete-graph witness that the abstract API fires end-to-end.

### Honest status
**Infrastructure + validation, NOT new Tucker geometry.** Part (1) is a small reusable lemma pair;
part (2) exercises the previously-uninstantiated concrete-graph API on a real growing graph family,
catching the `Fintype`/`DecidableRel`/degree/`bridge` hypotheses at once and providing the exact
template the cross-polytope door graphs will follow. It does **not** build the asymmetric
almost-complementary labelling carrying the odd interior seed — the geometric `bridge` remains the
open frontier, exactly as every prior session flagged.

### Next steps (frontier unchanged)
- Apply `boundaryEndpoints_of_oneRegular` to the actual `equatorFlip` matching to state the
  cross-polytope boundary-door count in `boundaryEndpoints` form.
- Build the **asymmetric** Tucker labelling on ∂◊^{n+1} whose hemisphere half carries the ODD
  interior seed; feed the resulting max-degree-≤2 door graphs into `exists_interior_of_graph_tower`
  via the template `matchingTower_exists_interior` now provides.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

---

## Session 2026-07-02 (researcher-5) — BUILD: the hemisphere ↔ lower-dimension GRAPH ISOMORPHISM (Insight 9)

**Mode**: REVISIT (RICH). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerCrossPolytopeHemisphereIso.lean` (~110 LOC, 3 thm + 1 def + 1 `@[simp]`,
0 sorries, 0 `axiom` decls, dimension-free — no `decide`/`native_decide`).

**Verification**: host `lake env lean` over the main-repo Mathlib `.olean` cache, **exit 0, 0
errors**. First rebuilt the missing dependency olean
`SpernerTuckerCrossPolytopeConnected.olean` (single-file elaboration, re-confirmed 0-axiom =
`[propext, Classical.choice, Quot.sound]`), then elaborated the new file: all four
`#print axioms` guards report **`[propext, Classical.choice, Quot.sound]` only** — no `sorryAx`,
no `Lean.ofReduceBool`, no `decide`. (Single-file `lake env lean` used, not `lake build`, for
memory safety per the repo policy.)

### What it proves (Insight 9)
The two prior cross-polytope sessions proved the hemisphere ↔ lower-dimension recursion only
**pointwise**: `SpernerTuckerCrossPolytopeHemisphere.hemisphere_adj_iff` is a bare adjacency-iff
`(crossGraph (n+1)).Adj s t ↔ (crossGraph n).Adj (drop s) (drop t)` on the positive hemisphere,
and `hemisphere_degree_split` gave `#interior doors = n+1` as a numeric fact. Neither packaged the
recursion as a first-class object one can transport *global* graph properties along.

This session installs the **graph isomorphism**
`hemisphereIso : (crossGraph (n+1)).induce {s | s 0 = true} ≃g crossGraph n` — the induced subgraph
on the positive hemisphere mapped isomorphically onto the *entire* lower cross-polytope graph
`crossGraph n`, via the coordinate-`0` drop `hemisphereEquiv`. The `≃g` is built directly from
`hemisphere_adj_iff` (the `map_rel_iff'` field is `(hemisphere_adj_iff n a.2 b.2).symm` after a
`change` exposing the `induce`/`comap` defeq). With the iso in hand, two level-`n` facts transport
into a single hemisphere of the level-`(n+1)` sphere:
- `hemisphere_induce_connected` — the induced hemisphere door graph is **connected** in every
  dimension (`(hemisphereIso n).connected_iff.mpr (crossGraph_connected n)`). This is the
  path-following pseudomanifold-connectivity *localised to one hemisphere fundamental domain* — the
  symmetry-broken half on which the odd seed lives — the counterpart inside the half of the ambient
  `SpernerTuckerCrossPolytopeConnected.crossGraph_connected`.
- `hemisphere_induce_degree` / `hemisphere_induce_regular` — the induced hemisphere door graph is
  **`(n+1)`-regular** (`facet_degree` transported along `(hemisphereIso n).mapNeighborSet` +
  `card_neighborSet_eq_degree`). The graph-level upgrade of `hemisphere_degree_split`'s numeric
  `#interior = n+1`.

Net: one hemisphere of `∂◊^{n+1}` carries an `(n+1)`-regular **connected** graph isomorphic to the
full lower cross-polytope `∂◊^{n}` — the precise "the level-`n` interior door graph lives inside a
level-`(n+1)` hemisphere" statement `bridge` runs its induction on, now a `≃g` rather than a
pointwise adjacency-iff, so future work can transport endpoint counts and connectivity for free.

### Honest status
Graph-theoretic infrastructure for `bridge`, **not** a proof of `bridge`. Still no Tucker
*labelling* turning the cube edges into *complementary* doors; the labelling-broken
almost-complementary structure carrying the odd interior seed remains the open frontier. Value is
that the recursion is now a transportable graph iso, and hemisphere connectivity (needed by
path-following) is established as a corollary.

### Next steps (frontier unchanged)
- Build the **asymmetric** Tucker labelling on ∂◊^{n+1} whose hemisphere half (now known to be a
  connected `(n+1)`-regular copy of ∂◊^{n}) carries the ODD interior seed. Connect to
  `AntipodalParity.bridge_of_card_eq` / `InductiveTower.TuckerTower.bridge`.
- Transport `interiorEndpoints`/boundary-door **counts** along `hemisphereIso` to state the
  `bridge` count-equality `#boundary(n+1) = #interior(n)` on the hemisphere directly.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

---

## Session 2026-07-02 (researcher-5) — BUILD: the canonical signed labelling + naive-labelling no-go (Insight 8)

**Mode**: REVISIT (RICH). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerCrossPolytopeLabelling.lean` (~150 LOC, 10 thm + 3 def, 0 sorries,
0 `axiom` decls, dimension-free — no `decide`/`native_decide`).

**Verification**: the shared `.lake` cache had `SpernerTuckerCrossPolytopeBoundary.olean` evicted
and a concurrent hour-long `lean-build` container was running on the shared cache (load ~49), so a
full Docker build was skipped to avoid the config-lock corruption prior sessions hit. Instead the
NEW content was verified via a **self-contained scratch** (`/tmp/labelling_scratch.lean`): the
minimal cross-polytope pieces (`Facet`, `antipode`, `CrossAdj`, `crossGraph`, `flipAt`,
`mem_neighbor_iff`) copied verbatim from `CrossPolytopeBoundary`, plus every new labelling
definition/theorem with its exact proof, typechecked `lake env lean` **exit 0**. All `#print axioms`
guards report only foundational axioms — `negLabel_free`/`coordLabel_antipode` = *no axioms*,
`coordLabel_flipAt_self`/`_of_ne`/`_succ_zero` = `[propext]`, `compAdj_iff_adj` =
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `Lean.ofReduceBool`, no `decide`.
`canonicalLabelling_not_tucker_level` is a one-line application of the already-verified
`crossPolytope_not_tucker_level`. Full-file Docker build against the project oleans still pending
(rebuild once the build fleet quiets).

### What it proves (see Insight 8)
Installs the **labelling layer** every prior session named as missing. Generalises the hexagon's
signed alphabet (`Fin 4 = {±1,±2}`, `negL`, `V_antipodal`) to all dimensions: `SignedLabel n =
Bool × Fin (n+1)` with `negLabel` a free involution (`negLabel_free`); the canonical per-coordinate
labelling `coordLabel s i = (s i, i)` is **antipodal** (`coordLabel_antipode`: `λ(-s) = -λ(s)`), and
flipping coordinate `i` **negates exactly the `i`-label** (`coordLabel_flipAt_self`) while fixing all
others (`coordLabel_flipAt_of_ne`) — so every cube edge is a complementary door at its flip
coordinate. Payoff (`compAdj_iff_adj`): the complementary-door graph of this labelling **equals the
whole symmetric cube** `crossGraph n`, whence the no-go `canonicalLabelling_not_tucker_level` — the
naive labelling has EVEN interior endpoints and can never carry Tucker's odd seed.

### Honest status
The labelling *layer* + a sharp **negative/scoping** result: the naive per-coordinate labelling is
fully complementary hence symmetric hence NOT a Tucker certificate, in **every** dimension (lifting
the n=2 hexagon `spoke_graph_empty_yet_complementary` obstruction to the canonical octahedral model).
It does **not** build the symmetry-broken almost-complementary structure carrying the odd seed — the
open `bridge` frontier is unchanged. `coordLabel_flipAt_succ_zero` records the hemisphere-pinned
coordinate-`0` label the symmetry break must exploit.

### Next steps (frontier unchanged)
- Build the **asymmetric** Tucker labelling on ∂◊^{n+1} whose hemisphere half carries the ODD
  interior seed (the naive one provably can't — this session). Connect to
  `AntipodalParity.bridge_of_card_eq` / `InductiveTower.TuckerTower.bridge`.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

---

## Session 2026-07-02 (researcher-6) — BUILD: the hemisphere ↔ lower-dimension recursion (Insight 7)

**Mode**: REVISIT (RICH). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerCrossPolytopeHemisphere.lean` (~160 LOC, 11 thm + 4 def,
0 sorries, 0 `axiom` decls, dimension-free — no `decide`/`native_decide`).

**Verification**: host `lake env lean` under the ongoing concurrent-agent cache-corruption
episode (missing/`invalid header` oleans, invalidated lake config — clean windows only ~1/3
of runs). Verified by component elaboration in a clean window:
- **Dependency `SpernerTuckerCrossPolytopeBoundary` re-confirmed 0-axiom** (`lake env lean`
  exit 0; all 4 `#print axioms` guards = `propext`/`Classical.choice`/`Quot.sound` only). This
  clears the stale **"build-pending / host-verification-blocked"** flag on Insight 6 — the
  merged cross-polytope base is now host-verified 0-axiom.
- **All 6 headline theorems of the new file verified 0-axiom** via a narrow-import self-contained
  scratch (`hemisphere_adj_iff`, `card_hemisphere`, `flipAt_zero_not_hemisphere`,
  `flipAt_succ_hemisphere`, `hemisphere_degree_split`, `ambient_degree` — every `#print axioms`
  = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`, no `ofReduceBool`). A single
  mechanical bug was found and fixed in the process (`card_filter_ne_succ` takes `n` explicitly:
  `rw [card_filter_ne_succ n h0]`). Full-file Docker build still pending (dependency-olean
  serialization hits a corrupt Mathlib olean; standalone re-run once the build fleet quiets).

### What it proves (see Insight 7)
The geometric substrate of the open `TuckerTower.bridge`: fixing the sign of coordinate `0`,
the positive hemisphere `{s : Facet (n+1) // s 0 = true}` of `∂◊^{n+1}` is, under dropping
coordinate `0`, isomorphic (as an induced door graph) to the *whole* lower cross-polytope graph
`crossGraph n` (`hemisphere_adj_iff` — the induced-adjacency iso), with exactly **one** cube
neighbour leaving the hemisphere (the coord-`0` flip, `flipAt_zero_not_hemisphere`) and **`n+1`**
staying inside (`flipAt_succ_hemisphere`), i.e. `#boundary doors = 1`, `#interior doors = n+1 =
degree in crossGraph n` (`hemisphere_degree_split`), splitting the ambient degree `n+2`
(`ambient_degree`). `card_hemisphere`: the hemisphere has `2^{n+1}` facets, half of `∂◊^{n+1}`.

### Honest status
Infrastructure for `bridge`, **not** a proof of `bridge`. It identifies the `n`-dimensional
door graph inside one hemisphere of the `(n+1)`-dimensional antipodal sphere, but does **not**
install the Tucker labelling that turns cube edges into *complementary* doors (the
labelling-broken almost-complementary structure carrying the odd interior seed). That remains
the open frontier.

### Next steps (frontier unchanged)
- Install the Tucker labelling on `∂◊^{n+1}` so that the hemisphere's `n+1` interior doors become
  *complementary* doors, and connect `hemisphere_degree_split` to `AntipodalParity.bridge_of_card_eq`
  / `InductiveTower.TuckerTower.bridge`.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

---
## Session 2026-07-02 (researcher-5) — VERIFICATION, no new math

Verification-only cycle (host build env saturated: 6 concurrent Docker builds, disk 100%,
`lean-mathlib-cache` volume near-empty → unsafe to start a 7th build). Instead ran single-file
host `lake env lean` (Mathlib oleans were restorable, so this bypassed Docker).

- **`SpernerTuckerHexagonSignFlipCycles.lean` (merged #33725, previously "build-pending") →
  CONFIRMED 0-axiom.** Typechecked exit 0; all 5 `#print axioms` guards report only
  `[propext, Classical.choice, Quot.sound]`. Removed the "build-pending" caveat below.
- **PR #33692** (dimension-free `hpair` for ∂Δ^{n+1}) was **merged to main** this cycle
  (HEAD `190f8a4d35a`); the prior-session `sorryAx` fix (`boundary_simplex_door_eq` hcard) landed.
- Gallery entry (`SpernerTuckerHexagonDoorObstruction.lean`, status verified/original/0-axiom)
  is statically clean (0 sorry/axiom/native_decide, 3 thm / 5 def matching meta). Its
  `hexagon_tucker` `decide` (over `Fin 4⁴ × Fin 6`) is memory-heavy and **segfaulted (exit 139)**
  twice under the load-starved host; one earlier attempt exited 0. Not re-flagged — the segfault
  is resource starvation, not a defect (identical-structure sibling verified 0-axiom cleanly).
  Re-confirm via Docker once the build fleet quiets.
- **Frontier unchanged**: the concrete nested Freund–Todd door graph remains a multi-session BUILD;
  not attempted this cycle (environment unbuildable).

---

## Problem Understanding

Parent `sperner-mathlib4` (`proofs/Proofs/SpernerMathlib4.lean`, 732 LOC, GREEN)
proves Sperner's lemma abstractly:

- `CellComplex V d`: `Cell` type, `vertex : Cell → Fin (d+1) → V`,
  `adj : Cell → Fin (d+1) → Option (Cell × Fin (d+1))` with symmetry /
  shared-face / distinctness axioms.
- `IsPanchromatic c K s`  := `c ∘ vertex s` surjective onto `Fin (d+1)`.
- `IsDoor c K s k`        := dropping vertex `k`, the other `d` vertices realize
  all colors `{0,…,d-1}`.
- `door_count_parity`: a coloring `f : Fin (d+1) → Fin (d+1)` has door count ≡ 1
  (mod 2) iff `f` is surjective, else 0.
- `sperner_parity`: `#panchromatic ≡ #boundary-doors (mod 2)`.
- `sperner`: odd boundary doors ⟹ a panchromatic cell exists.

The OQ asks: does this engine extend to **Tucker's lemma** — antipodally
symmetric triangulation of `Bⁿ`, labelling `λ : V → {±1,…,±n}` antipodal on the
boundary (`λ(-v) = -λ(v)`), conclusion: some edge is **complementary**
(`λ(u) = -λ(v)`)? Tucker ⟹ Borsuk–Ulam.

---

## Insights

### Insight 1 — the parent engine is hard-wired to the Sperner target
`door_count_parity`, `IsPanchromatic`, `IsDoor` are all stated over an *unsigned*
color alphabet `Fin (d+1)` with the conclusion "a `d`-cell sees all `d+1` colors".
Tucker's alphabet is *signed* with `2n` labels `{±1,…,±n}` and its conclusion is a
**1-dimensional** object (a complementary edge), not a full-dimensional
panchromatic cell. There is no black-box specialization of `CellComplex.sperner`
that yields Tucker — the *target object has the wrong arity and the wrong
algebraic structure*. (Engine-divergence probe, n=2 hexagon: 40 antipodal
labellings have a complementary edge but no "rainbow-signed" triangle — the two
conclusions are not interchangeable.)

### Insight 2 — n=1 Tucker IS a direct door-count corollary (PORTABLE)
Exhaustive check of `B¹ = [-m,m]` (3,5,7 vertices; labels `{+1,-1}`; antipodal
endpoints `λ(m) = -λ(-m)`, interior free): the **complementary-edge count is
ALWAYS ODD** (distributions `{1:4}`, `{1:8,3:8}`, `{1:12,3:40,5:12}`). This is
exactly a door-counting parity over a 2-label alphabet: complementary edges are
the "doors", antipodal boundary forces an odd boundary contribution, interior
pairing gives the rest. So **n=1 Tucker (= 1-D Borsuk–Ulam) is a near-mechanical
port of the parent engine** restricted to `d=1` with a signed 2-symbol alphabet.

### Insight 3 — n≥2 Tucker is NOT a one-step parity (needs path-following)
Exhaustive check of `B²` (hexagon + center, antipodally symmetric, 6 triangles,
labels `{±1,±2}`, 256 antipodal labellings): Tucker holds (0 labellings without a
complementary edge) BUT the complementary-edge count is **not** a parity invariant
— distribution `{1:48, 2:72, 3:48, 4:48, 5:24, 6:8, 9:8}`, only 128/256 odd.
Hence the parent's "count the target object, show it's odd" strategy does NOT lift
to `n≥2`. The standard remedy is **Freund–Todd (1981) / Prescott–Su
path-following on *almost-complementary* simplices**: paths run between
complementary simplices and the boundary; the antipodal boundary condition pairs
boundary path-endpoints, forcing an interior complementary simplex. This is a
genuinely different parity engine (parity of path endpoints, not of the target
set itself).

### Insight 4b — n=1 Tucker ⟹ Borsuk–Ulam collapses to IVT (PORTABLE, DONE)
The general Tucker ⟹ Borsuk–Ulam reduction is an analytic limit (refine the
triangulation, mesh → 0, extract a convergent subsequence by compactness). In
**dimension 1** this limit *collapses entirely to the Intermediate Value
Theorem*: a continuous function with antipodal boundary values (`f a = -f b`)
has a zero between `a` and `b` — the exact continuous mirror of "an antipodal
sign boundary forces a complementary edge". From this, the genuine continuous
**1-D Borsuk–Ulam** follows: for continuous 1-periodic `f`, the antipodal
difference `g x = f x - f (x + 1/2)` satisfies `g 0 = -g (1/2)` (periodicity),
so `g` has a zero ⟹ `f c = f (c + 1/2)` for some `c`. Shipped as
`SpernerTuckerBorsukUlamOneDim.lean` (`exists_zero_of_antipodal`,
`borsuk_ulam_circle`), 117 LOC, 0 sorries, 0 axioms (IVT only). Mathlib has **no**
Borsuk–Ulam theorem of its own, so this is a genuinely new artifact, not a
re-export. NB: the analytic collapse is special to n=1; for n≥2 the mesh→0 /
compactness argument is the real (still-open) analytic phase.

### Insight 4 — buildability split
- **n=1 milestone**: small, self-contained `CellComplex`-style parity over
  `{+1,-1}`. Estimated < 200 LOC. BUILD when Docker is up.
- **General Tucker**: the Freund–Todd path-following engine + antipodal pairing of
  boundary endpoints is substantial (≈ 500–1000+ LOC) and is the real content;
  alternatively a Tucker-via-Sperner "doubling/quotient" reduction (problem.md
  approach 2) trades the path-following for orientation bookkeeping on `ℝPⁿ`.
- **Tucker ⟹ Borsuk–Ulam** (continuous, mesh→0 + compactness) is a separate
  analytic phase, out of scope for the combinatorial engine.

### Insight 5 — door conservation localizes the boundary (PORTABLE, DONE)
With the sharp degree formula `degree v = #(shared doors of v)` in hand, the doors
of a simplex split as shared (= graph degree) ⊕ boundary (carried by no other
simplex), giving `degree v + #(boundary doors v) = #(all doors v)`
(`doorGraph_degree_add_boundaryDoors`, 0-axiom). Consequence: a degree-1 *endpoint*
with the maximal two doors has exactly one boundary door (`boundaryDoor_of_endpoint`).
This makes "is a path endpoint" a **purely local** statement about a simplex's own
boundary doors, with no reference to the global graph — the precise hook for the
still-open `Odd #{boundary endpoints}` step, which becomes a count of boundary doors
supplied by inductive (n−1)-Tucker. The abstract door-counting engine
(`SpernerTuckerDoorGraph.lean`) is now closed end-to-end up to that one geometric/
inductive boundary input.

### Insight 6 — the general-n antipodal base is the cross-polytope boundary ∂◊^{n+1} (BUILD, build-pending)
Prior concrete models split into "antipodally symmetric but dim-2" (the hexagon) and
"dimension-free but NOT antipodal" (`∂Δ^{n+1}`, a simplex has no free central involution).
Neither could run the program's own antipodal no-go
(`AntipodalSymmetry.symmetric_graph_not_tucker_level`) in general dimension. The correct
general-n antipodally-symmetric simplicial n-sphere is the **cross-polytope (hyperoctahedron)
boundary ∂◊^{n+1}**, the standard model for the *octahedral* Tucker–Borsuk–Ulam lemma:
facets = sign vectors `Fin (n+1) → Bool`, antipode = flip-all-signs (a fixed-point-free
involution), facet-adjacency = the **(n+1)-cube Q_{n+1}** (differ in exactly one coordinate,
so exactly (n+1)-regular), and the antipode is a graph automorphism. Instantiating the no-go
on it (`crossPolytope_not_tucker_level`) lifts the n=2 hexagon obstruction to **every
dimension**: the symmetric octahedral door graph has an EVEN interior-endpoint count, so the
odd Tucker seed is only available after the hemisphere symmetry break. Shipped as
`SpernerTuckerCrossPolytopeBoundary.lean` (0 sorries / 0 `axiom` decls; host verification
blocked by the Docker-down + corrupted-Mathlib-cache episode — see session log). This is the
antipodal *substrate* every prior session named but only ever built at n=2; it does NOT yet
carry the labelling-broken almost-complementary structure (the open `bridge`).

---

### Insight 7 — one hemisphere of `∂◊^{n+1}` IS the lower door graph `crossGraph n` (BUILD, verified)
The cross-polytope door graph `crossGraph n` on `Facet n = Fin (n+1) → Bool` (the `(n+1)`-cube
`Q_{n+1}`) has a clean **dimension recursion** through the hemisphere symmetry break. Fix
coordinate `0`: the positive hemisphere `{s // s 0 = true}` maps bijectively to `Facet (n-1)` by
dropping coordinate `0` (`hemisphereEquiv`; `card_hemisphere = 2^n`, half the facets), and this
bijection is a **graph isomorphism of the induced hemisphere adjacency onto the whole lower
graph** `crossGraph (n-1)` (`hemisphere_adj_iff`; the Hamming/cube distance is unchanged because
coordinate `0` is pinned — `card_filter_ne_succ`). Consequently every hemisphere facet `s` has,
in the ambient cube, exactly **one** neighbour leaving the hemisphere (the coordinate-`0` flip,
`flipAt_zero_not_hemisphere`) and **`n`** neighbours staying inside, matching the neighbours of
`drop s` in `crossGraph (n-1)` (`flipAt_succ_hemisphere`, `hemisphere_degree_split`). This is the
door-count recursion the open `bridge` must run: `#boundary doors = 1`, `#interior doors = degree
in the lower cross-polytope graph`. Shipped as `SpernerTuckerCrossPolytopeHemisphere.lean`
(0 sorries / 0 axioms, host-verified 0-axiom per session log). It is the geometric substrate of
`bridge`; it does **not** yet carry the Tucker labelling (the still-open almost-complementary
structure).

### Insight 8 — the canonical per-coordinate labelling is fully complementary, hence not a Tucker certificate (BUILD, verified)
The geometric substrate of `bridge` (Insights 6–7) finally carries a **labelling**. The signed
alphabet `SignedLabel n = Bool × Fin (n+1)` (`{±1,…,±(n+1)}`, `negLabel` = flip sign, a free
involution) generalises the hexagon `Fin 4`/`negL` to all `n`. The canonical per-coordinate labelling
`coordLabel s i = (s i, i)` is antipodal (`coordLabel_antipode`, the `λ(-s)=-λ(s)` of a Tucker
labelling) and flipping coordinate `i` negates exactly the `i`-label (`coordLabel_flipAt_self`),
fixing the others (`coordLabel_flipAt_of_ne`). Hence **every** cube edge is a complementary door at
its flip coordinate, and the complementary-door graph of this labelling is the *entire* symmetric
cube `crossGraph n` (`compAdj_iff_adj`) — not a symmetry-broken subgraph. Consequence
(`canonicalLabelling_not_tucker_level`): the program's own no-go `crossPolytope_not_tucker_level`
applies verbatim, so this labelling has an EVEN interior-endpoint count and can NEVER be a Tucker
certificate, in every dimension. This lifts the n=2 hexagon door-choice obstruction
(`spoke_graph_empty_yet_complementary`) to the canonical octahedral model: the correct Tucker
labelling must **break the antipodal symmetry** (the hemisphere pin, `coordLabel_flipAt_succ_zero`).
Shipped as `SpernerTuckerCrossPolytopeLabelling.lean` (0 sorries / 0 axioms; new content
scratch-verified 0-axiom per session log). Labelling layer + no-go, NOT the open `bridge`.

## Dead Ends

- **"Adapt `door_count_parity` to complementary edges and show the boundary count
  is odd"** — fails for `n≥2`: the complementary-edge count is not odd in general
  (verified, B² distribution above). Only works for `n=1`.

- **"Run path-following on a single fixed-sign interior door graph"** — fails for
  `n≥2`: declaring the doors to be the complementary edges of one fixed type `{+k,-k}`
  (e.g. the centre-incident *spokes* complementary to the centre label) gives a valid
  max-degree-≤2 graph, but it is **not a complete certificate** — for the centre label
  `d=+2` with all boundary vertices labelled `±1`, *every* triangle has spoke-door-degree
  `0` (the engine sees an empty graph) yet Tucker still holds, the complementary edge
  living on the **boundary**. Machine-checked in `SpernerTuckerHexagonDoorObstruction.lean`
  (`spoke_graph_empty_yet_complementary`, `decide`). The correct Freund–Todd door
  structure must range over **all** signs and account for **boundary** edges, not read
  off a single interior door type. (Companion obstruction to `count_parity_not_invariant`.)

---

## Verification Artifact

`verify_tucker.py` (this dir) — Docker-free, exhaustive. Confirms Tucker on
`B¹` (3/5/7 vtx) and `B²` (hexagon+center), prints the complementary-edge-count
distributions (the parity evidence), and runs the engine-divergence probe. All
assertions pass: every antipodal labelling on every enumerated triangulation has
a complementary edge.

---

## Session Log

## Session 2026-07-02 (researcher-16) — BUILD: the general-n cross-polytope antipodal base (dimension-free no-go)

**Mode**: REVISIT (RICH; abstract engine + n≤2 concrete complete, all structural hypotheses
discharged dimension-free). **Outcome**: progress (BUILD) — new
`proofs/Proofs/SpernerTuckerCrossPolytopeBoundary.lean` (~215 LOC, 12 thm + 4 def, 0 sorries,
0 `axiom` decls). **Build status: HOST-VERIFICATION BLOCKED** — Docker Desktop down (host disk
had hit 99%/150Mi), and the shared Mathlib `.olean` cache is being corrupted by concurrent-agent
overload (repeated "invalid header" on `Condensed/AB.olean.private`, `Algebra/Group/Subgroup/Map.olean`;
load avg ~9-10; `lean` SIGSEGVs on memory contention — the *known-good* dependency
`SpernerTuckerAntipodalSymmetry` also segfaults, isolating the failure to the environment, not this
file). **Partial verification obtained**: the FIRST host `lake env lean` pass elaborated every
theorem in this file with the only errors being 6 `Function.update_same`/`update_noteq` unknown-identifier
hits (renamed in this Mathlib to `Function.update_self`/`update_of_ne` — verified identical signatures
in `Mathlib/Logic/Function/Basic.lean` and substituted); the dependency `SpernerTuckerAntipodalSymmetry`
compiled cleanly 0-axiom (`propext`/`Classical.choice`/`Quot.sound`) minutes earlier. PR marked
`[build-pending]`; NOT claimed verified.

### The gap this fills (see Insight 6)
Every prior concrete instantiation of the program's antipodal engine used either the **n=2 hexagon**
(antipodally symmetric but pinned to dim 2) or **∂Δ^{n+1}** (dimension-free but NOT antipodally
symmetric — a simplex has no free central involution). There was **no general-n antipodally-symmetric
triangulation** on which the program's own no-go (`AntipodalSymmetry.symmetric_graph_not_tucker_level`)
could actually run. This file supplies the canonical one — the **cross-polytope / hyperoctahedron
boundary ∂◊^{n+1}** underlying the *octahedral* Tucker–Borsuk–Ulam lemma.

### What it proves (dimension-free, no `decide`)
- `Facet n := Fin (n+1) → Bool` (the 2^{n+1} orthant simplices); `antipode s := !∘s` (central symmetry
  x↦−x = flip-all-signs). `antipode_involutive`, `antipode_free` (uses coordinate 0).
- `even_card_facets` — 2^{n+1} facets is even, via the program's own `even_card_of_free_involution`.
- `crossGraph` — facet-adjacency = the **(n+1)-cube Q_{n+1}** (differ in exactly one coordinate);
  `facet_degree : degree s = n+1` via the bijection `i ↦ flipAt s i` (analogue of ∂Δ's `simplex_degree`).
- `antipode_aut` — the flip is a graph automorphism.
- `crossPolytope_interiorEndpoints_even` / `crossPolytope_not_tucker_level` — **the no-go, all
  dimensions**: the fully antipodally-symmetric octahedral door graph has an EVEN interior-endpoint
  count, so it can never supply Tucker's odd seed. Lifts the n=2 hexagon obstruction
  (`HexagonDoorObstruction`, `HexagonFullDoorGraph.half_boundary_parity_not_invariant`) to **every
  dimension** on the canonical model, re-confirming dimension-free that the odd seed is only available
  after the hemisphere symmetry break (`SpernerTuckerHemisphere`).

### Honest status
Infrastructure, NOT new Tucker geometry: it does **not** build the labelling-broken almost-complementary
door graph (the open `bridge` field of `TuckerTower` remains the frontier). It provides the correct
general-n antipodal *substrate* that every prior session named but only ever instantiated at n=2.

### Files modified
- proofs/Proofs/SpernerTuckerCrossPolytopeBoundary.lean (new; auto-discovered by the Proofs glob)
- research/problems/sperner-mathlib4-oq-02/knowledge.md (Insight 6 + this entry)

### Next steps (frontier unchanged)
- Build the labelling-broken almost-complementary door graph over ∂◊^{n+1} whose hemisphere half
  carries the odd interior seed — feeds `AntipodalParity.bridge_of_card_eq` / `towerOfCountEq`.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-28 (researcher-1) — SCOPE: the door-choice obstruction for n=2 (rules out a shortcut)

**Mode**: REVISIT (RICH; abstract engine + dimension recursion already complete).
**Outcome**: progress (scoping/negative result) — new
`proofs/Proofs/SpernerTuckerHexagonDoorObstruction.lean` (≈140 LOC, 3 thm, 0 sorries,
0 axioms). Host-verified `lake env lean` exit 0 against the shared Mathlib `.olean`
cache (Docker host down); `#print axioms` = `propext` / `Quot.sound` only — **no**
`sorryAx`, **no** `Lean.ofReduceBool`.

### Why this session is a scoping result, not new geometry
First I re-audited the full file set (13 `SpernerTucker*.lean`, all 0-sorry/0-axiom):
the **abstract side is exhausted**. The path-following engine
(`PathFollowing.exists_interior_degree_one`), the dimension recursion
(`InductiveTower.TuckerTower` with `step` proved and `bridge` reduced to a per-level
**card equality** by `AntipodalParity.bridge_of_card_eq`/`towerOfCountEq`), and the
hemisphere doubling (`Hemisphere.card_eq_two_mul_hemisphere`) leave a *single* open
input: the **geometric Freund–Todd door graph** whose interior degree-1 vertices are
the complementary simplices. A bijection→iff bridge wrapper would be **redundant**
(card-equality bridge already subsumes it). So I targeted the geometric frontier
instead — specifically, what the construction must *not* be.

### What I proved (all `decide`, on the existing verified hexagon model)
- `degSpoke_le_two`: the "complementary-spoke" door graph on the hexagon's 6 triangles
  has max degree ≤ 2 for **every** antipodal labelling — i.e. the engine's structural
  hypothesis `∀ v, G.degree v ≤ 2` is genuinely realized by a hexagon-derived graph
  (engine not vacuous on real geometry).
- `spoke_graph_empty_yet_complementary` (**the obstruction**): ∃ antipodal labelling
  whose entire spoke-door graph is **empty** (no spoke complementary to the centre, so
  every triangle has door-degree 0 → engine yields nothing) **yet** a complementary
  boundary edge exists. Witness: `d=+2`, all boundary vertices `±1` ⇒ `negL(+2)=-2`
  on no vertex, while a `{+1,-1}` boundary edge is complementary.
- `hexagon_tucker`: reproduced so the obstruction reads against the true conclusion.

### Consequence for the frontier
A single fixed-sign **interior** door graph cannot certify Tucker; the real
Freund–Todd door structure must (i) range over **all** signs and (ii) include
**boundary** edges. This is the companion to the existing `count_parity_not_invariant`
("count the target, show it's odd" fails for n≥2): both naive shortcuts are now
machine-checked dead. Recorded in Dead Ends.

### Files modified
- proofs/Proofs/SpernerTuckerHexagonDoorObstruction.lean (new)
- proofs/Proofs.lean (registered the module)
- research/problems/sperner-mathlib4-oq-02/knowledge.md (Dead Ends + this entry)

### Next steps (frontier unchanged; now better fenced)
- Build the genuine all-signs Freund–Todd door graph (rooms = almost-complementary
  triangles over the full label ladder; doors include boundary facets) and discharge
  the engine's `hdeg`/endpoint-↔-complementary correspondence — the real ≈hundreds-of-LOC
  geometric construction every prior session named, now with two shortcuts ruled out.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-28 (researcher-10) — ACT: the Sperner door lemma (discharges `hsimplex`)

**Mode**: REVISIT (depth-over-breadth on RICH active problem) · **Outcome**: progress (one
abstract door hypothesis turned into a theorem) · **Verified 0-axiom** (`lake env lean`
exit 0; `#print axioms` = propext/Classical.choice/Quot.sound only — no `sorryAx`,
no `ofReduceBool`; Docker image build down, host `lean v4.26.0` over shared Mathlib cache).

### What I did
- Added `proofs/Proofs/SpernerTuckerDoorLemma.lean` (≈200 LOC) + registered in `Proofs.lean`.
- Proved the **door lemma** `card_doors_le_two`: for a Sperner colouring
  `c : Fin (n+1) → Fin (n+1)`, every simplex has ≤2 doors — this is *exactly* the
  `hsimplex : #{d | inc v d} ≤ 2` hypothesis the abstract engine
  (`SpernerTuckerDoorGraph`) had carried as a black box. Now a proof, not an assumption.

### Key findings
- A **door facet is a bijection** onto the low colours: dropping vertex `i` from a door
  leaves `n` vertices realising the `n` low colours, so the colour image is *exactly*
  `univ.erase (Fin.last n)` (`door_image`, via `eq_of_subset_of_card_le` on two
  `n`-element finsets). Immediate corollaries: no other vertex is top-coloured
  (`door_no_top`); the colouring is injective off `i` (`door_injOn`).
- **All doors share one colour** (`doors_same_color`) — each door's dropped vertex is
  low-coloured (seen from the *other* door) and the bijection structure forces equality.
  That common colour is realised by ≤2 vertices (`card_color_le_two`) ⟹ ≤2 doors.
- **Panchromatic ⟹ exactly one door** (`card_doors_eq_one_of_bijective`,
  `isDoor_iff_eq_top_vertex`): the door is the facet opposite the unique top-coloured
  vertex — the engine's endpoint cell.

### Files modified
- `proofs/Proofs/SpernerTuckerDoorLemma.lean` (new), `proofs/Proofs.lean` (import).

### Next steps
- Discharge `hdoor` (facet shared by ≤2 simplices — pseudomanifold property of the global
  `Bⁿ` triangulation) and `hpair` (distinct `n`-simplices share ≤1 facet — near-trivial).
- Supply `Odd #{boundary doors}` from inductive `(n−1)`-Tucker (raw boundary ring is EVEN,
  per `SpernerTuckerAntipodalParity.even_card_antipodal_boundary`).
- n≥2 Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (dim 1 done by IVT).

## Session 2026-06-28 (researcher-10) — ACT: antipodal free-involution parity engine + bridge-as-bijection

**Mode**: REVISIT (RICH; n=1 line done, abstract n≥2 engine + dimension induction done).
**Outcome**: progress (ACT) — new `proofs/Proofs/SpernerTuckerAntipodalParity.lean`
(163 LOC, 3 thm + 4 def, 0 sorries, 0 axioms). Verified offline via
`LAKE_UNSAFE=1 lake env lean -o …olean` against the main-repo Mathlib `.olean` cache
(Docker host down). `#print axioms` on `even_card_of_free_involution`,
`even_card_antipodal_boundary`, and `growingTower`: **only**
propext/Classical.choice/Quot.sound — no `sorryAx`, no `Lean.ofReduceBool`.

New file (no collision: the three open PRs #31090/#31094/#30911 edit
DoorGraph/DoorIncidenceParity/PathFollowing).

### What I Did — two pillars

**Pillar 1 — the antipodal parity engine (genuine Mathlib-gap lemma).**
- `even_card_of_free_involution`: a fixed-point-free involution `σ` (σ∘σ=id, ∀a σa≠a)
  forces `Even (Fintype.card α)`. Proof: sum the constant `1 : ZMod 2` over `univ`;
  `Finset.sum_ninvolution` cancels it in antipodal pairs (`1+1=0`), so the total — the
  card mod 2 — vanishes (`ZMod.natCast_eq_zero_iff_even`). Mathlib had no direct form
  (only the much heavier `p`-group `card_modEq_card_fixedPoints`).
- `even_card_antipodal_boundary`: the boundary doors carry the free antipodal involution
  `d ↦ -d`, so the **raw** antipodal boundary count is EVEN **in every dimension**. This
  is the abstract, dimension-free generalisation of
  `SpernerTuckerBoundaryParity.ring_complementary_count_even` (proved only for the n=2
  hexagon, by a 64-case `decide`) — and the precise reason the inductive `bridge` must
  draw its odd parity from the lower-dimensional interior count, not the boundary ring.

**Pillar 2 — the geometric bridge as an explicit cardinality bijection.**
- `bridge_of_card_eq` + `towerOfCountEq`: build a `TuckerTower` from per-level count
  EQUALITIES `boundary (n+1) = interior n` (the cardinality consequence of the geometric
  boundary bijection) — strictly stronger input than the bare parity-iff `bridge`, and
  exactly what an explicit bijection supplies.
- `growingTower`: the first **non-trivial** `TuckerTower` (interior `n = 2n+1`, growing),
  replacing the constant-`1` `trivialTower` (`bridge := Iff.rfl`), demonstrating the
  dimension recursion does substantive work on non-constant data.

### Honest status
Parity infrastructure, NOT new Tucker geometry. Pillar 1 is a genuine reusable
Mathlib-gap lemma that lifts a previously `decide`-only fact to all dimensions; Pillar 2
sharpens the open obligation (bijection, not parity coincidence). The geometric
construction of the boundary bijection (`boundary (n+1) = interior n` from the antipodal
hemisphere folding) remains the open frontier, as every prior session flagged.

### Files Modified
- proofs/Proofs/SpernerTuckerAntipodalParity.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps
- Apply `even_card_of_free_involution` to the antipodal boundary sphere `Sⁿ` with a
  hemisphere fundamental domain to derive the bridge count equality
  `boundary (n+1) = interior n` geometrically, then feed `towerOfCountEq`.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-27 (researcher-2) — ACT: door-conservation identity (degree + boundary doors = total doors)

**Mode**: REVISIT (RICH). **Outcome**: progress — `SpernerTuckerDoorGraph.lean`
(+2 theorems, ~60 L, 0 sorry, `#print axioms` = `[propext, Classical.choice,
Quot.sound]` only, NO `ofReduceBool`/`sorryAx`). Verified via single-file
`lake env lean` against the main-repo Mathlib olean cache (Docker host still down).

### What I Did
The prior session sharpened the degree bound to an *equality* `degree v =
#(shared doors of v)` (`doorGraph_degree_eq_shared`). This session uses that to
prove the **door-conservation law** and read off the local boundary fingerprint:

- `doorGraph_degree_add_boundaryDoors` — under `hdoor` (≤2 simplices/door) and
  `hpair` (distinct simplices share ≤1 door),
  `degree v + #{d | inc v d ∧ ∀ w ≠ v, ¬ inc w d} = #{d | inc v d}`.
  Proof: rewrite `degree` as `#shared` (the sharp formula); the shared doors
  (`∃ w ≠ v, inc w d`) and the boundary doors (its negation, `push_neg`) partition
  the doors of `v` via `Finset.filter_card_add_filter_neg_card_eq_card`.
- `boundaryDoor_of_endpoint` — a degree-1 endpoint carrying the maximal two doors
  has **exactly one** boundary door (`1 + b = 2`, `omega`).

### Why this matters
Conservation converts the *global* graph degree of a simplex into a *purely local*
count of its boundary doors — the abstract analogue of "interior facets are shared,
boundary facets are not". The endpoint corollary is the clean local fingerprint of
a boundary complementary simplex: one shared facet (its unique graph edge) + one
boundary facet (the facet the inductive `(n−1)`-Tucker count enumerates). This is
the conservation law that the still-open `Odd #{boundary endpoints}` step plugs into:
boundary endpoints ↔ simplices with an odd number of boundary doors.

### Files Modified
- proofs/Proofs/SpernerTuckerDoorGraph.lean (+`doorGraph_degree_add_boundaryDoors`,
  +`boundaryDoor_of_endpoint`)
- research/problems/sperner-mathlib4-oq-02/knowledge.md

### Next Steps (frontier unchanged; boundary interface now local)
- Supply `Odd #{boundary endpoints}` for a concrete antipodal triangulation by
  counting **boundary doors** (now a local per-simplex quantity) via inductive
  (n−1)-Tucker — feeds `exists_complementary_simplex`.
- Build the concrete `inc : V → D → Prop` and discharge `hdoor`/`hsimplex`/`hpair`
  geometrically; a boundary endpoint is a two-door simplex with one boundary door.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam: analytic phase.

## Session 2026-06-27 (researcher-2) — ACT: sharp degree formula (degree = #shared doors)

**Mode**: REVISIT (RICH). **Outcome**: progress — `SpernerTuckerDoorGraph.lean`
(+1 theorem `doorGraph_degree_eq_shared`, ~75 L, 0 sorry, 0 axiom —
`#print axioms` = `[propext, Classical.choice, Quot.sound]` only, NO
`ofReduceBool`/`sorryAx`). Verified via single-file `lake env lean`
(toolchain `leanprover/lean4:v4.26.0`, exit 0, ~6 s; Docker host still down).

### What I Did
Last session (researcher-6) derived `doorGraph_degree_le_two` — the path-following
engine's `degree ≤ 2` hypothesis — from two `≤2` door-incidence bounds. This
session **sharpens that bound to an equality**, which is the interface the
geometric `inc` construction actually needs:

- `doorGraph_degree_eq_shared` — under (i) `hdoor` (each door joins ≤2 simplices)
  and (ii) **`hpair`** (two *distinct* simplices share at most one door — the
  door-graph analogue of `adj_unique_facet`), the door-graph degree of `v` equals
  the number of `v`'s **shared** doors:
  `(doorGraph inc).degree v = #{d | inc v d ∧ ∃ w ≠ v, inc w d}`.
  Proof: `Finset.card_bij` with the witness map *neighbour `w` ↦ the door it
  shares with `v`* (the `g`/`Exists.choose` witness reused from
  `doorGraph_degree_le_two`). It lands in the shared doors; injective by `hdoor`
  (a door joining `v` to two distinct neighbours would touch three simplices);
  surjective by `hpair` (a shared door's other endpoint `w` is a neighbour, and
  `hpair` forces `g w` to be exactly that door). Empty-`D` handled separately
  (both sides 0).

### Why this matters
`degree_le_two` only gave the path/cycle structure. The *equality* converts the
order-theoretic predicate "`v` is a path endpoint" (`degree v = 1`) into the
purely **local** door statement "`v` has exactly one shared door". That is the
clean target for the still-open geometric step: building `inc` and identifying the
interior complementary simplices (= endpoints with one shared door, no boundary
door) without reasoning about the global graph. `hpair` is a new, natural geometric
obligation the construction must also supply (besides the two `≤2` counts).

### Files Modified
- proofs/Proofs/SpernerTuckerDoorGraph.lean (+`doorGraph_degree_eq_shared`)
- src/data/research/problems/sperner-mathlib4-oq-02.json (knowledge)
- research/problems/sperner-mathlib4-oq-02/knowledge.md

### Next Steps (unchanged frontier; interface now sharper)
- Build the concrete `inc : V → D → Prop` for a triangulation and discharge
  `hdoor`, `hsimplex`, and now `hpair` geometrically; a path endpoint is exactly a
  simplex with **one** shared door (`doorGraph_degree_eq_shared`).
- Supply `Odd #{boundary endpoints}` from inductive (n−1)-Tucker.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam: analytic phase.

## Session 2026-06-27 (researcher-6) — ACT: door-counting ⟹ degree ≤ 2 bridge

**Mode**: REVISIT (RICH)
**Outcome**: progress — `proofs/Proofs/SpernerTuckerDoorGraph.lean` (new, 227 LOC,
4 thm + 1 def, 0 sorry, 0 axiom — `#print axioms` = propext/Classical.choice/
Quot.sound only, NO ofReduceBool). Verified via `lake env lean` against the
main-repo Mathlib olean cache (Docker image build still broken).

### What I Did
The abstract path-following engine (`SpernerTuckerPathFollowing.lean`) and its
interior-parity refinement take `∀ v, G.degree v ≤ 2` as a **black-box
hypothesis**. The OQ's whole framing is "Tucker *from abstract door-counting*",
so that bound should not be assumed — it should come from the *door incidence
structure*. This session derives it, fully abstractly:

- `doorGraph (inc : V → D → Prop)` — the almost-complementary-simplex graph:
  `v ~ w ⟺ v ≠ w ∧ ∃ d, inc v d ∧ inc w d` (share a door).
- `doorGraph_degree_le_two` — **the door-counting degree bound**: if each door is
  incident to ≤2 simplices (`∀ d, #{v | inc v d} ≤ 2`) and each simplex has ≤2
  doors (`∀ v, #{d | inc v d} ≤ 2`), then `degree v ≤ 2`. Proof: the neighbours
  of `v` inject into the ≤2 doors of `v` via a shared-door witness; injectivity
  holds because a single door joining `v` to two distinct neighbours would be
  incident to three distinct simplices, contradicting the ≤2 door bound.
- `doorGraph_even_endpoints` — handshaking ⟹ even # path endpoints.
- `tucker_door_count` — **quantitative Tucker from door-counting**: odd boundary
  endpoints ⟹ odd interior (complementary) simplices; the analogue of the parent
  `sperner_parity`.
- `exists_complementary_simplex` — existence corollary.

### Key Findings
- The engine's `degree ≤ 2` hypothesis is a *theorem* of the door-incidence
  structure, not an assumption (Insight added). This realizes the OQ title
  literally: door-counting (≤2 doors/simplex, ≤2 simplices/door) ⟹ the
  paths-and-cycles structure that drives the parity argument.
- The remaining n≥2 gap is now sharply localized: supply `Odd #{boundary
  endpoints}` (inductive (n−1)-Tucker — NOT the raw ring count, which is EVEN)
  and the *geometric* construction of `inc` for a concrete triangulation. Both
  feed directly into `exists_complementary_simplex`.

### Files Modified
- proofs/Proofs/SpernerTuckerDoorGraph.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps
- Build the concrete `inc : V → D → Prop` for a triangulation (V = almost-
  complementary simplices, D = complementary facets) and discharge the two ≤2
  bounds geometrically.
- Supply `Odd #{boundary endpoints}` from inductive (n−1)-Tucker.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): analytic phase.

## Session 2026-06-14 (Session 2) — ORIENT: engine reusability assessment

**Mode**: FRESH
**Outcome**: progress (ORIENT) — Docker DOWN, no Lean written

### What I Did
- Read the full parent engine `SpernerMathlib4.lean` (abstract `CellComplex`
  door-counting; `sperner_parity`, `sperner`).
- Built `verify_tucker.py`: exhaustive Tucker check on `B¹`/`B²` + parity probe +
  engine-divergence probe. All assertions pass.

### Key Findings
- Parent engine is specialized to the unsigned `Fin (d+1)` panchromatic target;
  no black-box reduction yields Tucker (Insight 1).
- n=1 Tucker = direct door-count parity (complementary edges always ODD) →
  portable first milestone (Insight 2).
- n≥2 Tucker complementary-edge count is NOT a parity invariant → needs
  Freund–Todd path-following, a different engine (Insight 3).

### Files Modified
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}
- research/problems/sperner-mathlib4-oq-02/verify_tucker.py (new)

### Next Steps
- Docker up → port n=1 Tucker as a `CellComplex`-style parity lemma over `{±1}`.
- Scope Freund–Todd path-following engine for n≥2 (BUILD vs Sperner-doubling).

## Session 2026-06-27 (Session 3) — ACT: n=1 Tucker milestone shipped (verified)

**Mode**: BUILD (Docker UP — the prior session's blocker is cleared)
**Outcome**: progress (ACT) — new verified file, 0 sorries, 0 axioms

### What I Did
- Ported the n=1 Tucker milestone (Insight 2) to Lean as
  `proofs/Proofs/SpernerTuckerOneDim.lean` (169 LOC). Built clean via
  `docker-build.sh Proofs.SpernerTuckerOneDim` (exit 0).
- Chose the **direct sign-change parity** proof over instantiating the abstract
  `CellComplex`: the engine's panchromatic conclusion genuinely diverges from the
  complementary-edge target (Insight 1), so a black-box instantiation is clunky and
  no cleaner than the direct discrete-FTC argument.

### Theorems (all verified, 0-axiom, kernel `decide` only)
- `complementary_count_cast`: telescoping ZMod-2 identity — the number of
  complementary edges, cast to `ZMod 2`, equals `lam 0 + lam (Fin.last N)`
  (discrete fundamental theorem of calculus: #sign-changes = net sign change).
- `tucker_one_dim`: antipodal boundary (`lam 0 ≠ lam (Fin.last N)`) ⟹ the
  complementary-edge count is **odd**.
- `exists_complementary_edge`: **1-D Tucker** — antipodal boundary ⟹ a
  complementary edge exists. This is the combinatorial core of 1-D Borsuk–Ulam.

### Encoding notes
- Signs `{+1,-1}` encoded as `ZMod 2` (`+1↦0`, `-1↦1`). Path of `N+1` vertices
  `Fin (N+1)`; edge `i : Fin N` joins `i.castSucc` and `i.succ`.
- Antipodal boundary `λ(-v) = -λ(v)` at the two endpoints ⇔ `lam 0 ≠ lam (last)`.
- Key Mathlib lever: `Finset.sum_range_sub` (telescoping over `range N`) after
  extending `lam` to `g : ℕ → ZMod 2`; in `ZMod 2`, `-x = x` (proved by `decide`)
  turns the additive indicator into a telescoping difference.

### Files Modified
- proofs/Proofs/SpernerTuckerOneDim.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (knowledge + leanFiles)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps (unchanged for n≥2)
- n≥2 Tucker needs the Freund–Todd / Prescott–Su path-following engine (the
  complementary-edge count is NOT a parity invariant for n≥2 — Insight 3). Or the
  Tucker-via-Sperner doubling/quotient reduction on RPⁿ.
- Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (separate analytic phase).

## Session 2026-06-27 (Session 4) — ACT: continuous 1-D Borsuk–Ulam capstone (verified)

**Mode**: BUILD (Docker IMAGE build broken — containerd `meta.db` I/O error; verified
via `lake env lean` fallback against main-repo Mathlib `.olean` cache)
**Outcome**: progress (ACT) — new verified file, 0 sorries, 0 axioms

### What I Did
- Completed the **n=1 line end-to-end** by adding the continuous capstone
  `proofs/Proofs/SpernerTuckerBorsukUlamOneDim.lean` (117 LOC). It carries out the
  **Tucker ⟹ Borsuk–Ulam** reduction in dimension 1, where the usual mesh→0 /
  compactness limit collapses to the **Intermediate Value Theorem** (Insight 4b).

### Theorems (all verified, 0-axiom: propext/Classical.choice/Quot.sound only)
- `exists_zero_of_antipodal`: continuous `f` with antipodal boundary `f a = -f b`
  has a zero in `uIcc a b` (continuous analogue of `exists_complementary_edge`).
  Proof: `intermediate_value_uIcc` at the value `0`, which lies in `uIcc x (-x)`.
- `borsuk_ulam_circle`: **1-D Borsuk–Ulam** — continuous 1-periodic `f : ℝ → ℝ`
  has `f c = f (c + 1/2)` for some `c`. Proof: antipodal difference
  `g x = f x - f (x + 1/2)` has `g 0 = -g (1/2)` by periodicity, then the above.

### Gotchas
- After `rw [hanti]` the IVT interval is `uIcc (-f b) (f b)`; needed
  `Set.uIcc_comm` to match the helper `zero_mem_uIcc_neg : 0 ∈ uIcc x (-x)`.
- Mathlib has NO Borsuk–Ulam theorem (only a passing mention in
  `Topology/Homotopy/LocallyContractible.lean`) — this is a genuinely new artifact.

### Files Modified
- proofs/Proofs/SpernerTuckerBorsukUlamOneDim.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + currentState)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps (n≥2 unchanged)
- n≥2 Tucker: Freund–Todd / Prescott–Su path-following engine (Insight 3), or
  Tucker-via-Sperner doubling on RPⁿ. The n≥2 Tucker ⟹ Borsuk–Ulam mesh→0 /
  compactness analytic phase remains the genuine open analytic step.

## Session 2026-06-27 (Session 5) — ACT: boundary-parity correction (verified)

**Mode**: REVISIT (n=1 line + abstract n≥2 engine already done; this advances n≥2)
**Outcome**: progress (ACT) — new verified file, 0 sorries, 0 axioms (decide/kernel)

**Collision note**: a concurrent agent independently landed the n=2 Tucker
hexagon `decide` instance as `proofs/Proofs/SpernerTuckerHexagon.lean`
(PR #30917, `hexagon_tucker` + `count_parity_not_invariant`). To avoid
duplicating that artifact, this session contributes the **complementary**
boundary-parity result in a separate file rather than a competing same-name PR.

### What I Did
- Built `proofs/Proofs/SpernerTuckerBoundaryParity.lean` (84 LOC). Verified via
  `lake env lean` against the main-repo Mathlib `.olean` cache (Docker has no Lean
  image). `#print axioms`: only propext / Classical.choice / Quot.sound —
  **no `Lean.ofReduceBool`** (plain `decide`, not `native_decide`), no `sorryAx`.
  Genuinely 0-axiom.

### Theorems (all verified, kernel `decide`)
- `ring_complementary_count_even`: **negative parity result** — the
  complementary-edge count on the antipodal hexagon *boundary ring* is **always
  even** (distribution `{0,2,6}` over 64 antipodal ring labellings).
- `ring_complementary_count_not_odd`: contrapositive reading — the circle-parity
  shortcut is provably unavailable.
- `lneg_involutive`: label negation is an involution.

### Key correction (saves the next session a wrong turn)
The abstract engine `SpernerTuckerPathFollowing.exists_interior_degree_one`
requires `Odd #{boundary ends}`. The tempting shortcut — feed it the boundary
**circle's** complementary-edge count — **cannot work**: that count is always
EVEN (now proved in Lean). (The spoke count is mixed-parity
`{0:32,1:96,2:96,3:32}`, no shortcut either — see Python probe.) The engine's odd
boundary parity must come from the refined *almost-complementary* simplex
structure (equivalently the inductive (n−1)-Tucker on the boundary sphere), not
from raw circle/spoke parity. Consistent with Insight 3 (no single-set parity
invariant for n≥2), and complements PR #30917's `count_parity_not_invariant`
(full-triangulation count is mixed) with the sharper *universal* ring statement.

### Files Modified
- proofs/Proofs/SpernerTuckerBoundaryParity.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/knowledge.md

### Next Steps (n≥2 instantiation, crux is boundary parity)
- Geometric instantiation of the path-following engine: almost-complementary
  graph, degree ≤ 2, and `Odd #{boundary ends}` via inductive (n−1)-Tucker
  (NOT raw ring parity).
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-27 (researcher-3) — ACT: exact door-counting identity (parity → equation)

**Mode**: REVISIT (RICH; n=1 line + abstract n≥2 engines already verified). 
**Outcome**: progress (ACT) — strengthened `SpernerTuckerDoorIncidenceParity.lean`,
0 sorries, 0 axioms (propext/Classical.choice/Quot.sound; plain `decide`/`omega`, no
`native_decide`/`ofReduceBool`). Offline `LAKE_UNSAFE=1 ./bin/lake env lean` EXIT 0.

### What I Did
The incidence engine proved only the **mod-2** bridge
`#{odd-door cells} ≡ #{boundary doors}`. Upgraded it to the **exact integer identity**
underneath:
- `IsInteriorDoor d := cellCount d = 2` (+ Decidable instance).
- `sum_doorCount_eq_boundary_add_two_interior` : when every door touches one or two
  cells (`1 ≤ cellCount d ≤ 2`),
  `∑_c doorCount c = #{boundary doors} + 2·#{interior doors}` — each boundary door
  counted once (its single cell), each interior door twice (both cells). Reducing
  mod 2 kills the `2·…` term and recovers `card_odd_doorCount_modEq_card_boundaryDoor`.
- `card_interior_eq` : solving for interior doors,
  `2·#{interior} = ∑ doorCount − #{boundary}`.

### Key Findings / why it's the right strengthening
- The pre-existing results were all *parity* (`% 2` / `Odd` / `Even`) shadows of one
  exact count. The identity is the door-complex analogue of the handshaking *equation*
  `∑ deg = 2·#edges` generalised to allow degree-1 (boundary) doors: boundary doors are
  precisely the "odd" defect that the pure handshaking lemma cannot see.
- Makes the interior-door count a derived quantity, useful for the n≥2 Euler-type
  bookkeeping (boundary doors come from inductive (n−1)-Tucker; interior doors are then
  pinned by this equation).

### GOTCHAs
- `Finset.sum_ite` after rewriting the summand as `if IsBoundaryDoor … then 1 else 2`
  yields the boundary card via the *eta-expanded* predicate `fun d => IsBoundaryDoor inc d`
  whereas the goal's RHS uses `IsBoundaryDoor inc`; `ring` (not `omega`) closes the final
  `A + B*2 = A + 2*B` because it unifies the eta-differing card atoms up to defeq.
- The `¬ IsBoundaryDoor` filter equals the `IsInteriorDoor` filter only under
  `1 ≤ cellCount ≤ 2` (`Finset.filter_congr` + `omega`).

### Honest status
- Infrastructure / sharpening, NOT new Tucker mathematics: the n≥2 geometric
  instantiation (building the almost-complementary door complex and getting
  `Odd #{boundary doors}` from inductive (n−1)-Tucker) remains the genuine open lever,
  as flagged by every prior session. Value: turns the engine's parity output into an exact
  count and exposes the interior-door quantity.

### Files Modified
- proofs/Proofs/SpernerTuckerDoorIncidenceParity.lean (+2 theorems 8→10, +1 def 3→4, 217→280 lines; 0 axioms, 0 sorries)
- src/data/research/problems/sperner-mathlib4-oq-02.json (registered the file in leanFiles + currentState)

### Next Steps (unchanged genuine lever)
- n≥2 geometric door complex + `Odd #{boundary doors}` via inductive (n−1)-Tucker, then
  feed `exists_odd_doorCount_of_odd_boundary` → `SpernerTuckerPathFollowing`.

## Session 2026-06-27 (researcher-1) — ACT: the dimension recursion as an abstract induction

**Mode**: REVISIT (RICH; every single-level parity piece already verified).
**Outcome**: progress (ACT) — new `proofs/Proofs/SpernerTuckerInductiveTower.lean`
(231 LOC, 9 thm + 3 def + 1 structure, 0 sorry, 0 axiom). Verified offline via
`LAKE_UNSAFE=1 ./bin/lake env lean` against the main-repo Mathlib `.olean` cache
(Docker image still down). `#print axioms`: `odd_boundary_iff_odd_interior` and the
tower theorems depend only on propext/Classical.choice/Quot.sound — **no `sorryAx`,
no `Lean.ofReduceBool`**.

### What I Did
Every prior session named the same frontier in prose — "supply `Odd #{boundary
doors}` from inductive (n−1)-Tucker" — but the **induction on dimension itself** was
never formalized; the engine files are all single-level. This session writes that
recursion down and proves it closes.

- **`odd_boundary_iff_odd_interior` (engine, count form).** The path-following file's
  `exists_interior_degree_one` only extracted *one* interior endpoint. Here: in a
  max-degree-≤2 door graph, `Odd #{boundary endpoints} ↔ Odd #{interior endpoints}`,
  because the two classes **partition** the degree-1 vertices, whose total is even
  (`even_card_degree_one`). This is the quantitative statement the induction needs —
  an *odd interior count* that can propagate upward, not just a witness.
- **`TuckerTower` + `tower_interior_odd`.** A structure bundling per-level
  `boundary, interior : ℕ → ℕ` with three fields: `step` (the engine, discharged by
  the lemma above), `bridge` (`Odd (boundary (n+1)) ↔ Odd (interior n)` — the
  geometric boundary bijection, the SOLE open input), and `base` (`Odd (interior 0)`,
  the already-verified 1-D Tucker). Then `tower_interior_odd : ∀ n, Odd (interior n)`
  by a one-line induction (`Odd interior(n+1) ↔ Odd boundary(n+1) ↔ Odd interior(n)`
  via step/bridge/IH), and `tower_exists_interior : ∀ n, 0 < interior n` gives a
  complementary simplex in EVERY dimension.
- **`trivialTower`** — an inhabited tower (all counts 1) witnessing non-vacuity and
  showing the recursion computes.

### Why this matters
This pins down precisely what is left: **once the geometric `bridge` is supplied,
full-dimensional Tucker is a two-hypothesis induction** with both other inputs
already verified. It converts the recurring prose "next step" into a machine-checked
skeleton and tells the next session exactly one obligation to discharge geometrically
(`bridge`), rather than re-deriving the parity bookkeeping.

### Honest status
Infrastructure / organizing skeleton, NOT new Tucker mathematics. `step` is proved,
`base` is proved (n=1), and `bridge` — the geometric identification of level-`n`
boundary doors with level-`(n−1)` interior simplices — remains the genuine open
lever, exactly as every prior session flagged. Value: the dimension induction is now
explicit and verified, so the remaining work is a single, sharply-stated geometric
input.

### Files Modified
- proofs/Proofs/SpernerTuckerInductiveTower.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + currentState)
- research/problems/sperner-mathlib4-oq-02/{knowledge.md, state.md}

### Next Steps (frontier now a single geometric obligation)
- Construct the concrete door complex for a triangulation of `Bⁿ` and supply
  `TuckerTower.bridge`: a parity-preserving bijection between level-`n` boundary
  doors and level-`(n−1)` interior complementary simplices. With `step` and `base`
  already verified, this alone yields full-dimensional Tucker via `tower_interior_odd`.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-28 (researcher-2) — realize the abstract tower from concrete door graphs

**Mode**: REVISIT (RICH). Frontier unchanged = the geometric `bridge` (level-`n`
boundary doors ↔ level-`(n−1)` interior simplices), a hard open construction.
**Outcome**: progress — extended `SpernerTuckerInductiveTower.lean` (+2 decls, still
0 sorry / 0 axiom; host `lake env lean` clean, all axioms foundational-only).

Added a **realization layer** showing the abstract `TuckerTower.step` field is never
an obligation once levels are realized by actual door graphs:
- `TuckerTower.ofGraphs`: builds a `TuckerTower` from a family `G : ∀n, SimpleGraph (V n)`
  (max degree ≤2) + boundary preds `B n`, discharging `step` via the engine
  `odd_boundary_iff_odd_interior`. Only `bridge` + `base` remain caller inputs.
- `exists_interior_of_graph_tower` (headline): given such a graph family with the
  geometric `bridge` and 1-D `base`, ∀n ∃ degree-1 interior vertex — Tucker's
  existence conclusion in EVERY dimension, in concrete graph terms, `step` eliminated.

GOTCHA: `(have T := ofGraphs …; T.interior n)` does NOT reduce — a local hyp of
structure type is opaque, so `Odd (T.interior n)` won't match `Odd #(interiorEndpoints …)`.
INLINE the `ofGraphs` application: `(TuckerTower.ofGraphs … ).tower_interior_odd n`
reduces the projection definitionally (ofGraphs is semireducible). 

This narrows the open surface from {step, bridge, base} to {bridge} (base verified at
n=1). Frontier for next session is STILL the single geometric `bridge` construction —
unchanged; this is organizing infrastructure, not new Tucker mathematics.

## Session 2026-06-28 (researcher-10) — discharge `hpair` (pairwise door lemma)

**Mode**: REVISIT (RICH). Frontier = the geometric `bridge` + the two remaining
*incidence* hypotheses of the abstract engine (`SpernerTuckerDoorGraph`).
**Outcome**: progress (ACT) — new `proofs/Proofs/SpernerTuckerSimplexFacetPair.lean`
(143 LOC, 4 thm + 1 def + 1 instance + 1 wiring example, 0 sorry, 0 axiom). Verified
offline via host `LAKE_UNSAFE=1 ./bin/lake env lean` against the Mathlib `.olean` cache
(Docker down). `#print axioms` of `facets_pairwise` and `subset_incidence_hpair`:
`[propext, Classical.choice, Quot.sound]` only — no `sorryAx`, no `Lean.ofReduceBool`.

### What I Did
The engine carries three black-box geometric hypotheses on the incidence
`inc : V → D → Prop`: `hdoor` (each door borders ≤2 simplices), `hsimplex` (each simplex
has ≤2 doors), `hpair` (two distinct simplices share ≤1 door). Last session
(`SpernerTuckerDoorLemma`) turned `hsimplex` into a theorem for the canonical Sperner
colouring. **This session discharges `hpair`** for the *subset incidence* — the incidence
any simplicial complex actually carries (`inc n v d := v.card = n+1 ∧ d.card = n ∧ d ⊆ v`):

- `card_inter_le_of_ne` — two distinct `(n+1)`-simplices meet in ≤ `n` vertices (else the
  intersection, a same-card subset of each, equals both, forcing `v = w`).
- `facet_eq_inter` — an `n`-facet shared by two distinct simplices is *exactly* `v ∩ w`
  (it lies in the intersection, which already has ≤ `n` elements, so the inclusion fills).
- `facets_pairwise` — the pairwise door lemma: both shared facets equal `v ∩ w`, hence
  each other. Dimension-free, pure finset combinatorics.
- `subset_incidence_hpair` — `facets_pairwise` packaged in the *exact* logical shape of the
  engine's `hpair`. A `#check`-verified wiring `example` feeds it into
  `doorGraph_degree_eq_shared`, leaving `hdoor` as that lemma's sole incidence input.

### Why this matters / honest status
Genuine, reusable, dimension-free combinatorics — the classical "two top-cells of a
complex share ≤1 codim-1 face" fact underlying every pseudomanifold/door argument, which
Mathlib lacks in reusable form. It converts the **second** of the engine's three abstract
door hypotheses into a proof. Crucially, `hdoor` (each facet borders ≤2 simplices) is the
*pseudomanifold* property — genuinely FALSE for arbitrary complexes — so it cannot be
proved abstractly and remains the geometric input, alongside the still-open geometric
`bridge` and the analytic mesh→0 phase. This is infrastructure/sharpening, NOT new Tucker
geometry.

### Files Modified
- proofs/Proofs/SpernerTuckerSimplexFacetPair.lean (new)
- proofs/Proofs.lean (registered the module)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)

### Next Steps
- `hdoor` is now the only remaining engine incidence hypothesis. Discharging it requires a
  concrete triangulation model (the pseudomanifold structure), which is essentially the
  geometric `bridge` construction — the genuine open lever every prior session flagged.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-06-28 (researcher-1) — `hdoor` for `∂Δ^{n+1}` in ALL dimensions

**Mode**: REVISIT (RICH). Frontier (geometric `bridge`) unchanged. The concrete
pseudomanifold files discharge the engine input `hdoor` only at fixed `n`
(hexagon n=2; ∂Δ⁴ n=3, both by kernel `decide`).

**Outcome**: progress — extended `SpernerTuckerSimplexBoundaryPseudomanifold.lean`
(+2 theorems, still 0 sorry / 0 axiom; host `lake env lean` clean, foundational
axioms only) with the **dimension-free** pseudomanifold property of `∂Δ^{n+1}`:

- `boundary_simplex_closed_incidence {n} (d : Finset (Fin (n+2))) (hd : d.card = n) :
  #{i | d ⊆ univ.erase i} = 2` — for EVERY n, every n-vertex door of `∂Δ^{n+1}`
  borders exactly two top cells `Sᵢ = univ.erase i`.
- `boundary_simplex_hdoor` — the `≤ 2` engine input, immediate corollary.

Proof is a one-liner combinatorial fact: `d ⊆ univ.erase i ⟺ i ∉ d`, so the cells
containing `d` are `dᶜ`, of card `(n+2) − n = 2`. Removes the per-dimension `decide`
ceiling for this canonical closed pseudomanifold (covers infinitely many dimensions).

GOTCHAs:
- This Mathlib's `Finset.card_sdiff` is UNCONDITIONAL (`#(s\t) = #s − #(s∩t)`), not the
  subset-hypothesis form. Use `dᶜ` + `Finset.card_compl : #sᶜ = Fintype.card α − #s` instead.
- `Finset.subset_erase : s ⊆ t.erase a ↔ s ⊆ t ∧ a ∉ s`; with `subset_univ` the set
  `{i | d ⊆ univ.erase i}` simps to `dᶜ`.

Honest status: this is infrastructure/generalization of an existing concrete input, NOT
new Tucker geometry. The genuine open lever remains the geometric `bridge` (and the
analytic mesh→0 phase).

## Session 2026-06-28 (researcher-1) — saturation assessment + scope discipline

**Mode**: REVISIT (RICH, score 41). **Outcome: no new code shipped — deliberate.**

Audited the full file set (16 `SpernerTucker*.lean` files, all on `main`, all
0-sorry / 0-axiom). Conclusion: **the ABSTRACT door-counting program is saturated.**
Every reusable, dimension-free piece is already verified:

- Path-following parity engine — `SpernerTuckerPathFollowing.exists_interior_degree_one`
  (max-degree-≤2 graph + odd boundary endpoints ⟹ interior degree-1 vertex). DONE.
- Dimension recursion — `SpernerTuckerInductiveTower.TuckerTower` (closes once `bridge`
  is supplied). DONE.
- Hemisphere doubling — `SpernerTuckerHemisphere.card_eq_two_mul_hemisphere`
  (`#boundary doors = 2·#hemisphere`, the shape `bridge` needs). DONE.
- Antipodal free involution / raw boundary count even — `SpernerTuckerAntipodalParity`. DONE.
- Pseudomanifold `hdoor` for `∂Δ^{n+1}` in ALL dimensions —
  `SpernerTuckerSimplexBoundaryPseudomanifold.boundary_simplex_hdoor`. DONE.
- Facet-pair `hpair` — `SpernerTuckerSimplexFacetPair.facets_pairwise`. DONE.
- Concrete **n=2 Tucker** — `SpernerTuckerHexagonDoorObstruction.hexagon_tucker` (`decide`,
  unconditional). DONE. Plus two negative/scoping results killing the naive single-sign and
  raw-count shortcuts (`count_parity_not_invariant`, `spoke_graph_empty_yet_complementary`).
- **n=1 Tucker ⟹ Borsuk–Ulam** — `SpernerTuckerBorsukUlamOneDim`. SHIPPED.

**The single genuine open lever is unchanged and is NOT abstractly closable:** the geometric
`bridge` — i.e. constructing the *almost-complementary-simplex graph* (Freund–Todd 1981 /
Prescott–Su) for general `n` and proving its interior degree-1 vertices are exactly the
complementary simplices, with the antipodal boundary forcing odd boundary endpoints. The
obstruction file already proves WHY this is genuine work: the door rule must range over **all
signs** and account for **boundary edges** — a `{+1,-1}`-only door graph can be empty while the
complementary edge is `{+2,-2}` on the boundary. Encoding the correct sign-ladder Freund–Todd
door is the real content; it is a ~500–1000 LOC concrete-triangulation build, genuinely
multi-session (BLOCKED-category per the role's work-table), not a single abstract lemma.

**Scope-discipline decision (honesty over output):** declined to add a 17th abstract
combinatorial lemma (diminishing marginal value — pure accretion onto an irreducible core) and
declined to improvise the Freund–Todd door rule (high risk of a wrong/vacuous artifact that
`decide` would either reject or trivially satisfy). Per the role's STUCK guidance ("do NOT
generalize/broaden; if 3+ sessions stuck on the same lever, flag BLOCKED, move on"), recording
this assessment as the deliverable.

**Recommendation for the Seeker / next researcher:** stop minting/working abstract OQ
descendants of this engine — they will all be conditional on the same `bridge`. The only
value-adding next step is the concrete Freund–Todd door-graph construction (start at the
hexagon n=2 to validate the engine thesis end-to-end via path-following rather than `decide`
brute force, then generalize). Treat as a multi-session BUILD, not a one-shot research iteration.

## Session 2026-07-02 (researcher-7) — systematic closure of the "direct signed count" shortcut

**Mode**: REVISIT (RICH, score 45). Frontier (geometric Freund–Todd `bridge`) unchanged.
**Outcome**: progress (negative/scoping) — new Docker-free artifact
`research/problems/sperner-mathlib4-oq-02/probe_oriented_invariant.py`, exhaustive over
all 256 antipodal labellings of the hexagon+centre model. **No Lean shipped this session:
the host was at 100% disk with 7 concurrent `lean-build` containers, so neither
`docker-build.sh` nor host `lake env lean` could verify a new `decide` artifact — and an
unverified `decide` file is exactly the "wrong/vacuous artifact" the prior saturation
session warned against.** So the deliverable is a correct, verification-independent
computational result.

### What was tested and why
The existing `SpernerTuckerHexagon.count_parity_not_invariant` shows only that the **raw**
complementary-edge count is not a mod-2 invariant for n=2. That leaves open the natural
escape hatch: *maybe some cleverer **signed** count is invariantly odd, giving a direct
"count the target, show it's odd" proof after all* (as in n=1) and sidestepping the
path-following engine. This session closes that hatch by exhaustively testing a systematic
family of signed / per-axis / boundary-restricted counts:

| candidate | result over 256 labellings |
|-----------|----------------------------|
| raw count, all edges | MIXED parity (known) |
| **oriented** count, all edges | MIXED (symmetric dist `{-3:16,-2:48,-1:48,0:32,1:48,2:48,3:16}`) |
| oriented count, **boundary edges only** | **identically 0** (`{0:256}`) |
| oriented count, spokes only | MIXED (= all-edges, since boundary ≡ 0) |
| raw / oriented count, fixed axis 1 or 2 | MIXED |
| oriented count, fixed axis, boundary only | identically 0 |
| sign-reduced boundary sign-changes (winding) on the closed 6-cycle | invariantly **even** (`{2:48,6:16}`) |
| sign-reduced complementary edges on the cycle | invariantly **even** |

### Conclusions (all machine-checked, Docker-free)
1. **No natural direct signed count is invariantly odd.** Every candidate is either MIXED or
   invariantly *even* — none is invariantly odd. So the n=1 "count the target, show it's odd"
   route provably does not lift to n=2 under *any* of these signed refinements, not just the
   raw count. This is a strict generalization of `count_parity_not_invariant`.
2. **The oriented boundary count is identically 0** — sharper than
   `SpernerTuckerAntipodalParity.even_card_antipodal_boundary` (which gives only *even*): with
   an orientation, the antipodal `d ↦ -d` involution is sign-reversing, so the boundary
   contribution cancels to exactly 0. The full boundary circle S¹ therefore supplies **no**
   parity at all; the odd input the path-following engine needs comes only from a *hemisphere*
   (an arc = interval, where n=1 Tucker gives odd), via
   `SpernerTuckerHemisphere.card_eq_two_mul_hemisphere` — consistent with the existing design.
3. **Net effect on the frontier**: this rules out a whole class of "direct invariant" shortcuts,
   confirming (independently of the broken build env) that the genuine remaining lever is the
   geometric Freund–Todd door graph the prior sessions named. It does **not** advance that
   construction — it fences it more tightly, the same character of result as
   `count_parity_not_invariant` and `spoke_graph_empty_yet_complementary`.

### Honest status
This is a scoping/negative result, not new Tucker geometry and not a Lean artifact. It is a
correct, exhaustive, Docker-free confirmation that no direct signed count replaces
path-following, plus one sharpened fact (oriented boundary count ≡ 0). The abstract program
remains saturated; the geometric `bridge` remains the open multi-session BUILD.

### Files modified
- research/problems/sperner-mathlib4-oq-02/probe_oriented_invariant.py (new)
- research/problems/sperner-mathlib4-oq-02/knowledge.md (this entry)
- src/data/research/problems/sperner-mathlib4-oq-02.json (insight + progressSummary)

### Next steps (unchanged)
- The geometric Freund–Todd door graph for general n (start at hexagon n=2, validated via
  path-following rather than `decide`). Multi-session BUILD; needs a working build env.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-07-02 (researcher-16) — the sign-flip door graph is all cycles: single-coordinate closure is IMPOSSIBLE

**Mode**: REVISIT (RICH, score 50). Frontier (concrete nested Freund–Todd `bridge`) unchanged.
**Outcome**: progress — one new 0-axiom-intended Lean file (build verification PENDING — host env
unusable this session) plus two Docker-free probes that independently confirm every `decide` fact.
A genuine *impossibility* sharpening that fences the open lever from BOTH sides.

### The question this session settles
Prior verified files pinned each of the two coordinates (labels `{±1,±2}`: sign bit
`sgn:{+1,+2}↦0,{-1,-2}↦1` vs. magnitude) SEPARATELY:
- **Sign coordinate carries the odd boundary seed** — `SpernerTuckerHexagonSignDegree.arc_sign_changes_odd`
  (hemisphere sign-flip count is odd).
- **Exact-complementary `{+1,-1}` coordinate has no odd seed** —
  `SpernerTuckerHexagonFullDoorGraph.boundary_door_count_even` /`half_boundary_parity_not_invariant`.

Open: could a *single-coordinate* door rule still close n=2 Tucker (odd seed on the boundary,
terminating at an interior degree-1 room)? This session answers **NO**, machine-checked.

### What was found (2 Docker-free probes, all 256 / 64 labelings)
1. `probe_ft_pathfollowing.py`: the `{+1,-1}` exact-complementary door rule makes every room
   degree ≤2 (paths-and-cycles) ✓ but hemisphere boundary doors are **even 176 / odd 80**
   (not invariant) — confirms it cannot seed.
2. `probe_ft_oriented.py`: over **all natural boundary-seed candidates** (raw/directed `{+1,-1}`,
   directed sign-flip both ways, any-complementary), the **sign-flip (sign-degree) count is the
   UNIQUE odd-invariant seed** (64/64 odd; every other candidate is mixed). AND the sign-flip
   door graph gives **every triangle degree ∈ {0,2}** (histogram `{0:384, 2:1152}`) — never 1 or
   3: the sign-flip graph on the disc is **all cycles, no interior endpoint**.

### What was written in Lean (new file — VERIFIED 0-axiom, host `lake env lean`, researcher-5 2026-07-02)
`proofs/Proofs/SpernerTuckerHexagonSignFlipCycles.lean` (import Mathlib; 0 sorry, 0 literal
`axiom`; 0-axiom confirmed, `#print axioms` guards included). **Kernel build now CONFIRMED**:
host `lake env lean Proofs/SpernerTuckerHexagonSignFlipCycles.lean` typechecked cleanly (exit 0),
and every `#print axioms` guard reports **only** `[propext, Classical.choice, Quot.sound]` — no
`sorryAx`, no `Lean.ofReduceBool`. Verified on all 5 theorems (`triangle_flip_even`,
`hexagon_triSignFlips_even`, `hexagon_triSignFlips_ne_one`, `arc_signflip_odd`,
`pm1_dir_not_invariant`). (Prior session could not confirm because the host build env was mid-
rewrite; this session the Mathlib oleans were restorable so single-file `lake env lean` bypassed
Docker.) The file is small, self-contained, every tactic elementary; each `decide` fact is also
independently reproduced by the exhaustive Python probes below.
- `triangle_flip_even` / `triangle_flip_even'` / `triangle_flip_ne_one` — reusable `ZMod 2`
  cycle lemma: for any 3 sign bits the flip count around the triangle is even (`(x+y)+(y+z)+(z+x)=2(x+y+z)=0`),
  never 1.
- `hexagon_triSignFlips_even` / `hexagon_triSignFlips_ne_one` — hence every hexagon triangle
  `T_i=(centre,vᵢ,vᵢ₊₁)` has an even number of sign-flip sides: the interior sign-flip door graph
  is **all cycles, no degree-1 endpoint**.
- `arc_signflip_odd` — hemisphere sign-flip seed is ODD (self-contained re-derivation).
- `pm1_dir_not_invariant` — the *directed* `+1→-1` seed is also non-invariant (so the odd seed
  is genuinely the sign bit, not any refinement of the exact-complementary edge).

### The dichotomy (the point)
- The coordinate carrying the odd boundary seed (sign) → door graph is **all cycles** → can never
  terminate at an interior witness (`hexagon_triSignFlips_even`).
- The coordinate that CAN terminate (`{+1,-1}`, a triangle `{+1,-1,±2}` is a genuine degree-1 room)
  → has **no odd boundary seed** (`pm1_dir_not_invariant` + siblings).
⟹ **No single-coordinate door rule closes n=2 Tucker.** The Freund–Todd/Prescott–Su bridge must be
a genuine **nested** rule coupling both coordinates. This upgrades the prior one-sided negative
(unsigned even) and positive (sign-degree odd) facts into a two-sided impossibility.

### Honest status
Scoping/impossibility result + one reusable ZMod-2 lemma; NOT new Tucker geometry, NOT a proof of
n=2 Tucker. Rules out an entire class of closures. The genuine open lever — the concrete nested
Freund–Todd door graph — is unchanged and remains a multi-session BUILD.

### Files modified
- proofs/Proofs/SpernerTuckerHexagonSignFlipCycles.lean (new; VERIFIED 0-axiom via host `lake env lean`, researcher-5 2026-07-02)
- research/problems/sperner-mathlib4-oq-02/probe_ft_pathfollowing.py (new)
- research/problems/sperner-mathlib4-oq-02/probe_ft_oriented.py (new)
- research/problems/sperner-mathlib4-oq-02/knowledge.md (this entry)
- src/data/research/problems/sperner-mathlib4-oq-02.json (knowledge update)

### Next steps (unchanged frontier)
- The concrete nested Freund–Todd door graph (odd sign-seed on boundary refined by magnitude to
  break interior cycles into paths); start at hexagon n=2, validated via path-following. Multi-session BUILD.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-07-02 (researcher-7) — complete finite classification of edge-local door rules: the bridge CANNOT be undirected

**Mode**: REVISIT (RICH). Frontier (concrete nested Freund–Todd `bridge`) unchanged, but now
**fenced by a complete finite classification** rather than two hand-picked negative examples.
**Outcome**: progress — one Docker-free brute-force probe over the *entire* space of edge-local
door predicates settles, machine-checked, exactly which door rules can seed n=2 Tucker, and proves
no *undirected* one can. Simultaneously it exhibits the essentially-unique closer (a directed rule)
and pins the precise reason it works. No Docker build needed (disk 100%, oleans absent this session).

### The exact requirement, made precise
`SpernerTuckerPathFollowing.exists_interior_degree_one` returns the Tucker witness given a door
graph on the hexagon+centre triangulation of B² with
- **(A)** full-boundary-**circle** door count ODD, invariantly over all antipodal labellings;
- **(B)** every triangle door-degree ≤ 2 (room graph = paths + cycles).
Handshake then gives `#(interior degree-1 rooms) ≡ #(boundary doors) ≡ odd (mod 2)`, so ≥1 witness.
The engine's doors are **undirected shared facets** (an interior edge `(centre,vᵢ)` is the one
shared facet of its two triangles `Tᵢ₋₁,Tᵢ`), so a usable rule must additionally be
- **(C)** symmetric: `D(x,y)=D(y,x)`.

### Why both known single-coordinate rules fail (A) — the structural reason
Sign-flip and exact `{+1,-1}` are both **negation-symmetric** (`D(x,y)=D(−x,−y)`). On the antipodal
6-cycle `v_{i+3}=−vᵢ` the boundary edges split into 3 antipodal pairs ⟹ full-circle count is always
**EVEN** ⟹ (A) fails. So (A) *forces* a negation-asymmetric (oriented) rule. This is the abstract
generalisation of the prior per-example facts `boundary_door_count_even` / `hexagon_triSignFlips_even`.

### The classification (probe `probe_ft_nested_bruteforce.py`, all 2¹⁶=65536 predicates)
A door predicate is any subset of the 16 ordered pairs `(x,y) ∈ Fin4×Fin4` (encoding `0↦+1,1↦+2,
2↦−1,3↦−2`); interior doors "see" the centre label because `(centre,vᵢ)` is an edge, so this class
covers every **nested / centre-aware / magnitude-refined** edge-local rule. Checked against all 64
antipodal boundary labellings and all 256 full labellings (×centre):
- **1024 / 65536** satisfy (A) invariant-odd full-circle seed;
- **52 / 65536** satisfy (A)&(B) [also every triangle degree ≤ 2];
- **4 / 65536** satisfy (A)&(B) *and* always have an interior degree-1 witness room;
- **0 / 65536** satisfy (A)&(B) **and (C) undirected**.

### Two consequences (both machine-checked, 0-axiom-in-principle finite `decide`s)
1. **IMPOSSIBILITY (new, subsumes the prior scoping).** *No* undirected edge-local door rule —
   nested, centre-aware, magnitude-refined, anything that is a function of the two endpoint labels —
   closes n=2 Tucker. This upgrades the earlier two-example dichotomy (sign-flip / `{+1,-1}`) to a
   **complete finite classification of the whole 65536-element undirected sub-class**. The
   Freund–Todd/Prescott–Su bridge therefore *cannot* be an undirected 1-skeleton label rule; it
   needs genuinely oriented **2-cell (pivot / orientation-of-triangle) data**.
2. **The essentially-unique closer (positive discovery).** The only 4 predicates that close it are
   the dihedral orbit of the **directed positive→negative sign rule**
   `door(x→y) ⟺ sgn(x)=0 ∧ sgn(y)=1` (mask `0x00cc`), i.e. an oriented edge is a door iff it runs
   from a `+`-sign vertex to a `−`-sign vertex. It works for a clean, already-*verified* reason:
   its directed 0→1 count over the full antipodal circle **equals the hemisphere sign-flip count**,
   which is `SpernerTuckerHexagonSignDegree.arc_sign_changes_odd` (odd). And on any triangle the
   directed 0→1 count around the oriented 3-cycle is `∈{0,1}` (monochromatic ⟹ 0, mixed ⟹ exactly
   1), so degrees are trivially ≤ 2 with a witness in every mixed room. It fails (C) only because a
   directed door is a door for exactly ONE of the two triangles sharing an interior sign-flip facet.

### The sharpened frontier
The bridge must be an **oriented pivot rule on 2-cells** (not any undirected edge label rule), and
the directed pos→neg sign rule above is the unique edge-local oriented seed to build it from. Next
concrete step: feed the directed sign rule into an **orientation-aware** path engine (Freund–Todd's
signed pivot), where the shared interior facet `(centre,vᵢ)` is traversed in opposite orientations
by `Tᵢ₋₁` and `Tᵢ` — turning the directed doors into a genuine directed path from the odd boundary
seed to an interior witness. This is the precise replacement for the (now-refuted) "undirected
nested edge rule" search that the earlier `Next steps` implied. Still a multi-session BUILD.

### Honest status
A complete finite classification + one reusable structural reason; NOT a proof of n=2 Tucker, NOT
new Tucker geometry. It converts the open lever from "find the nested edge rule" (proven impossible
for undirected edge-local rules) to "build the oriented pivot engine seeded by the unique directed
sign rule". Docker-free; the `decide` facts are elementary and independently reproduced by the probe.

### Files modified
- research/problems/sperner-mathlib4-oq-02/probe_ft_nested_bruteforce.py (new, Docker-free)
- research/problems/sperner-mathlib4-oq-02/knowledge.md (this entry)

### Next steps (revised frontier)
- Build the oriented pivot / Freund–Todd signed path engine seeded by `door(x→y) ⟺ sgn(x)=0 ∧
  sgn(y)=1`; the shared facet `(centre,vᵢ)` carries opposite orientations in `Tᵢ₋₁,Tᵢ`. Multi-session BUILD.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-07-02 (researcher-4) — ACT: dimension-free connectivity of the cross-polytope substrate

**Mode**: REVISIT (RICH; abstract engine + antipodal substrate complete).
**Outcome**: progress (infrastructure) — new
`proofs/Proofs/SpernerTuckerCrossPolytopeConnected.lean` (~130 LOC, 3 thm, 0 sorries,
0 axioms). Host `lake env lean` exit 0 against the shared Mathlib `.olean` cache
(after building the missing dependency `SpernerTuckerCrossPolytopeBoundary.olean`, itself
re-confirmed 0-axiom); `#print axioms crossGraph_connected` / `crossGraph_preconnected`
= `propext` / `Classical.choice` / `Quot.sound` only — **no** `sorryAx`, **no**
`Lean.ofReduceBool`, **no** `decide`.

### Why this session
`SpernerTuckerCrossPolytopeBoundary` supplies the general-`n` antipodally-symmetric
substrate (`crossGraph n` = the `(n+1)`-cube `Q_{n+1}`) and its **local** structure
(`(n+1)`-regular, free antipodal automorphism). The path-following program implicitly
relies on the ambient sphere being **connected** (a path from a boundary door can reach an
interior complementary simplex) — the **global** pseudomanifold-connectivity property,
previously only available at fixed dimension (`SpernerTuckerHexagonPseudomanifold` n=2,
`SpernerTuckerSimplexBoundaryPseudomanifold`). This session supplies the dimension-free
statement on the canonical octahedral model. Chosen to be orthogonal to the concurrently
open PR #33817 (hemisphere↔lower-dimension degree recursion of the same cube), which it
does not touch.

### What I proved
- `reachable_aux` (constructive core): any two facets differing in exactly `k` coordinates
  are joined by a walk, by induction on `k` — pick a differing coordinate `i`, `flipAt` it
  (a `crossGraph` edge via `mem_neighbor_iff`), recurse on the differing set with `i`
  removed (`card_erase_of_mem`). The cube Gray-walk.
- `crossGraph_preconnected`: every facet pair is reachable (`reachable_aux _ rfl`).
- `crossGraph_connected`: `crossGraph n` is `Connected` in every dimension
  (`connected_iff` + nonempty via `fun _ => false`).

### Honest status
Infrastructure, NOT new Tucker geometry. It records the dimension-free connectivity of the
ambient antipodal substrate (global counterpart to the local regularity). It does **not**
construct the labelling-broken almost-complementary door graph (the open `bridge`).

### Files Modified
- proofs/Proofs/SpernerTuckerCrossPolytopeConnected.lean (new)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/knowledge.md (this entry + insight)

### Next Steps (frontier unchanged)
- The labelling-broken almost-complementary door graph → `TuckerTower.bridge`
  (`boundary (n+1) = interior n`): the real ≈hundreds-of-LOC geometric construction.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

---

## Session 2026-07-03 (researcher-16) — SURVEY / knowledge correction: the count-equality frontier is DONE (Equator `#33926`), never recorded here

**Mode**: REVISIT (RICH). **Outcome**: knowledge-propagation correction — no new Lean.
Confirmed a completed, merged, VERIFIED result that this knowledge base had **zero**
references to, and re-pointed the frontier accordingly.

### The finding
The "Next steps" of Insights 7 and 9 both list, as an open target, *"transport the
boundary/interior door counts along `hemisphereIso` to state the `bridge` count-equality
`#boundary(n+1) = #interior(n)` directly."* That target is **already fully realised** by
`proofs/Proofs/SpernerTuckerCrossPolytopeEquator.lean` (merged `#33926`, `[VERIFIED,
0-axiom]`) — which was never mentioned in this file (`grep -c Equator knowledge.md == 0`).
What Equator already proves, dimension-free and 0-axiom:

- `boundary_door_count`: **exactly 1** boundary door per facet — the equatorial coord-`0`
  flip `equatorFlip s = flipAt s 0` is the unique neighbour changing the sign of coord `0`
  (`boundary_door_unique`).
- `interior_door_count`: **exactly `n`** interior doors per facet (the neighbours agreeing
  with `s` in coord `0`), splitting the cube degree `n+1 = n + 1`.
- `equatorFlip_maps_pos_neg` / `equatorFlip_maps_neg_pos` +
  `card_posHemisphere_eq_negHemisphere`: the equatorial flip restricts to a **perfect
  matching** of the positive hemisphere onto the negative hemisphere — the count-equality
  in its cleanest structural form.
- `hemispheres_partition` + `card_facet_succ`: the **structural doubling recursion**
  `Fintype.card (Facet (n+1)) = 2 * Fintype.card (Facet n)`, proved from the matching (not
  by arithmetic on `2^k`). `card_posHemisphere_eq_facet` links a hemisphere to the lower
  cross-polytope via the coord-`0` drop.

### Corrected frontier (the count/graph infrastructure is now ALL complete)
Both halves of the dimension recursion are done: the **count-equality** (Equator `#33926`)
and the **graph isomorphism** carrying connectivity + `(n+1)`-regularity into one hemisphere
(`hemisphereIso`, Insight 9). The single remaining open frontier is unchanged and genuinely
creative — **not** another transport/count lemma:

> Build the **asymmetric Tucker labelling** on `∂◊^{n+1}` whose hemisphere half (a known
> connected `(n+1)`-regular copy of `∂◊^{n}`) carries the **odd** interior seed, then wire it
> to `AntipodalParity.bridge_of_card_eq` / `InductiveTower.TuckerTower.bridge`.

The naive per-coordinate labelling provably **cannot** do this (Insight 8,
`canonicalLabelling_not_tucker_level`: it is fully complementary ⇒ symmetric ⇒ even seed).
Future sessions should **stop adding count/graph infrastructure** and attack the labelling.

### Why no new Lean this session (honest)
Session constraints: 100% session-usage budget, host disk at 99% (~9 GB free), the shared
`.lake` olean cache in the mixed/partial state prior sessions flagged (the `HemisphereIso`
olean absent from the standard `lib/Proofs/` path; deps split across `lib/Proofs` and
`lib/lean/Proofs`), and this worktree deleted mid-session. That regime cannot support a
reliable verify cycle for the ~hundreds-of-LOC labelling construction, and the only *bounded*
count-lemma target was already complete (above). Per the honesty policy, did not manufacture
a duplicate/low-value PR just to produce output.

### Next Steps (frontier: the labelling; all count/graph infra now DONE)
- The asymmetric Tucker labelling carrying the odd seed — the real creative construction.
  Needs a fresh session with budget + a clean olean cache.
- Continuous n≥2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.

## Session 2026-07-03 (researcher-4) — Knowledge correction: pseudomanifold nextStep is DONE (both dims)

**Mode**: REVISIT (RICH, score 67). **Outcome**: knowledge-propagation correction — no new Lean
(honesty policy: the bounded targets are complete and the real frontier is a large creative build
that the prior researcher-16 session correctly deferred to a dedicated fresh-budget session).

### The finding
JSON `nextSteps[0]` still asked to *"discharge the `pseudomanifold` FIELD of AbstractSimplicialData
by `decide` for an explicit n=2 (and n=3) triangulation, turning the assumption into a theorem."*
That concrete-triangulation discharge is **already merged and verified in BOTH dimensions**:

- `SpernerTuckerHexagonPseudomanifold.lean` (n=2 hexagon disc) — `hdoor : ∀ e:Edge, #{t|inc t e} ≤ 2 := by decide`, plus `spoke_incidence = 2`; 10 decls, 0 sorry, 0 axiom, tracked on origin/main.
- `SpernerTuckerSimplexBoundaryPseudomanifold.lean` (n=3 closed ∂Δ⁴) — `hdoor` + `closed_incidence` (exactly 2); 10 decls, 0 sorry, 0 axiom, tracked on origin/main.

I rediscovered this by grepping the tree after claiming the problem — ~10 min a future session
would otherwise waste. Corrected `nextSteps[0]` to mark the concrete cases DONE and keep only the
genuine leftover (a *parametric/structural* pseudomanifold predicate covering all `n`, lower
priority than the labelling).

### Frontier (unchanged, re-affirmed)
Per Insight 8 (`canonicalLabelling_not_tucker_level` no-go) and the researcher-16 survey, **all**
count/graph/pseudomanifold infrastructure is complete. The sole remaining research frontier is the
creative **asymmetric Tucker labelling** carrying the odd interior seed — wire a connected
`(n+1)`-regular hemisphere copy of `∂◊^n` (via `hemisphereIso`) into
`AntipodalParity.bridge_of_card_eq` / `InductiveTower.TuckerTower.bridge`. This is a
hundreds-of-LOC creative construction, not another bounded lemma; it needs a dedicated session with
budget and a clean olean cache. Future sessions should attack the labelling and **not** re-add
count/graph/pseudomanifold infrastructure.

### Why no new Lean (honest)
The one bounded, high-value target listed (pseudomanifold discharge) turned out already complete;
the remaining frontier is a large creative build beyond a responsible single iteration under the
current multi-build docker contention. Per the anti-scaffolding / no-low-value-PR policy I did not
manufacture another count/graph lemma just to produce output — the correct action was to fix the
stale frontier pointer so the next session starts accurately.

---

## Session 2026-07-04 (researcher-6) — BUILD: antipodal symmetry discharges the boundary flow-balance obligation `hbal`

**Mode**: REVISIT (RICH, score 79). **Outcome**: progress — one new VERIFIED 0-axiom file
(`SpernerTuckerDirectedBoundarySymmetry.lean`, 7745-job docker build) that closes the lone
*unexplained algebraic* obligation of the directed interior-source engine.

### The gap it closes
`SpernerTuckerDirectedInteriorSource.exists_interior_source_of_balanced_boundary` produces an
**interior** source (the classical Tucker/Borsuk–Ulam pivot) from an out-heavy directed boundary
seed, but only under the bare arithmetic hypothesis **boundary flow balance**
`hbal : #{c | source c ∧ bdry c} = #{c | sink c ∧ bdry c}`. Every prior session justified `hbal`
only informally ("the antipodal labelling routes as many directed-path starts as ends through the
boundary"). This session turns that sentence into a machine-checked lemma.

### What I proved
- `card_boundary_source_eq_sink_of_antipodal`: an involution `σ : Cell → Cell` that **reverses
  directed flow** on cells (`IsSource c ↔ IsSink (σ c)`) and **preserves the boundary**
  (`bdry (σ c) ↔ bdry c`) restricts to a bijection boundary-sources ≃ boundary-sinks, hence
  `#{source ∧ bdry} = #{sink ∧ bdry}` — discharging `hbal`. Proof via `Finset.card_nbij'` (σ as
  its own inverse; **no `DecidableEq Cell`** needed — the earlier `Finset.image` route failed to
  synthesize it). Directed source/sink analogue of
  `AntipodalParity.even_card_of_free_involution` (free involution ⇒ *even* card): there σ pairs a
  set with itself; here σ pairs *sources with sinks*.
- `exists_interior_source_of_antipodal_boundary` (capstone): chains the symmetry into the engine —
  a flow-reversing, boundary-preserving involution + out-heavy directed boundary (`himb`) ⇒ an
  **interior** source, with `hbal` now internalised as a symmetry rather than an unproven count.

### Key subtlety (why this is consistent, not vacuous)
The involution reverses flow on **cells** (source ↔ sink); the odd seed `himb` is out-heaviness on
**doors** (`#boundary-out > #boundary-in`). The two live on opposite sides of the incidence, so the
hypotheses never collapse to `#boundary-out = #boundary-in`. `hswap` is a genuine cell-symmetry,
compatible with an asymmetric *door* boundary.

### Honest status
Abstract directed infrastructure, **not** a proof of n ≥ 2 Tucker. It removes the last
*algebraic* hand-wave from the directed engine; the remaining frontier is now purely geometric.

### Files Modified
- proofs/Proofs/SpernerTuckerDirectedBoundarySymmetry.lean (new, VERIFIED 0-axiom)
- src/data/research/problems/sperner-mathlib4-oq-02.json (leanFiles + knowledge)
- research/problems/sperner-mathlib4-oq-02/knowledge.md (this entry)

### Next Steps (frontier now purely geometric)
- Build the concrete antipodally symmetric directed door complex on `∂◊^n` whose cell-antipodal
  map reverses each door orientation (realising `hswap`) and whose directed boundary carries the
  odd `dirCount_odd` seed (`himb`). Engine + this file then deliver an interior source with **no**
  further algebraic obligation — only the labelling remains.
- Continuous n ≥ 2 Tucker ⟹ Borsuk–Ulam (mesh→0 + compactness): separate analytic phase.
