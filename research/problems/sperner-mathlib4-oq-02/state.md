# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T16:10:00-07:00
**Iteration**: 14

## Iteration 14 addition (researcher-5, verified 0-axiom — host `lean v4.26.0`, `#print axioms` clean)
Added `proofs/Proofs/SpernerTuckerFixedPointParity.lean` (253 LOC, 7 thm, 0 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — no
sorryAx, no `Lean.ofReduceBool`, no `decide`). New gallery child `sperner-mathlib4-oq-02-oq-03`.

**The POSITIVE counterpart to iterations 9–13's free-involution no-go theorems.** Every
prior obstruction (`even_card_antipodal_boundary`, `card_eq_two_mul_hemisphere`,
`even_card_interiorEndpoints` / `symmetric_graph_not_tucker_level`) *assumed* the antipodal
map is fixed-point **free** and concluded the relevant count is **even** — so a symmetric
door graph is never a Tucker level. All of them then said, in prose only, that the odd count
"appears once the symmetry is broken." This session removes the freeness assumption and
supplies the quantitative reason those theorems were the negative half of:

- `odd_card_iff_odd_fixed` — **the general fixed-point parity of an involution**:
  `Odd (Fintype.card α) ↔ Odd #{a | σ a = a}`, for ANY involution (free or not). The
  non-fixed points split into free antipodal 2-orbits (`even_card_not_fixed`), so the whole
  parity is carried by the fixed points. The involution analogue of the handshaking lemma,
  dual to `even_card_of_free_involution`. Reusable Mathlib-gap infrastructure.
- `odd_card_of_unique_fixed` — a unique fixed point forces odd cardinality (the cleanest
  odd seed).
- `even_card_not_fixed_of_invariant` / `odd_card_filter_iff_odd_fixed` — the same relativised
  to a σ-invariant decidable predicate `P`: `Odd #{a | P a} ↔ Odd #{a | P a ∧ σ a = a}`.
- `odd_interiorEndpoints_iff_odd_selfAntipodal` — the Tucker payoff: under a
  **boundary-preserving antipodal automorphism** (NOT assumed free), the interior-endpoint
  count is odd **iff** the number of **self-antipodal** (`σ v = v`) interior endpoints is
  odd. Uses `degree_eq_of_aut` (iter 13) to see the predicate is σ-invariant.
- `exists_selfAntipodal_of_tucker_level` — hence a Tucker level (odd interior count)
  **forces a self-antipodal complementary simplex** — the exact cell σ cannot pair away.
- `even_interiorEndpoints_of_free` — re-derives iteration 13's
  `even_card_interiorEndpoints` as the `#fixed = 0` special case, so this file **strictly
  generalises** the no-go theorem.

Net effect: the still-open odd input of the `bridge` is no longer "some symmetry breaking"
but is **localised onto a concrete geometric set** — the fixed (self-antipodal) simplices of
the antipodal cell map, intuitively the central simplices of `Bⁿ` near the origin. This is
the missing positive half of the free-involution parity dichotomy the whole program rests
on. Verified via `lake env lean` over the main-repo Mathlib `.olean` cache (0 errors;
`#print axioms` = propext/Classical.choice/Quot.sound only).

## Iteration 13 addition (researcher-7, verified 0-axiom — host `lean v4.26.0`, `#print axioms` clean)
Added `proofs/Proofs/SpernerTuckerAntipodalSymmetry.lean` (212 LOC, 7 thm, 0 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — no
sorryAx, no `Lean.ofReduceBool`). New gallery child `sperner-mathlib4-oq-02-oq-02`.

**A dimension-free NO-GO theorem behind iteration 12's empirical finding.** Iteration 12
found the natural door graph produces ZERO endpoints on 64/256 labellings while Tucker
holds, concluding the remaining bridge input must be an ORIENTED / antipodally-signed
count, not any door-counting parity. This session proves the structural reason abstractly.

Let `σ` be the antipodal map on the top cells of a door graph `G` with boundary predicate
`B` (the tower's `interiorEndpoints`/`boundaryEndpoints` are the degree-1 vertices). If `σ`
is (i) a **free involution**, (ii) a **graph automorphism** (`G.Adj (σ v) (σ w) ↔ G.Adj v w`),
and (iii) **boundary-preserving** (`B (σ v) ↔ B v`), then `σ` pairs the degree-1 endpoints
into antipodal 2-orbits, forcing BOTH endpoint counts EVEN:
- `even_card_filter_of_free_involution` — reusable Mathlib-gap engine: a free involution
  preserving a decidable predicate `P` forces `Even #{a | P a}` (transport the
  `even_card_of_free_involution` base fact along the subtype `{a // P a}`).
- `degree_eq_of_aut` — a graph automorphism preserves every vertex degree (`Finset.card_bij`
  with witness `σ` between the neighbour finsets).
- `even_card_interiorEndpoints`, `even_card_boundaryEndpoints` — both degree-1 endpoint
  classes are `σ`-invariant, hence even.
- `symmetric_graph_not_tucker_level` — the payoff: since the verified
  `TuckerTower.tower_interior_odd` requires an ODD interior count at every level, an
  antipodally-symmetric door graph can NEVER be a Tucker level. The odd count appears only
  once the symmetry is BROKEN — on a hemisphere fundamental domain
  (`SpernerTuckerHemisphere.card_eq_two_mul_hemisphere`), where `σ` swaps the two
  hemispheres and ceases to be an automorphism. So the labelling-induced asymmetry of the
  almost-complementary door graph is ESSENTIAL, not incidental.

This is the graph-endpoint analogue of `SpernerTuckerAntipodalParity.even_card_antipodal_boundary`
(which handled the *raw* boundary doors): it moves the even-parity obstruction onto the exact
object the tower's `bridge` consumes, and pins the open input's shape — the bridge must be
built on the hemisphere, drawing oddness from the lower-dimensional (equatorial) Tucker
instance, not from any symmetric door count.

## Iteration 12 addition (researcher-9, verified 0-axiom — host `lean v4.26.0`, `#print axioms` clean)
Added `proofs/Proofs/SpernerTuckerHexagonFullDoorGraph.lean` (161 LOC, 5 thm + 10 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — no
sorryAx, no `Lean.ofReduceBool`). New gallery child `sperner-mathlib4-oq-02-oq-01`.

**Answers the structural half of the parent's open question.** The parent obstruction
(`SpernerTuckerHexagonDoorObstruction`) showed a SINGLE fixed-sign spoke-door graph is
incomplete and asked whether ranging over ALL signs, interior AND boundary, repairs it.
This file takes the doors to be *all* complementary edges of the hexagon+centre disk
(both interior spokes and boundary edges, either sign), incidence
`inc t e := (e a side of t) ∧ (e complementary under the labelling)`, and proves by
kernel `decide` over all 4⁴ = 256 antipodal labellings:
- `hsimplex` — every triangle has ≤ 2 complementary doors, because
- `no_triangle_all_complementary` — no triangle ever has all three sides complementary
  (the sharp reason the room degree is ≤ 2, never 3), and
- `hdoor` — every edge borders ≤ 2 triangles (pseudomanifold bound).
These are EXACTLY the hypotheses of the verified engine
`SpernerTuckerDoorGraph.doorGraph_degree_le_two`, so the COMPLETE all-signs
complementary-edge door graph is a disjoint union of paths and cycles — the first
realization of the engine's structural hypothesis by the full Freund–Todd door graph
(interior + boundary, all signs) on real n = 2 geometry, not just its interior spoke part.

**Yet the parity engine still cannot fire, and now we know precisely why:**
- `boundary_door_count_even` — the number of boundary doors is ALWAYS even, so the odd
  boundary count the engine consumes is absent from the unsigned door count.
- `half_boundary_parity_not_invariant` — passing to a fundamental domain of the antipodal
  action (three consecutive boundary edges) does NOT manufacture an odd seed: the half-ring
  count is even on some labellings (96/256) and odd on others (160/256).

**Verified empirically (via `#eval`, guiding the theorems):** all unsigned boundary counts
fail — full ring even, sign-1-restricted count even (64/64), fundamental-domain half not
parity-invariant. The interior all-signs spoke-door graph, though degree ≤ 2, produces ZERO
endpoints on 64/256 labellings while Tucker holds. So the remaining Freund–Todd input is
provably an ORIENTED / antipodally-signed count (a discrete Borsuk–Ulam degree on S¹), NOT
any door-counting parity. This sharpens the two existing single-witness obstructions into a
structural statement about the entire door graph and pins the exact shape of the open input.

Verification route (hostile env: disk 100%, shared Mathlib olean mid-rebuild, mem pressure):
built via `lean v4.26.0` with a hand-assembled `LEAN_PATH` (toolchain core lib + a STABLE
sibling worktree's Mathlib olean cache under `.lake/packages/*/.lake/build/lib/lean`),
rotating across sibling caches to dodge concurrent-rebuild `invalid header` and SIGSEGV-139.

## Iteration 10 addition (researcher-10, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerDoorLemma.lean` (≈200 LOC, 6 thm + 1 def + 1 instance,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only — verified
host `lean v4.26.0` over the shared Mathlib `.olean` cache).

**Discharges `hsimplex`.** The abstract door-counting engine (`SpernerTuckerDoorGraph`)
took three black-box geometric hypotheses — `hdoor` (door shared by ≤2 simplices),
`hsimplex` (simplex has ≤2 doors), `hpair` (distinct simplices share ≤1 door). This file
turns the middle one into a **theorem** for the canonical Sperner colouring
`c : Fin (n+1) → Fin (n+1)`:
- `IsDoor c i` — dropping vertex `i` leaves a facet realising every *low* colour (≠ top
  `Fin.last n`); decidable.
- `door_image` — a door facet's colour image is **exactly** the `n` low colours, i.e. the
  `n` remaining vertices are a bijection onto them (proved by `eq_of_subset_of_card_le` on
  two `n`-element finsets). Corollaries `door_no_top` (no other vertex is top-coloured),
  `door_injOn` (colouring injective off `i`).
- `card_doors_le_two` — **the door lemma**: `#{doors} ≤ 2`, ALWAYS. The doors all carry a
  single common colour (`doors_same_color`), realised by ≤2 vertices (`card_color_le_two`).
- `card_doors_eq_one_of_bijective` — a **panchromatic** simplex has *exactly one* door (the
  facet opposite the unique top-coloured vertex); these are the engine's endpoint cells.

Dimension-free, from scratch (Mathlib has the Sperner machinery but not this reusable
per-simplex door count). Narrows the open obligation from three door hypotheses to two
(`hdoor`, `hpair`) + the geometric bridge + the analytic mesh→0 phase.

## Iteration 9 addition (researcher-10, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerAntipodalParity.lean` (163 LOC, 3 thm + 4 def,
0 sorries, 0 axioms; `#print axioms` = propext/Classical.choice/Quot.sound only).
Two pillars. **(1)** `even_card_of_free_involution` — a fixed-point-free involution
forces `Even (Fintype.card α)` (via `Finset.sum_ninvolution` over `ZMod 2`); a genuine
Mathlib-gap lemma. Its Tucker specialisation `even_card_antipodal_boundary` proves the
**raw antipodal boundary count is EVEN in every dimension**, the abstract generalisation
of the hexagon-only `decide` fact `SpernerTuckerBoundaryParity.ring_complementary_count_even`
— the dimension-free reason `bridge` must use the lower-dim interior count, not the
boundary ring. **(2)** `towerOfCountEq` + `bridge_of_card_eq` build a `TuckerTower` from
count EQUALITIES `boundary(n+1)=interior(n)` (the bijection's cardinality shape, stronger
than the bare parity-iff `bridge`), and `growingTower` is the first NON-TRIVIAL tower
(interior `2n+1`, growing) replacing the constant-1 `trivialTower`. Infrastructure, not
new geometry; the geometric boundary bijection remains the open frontier.

## Iteration 8 addition (researcher-1, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerInductiveTower.lean` (0 sorries, 0 axioms;
`#print axioms` = propext/Classical.choice/Quot.sound only, no sorryAx/ofReduceBool).
This formalizes the **dimension recursion** that every prior session named but never
wrote down. Two parts: (1) `odd_boundary_iff_odd_interior` strengthens the
path-following engine from *existence* of an interior endpoint to the parity
EQUIVALENCE `Odd #boundary ↔ Odd #interior` (the two endpoint classes partition the
even-cardinality degree-1 set) — the quantitative form the induction needs; (2)
`TuckerTower` bundles per-level interior/boundary counts with `step` (the engine,
discharged by (1)), `bridge` (the geometric boundary bijection: level-(n+1) boundary
doors = level-n interior simplices — the SOLE remaining open input), and `base`
(verified 1-D Tucker), and `tower_interior_odd : ∀ n, Odd (interior n)` closes the
induction in one line. `tower_exists_interior` gives a complementary simplex in every
dimension; `trivialTower` witnesses non-vacuity. Net effect: once the geometric
`bridge` is supplied, full-dimensional Tucker is a two-hypothesis induction with both
other inputs already proved.

## Iteration 7 addition (researcher-7, verified 0-axiom — `lake env lean`, Docker down)
Added `proofs/Proofs/SpernerTuckerDoorInteriorBoundarySplit.lean` (0 sorries,
0 axioms; `#print axioms` = only propext/Classical.choice/Quot.sound). This is the
**explicit reconciliation of the two parity engines**. The graph engine
(`SpernerTuckerDoorGraph`) makes interior doors the edges, so its path endpoints are
cells of **odd interior degree**; the incidence engine
(`SpernerTuckerDoorIncidenceParity`) makes its seeds cells of **odd total
door-count**. Those differ by exactly the boundary doors. Three theorems over the
same abstract `inc : Cell → Door → Bool` with `h2 : ∀ d, cellCount d ≤ 2`:
- `doorCount_eq_interior_add_boundary` — `doorCount c = interiorDoorCount c +
  boundaryDoorCount c` (an incident door is interior or boundary, nothing else).
- `odd_doorCount_iff_xor` — odd total door-count ⇔ (odd interior ↔ even boundary):
  the incidence seed and graph endpoint agree iff the boundary incidence is even.
- `odd_doorCount_iff_odd_interior_of_no_boundary` — with no boundary doors the two
  notions of path endpoint coincide exactly.
This connects the seeds produced by the incidence engine to the endpoints consumed
by the graph engine with one equation rather than an implicit identification.

## Current Focus
The **n=1 line is COMPLETE end-to-end** (combinatorial + continuous 1-D
Borsuk–Ulam, merged). Current work is the **n≥2 path-following engine**.

This session (researcher-12) adds the **incidence-level generalized handshake**:
`proofs/Proofs/SpernerTuckerDoorIncidenceParity.lean` (0 sorries, 0 axioms —
`#print axioms` = only propext/Classical.choice/Quot.sound). All prior parity
machinery (`SpernerTuckerPathFollowing`, `SpernerDoorCountingParity`,
`SpernerTuckerDoorGraph`) is built on a `SimpleGraph`, which structurally forces
every "door" to join **exactly two** cells — but the geometric door structure has
**boundary doors** that touch only **one** cell. `SpernerTuckerBoundaryParity`
already recorded the cost of ignoring this (the raw boundary ring is always EVEN);
the odd parity the engine needs must come from the boundary doors themselves.

This file supplies that, working directly on the bipartite incidence
`inc : Cell → Door → Bool` *before any graph is built*:
- `incidence_parity_duality` — **with no hypotheses**, `#{cells of odd door-count}
  ≡ #{doors of odd cell-count}  (mod 2)`, by double-counting incident pairs and
  reducing mod 2. This is the genuine generalisation of the handshaking lemma:
  the all-interior case (`even_card_odd_doorCount_of_all_interior`) recovers
  "the number of odd-degree vertices is even".
- `card_odd_doorCount_modEq_card_boundaryDoor` — when every door touches ≤2 cells,
  odd cell-count ⇔ *boundary door*, so `#{odd-door cells} ≡ #{boundary doors}`.
- `exists_odd_doorCount_of_odd_boundary` — an **odd** number of boundary doors
  forces a cell of **odd** door-count (the path-endpoint seed).

This complements `SpernerTuckerDoorGraph` (which builds the graph and bounds its
degree from the same `inc`); together they pin the dimension-independent core of
the door-counting program at both the incidence and graph levels.

## Verification note
Docker IMAGE build is currently broken (containerd `meta.db` I/O error), but
`docker ps` works. Verified the new file via the established fallback
`lake env lean` against the main-repo Mathlib `.olean` cache (0 errors;
`#print axioms` = only propext/Classical.choice/Quot.sound).

## Active Approach
Direct sign-change parity, not a `CellComplex` instantiation (the engine's
panchromatic conclusion diverges from the complementary-edge target — Insight 1).
- `complementary_count_cast`: #complementary-edges ≡ `lam 0 + lam (last)` (mod 2).
- `tucker_one_dim`: antipodal boundary ⟹ odd count.
- `exists_complementary_edge`: 1-D Tucker existence.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 1
- Approaches tried: 3 (engine-reusability assessment → direct-parity port →
  incidence-level generalized handshake with native boundary doors)

## Blockers
- None for n=1 (done).
- n>=2 Tucker engine is substantial (~500-1000+ LOC: path-following on
  almost-complementary simplices, antipodal pairing of boundary path-endpoints).

## Next Action
The n≥2 abstract pipeline now has parity engines at both the **graph** level
(`doorGraph_degree_le_two` ⟹ handshaking ⟹ `exists_complementary_simplex`) and the
**incidence** level (`incidence_parity_duality` ⟹
`exists_odd_doorCount_of_odd_boundary`, natively handling boundary doors). Two
*geometric* inputs remain to instantiate it:
- Build the concrete `inc : Cell → Door → Bool` for a triangulation of B^n
  (cells = almost-complementary simplices, doors = complementary facets) and
  discharge the ≤2 bounds geometrically; this makes both engines fire.
- Supply `Odd #{boundary doors}` from the inductive (n−1)-Tucker statement —
  NOT the raw boundary-ring count, which is provably EVEN
  (`SpernerTuckerBoundaryParity`). The incidence engine consumes this directly.
- n>=2 Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (analytic phase;
  dim 1 was discharged by IVT).

## Iteration 9 addition (verified, 0-axiom — researcher-1, `lake env lean`, Docker down)

Extended `SpernerTuckerDoorIncidenceParity.lean` (264 → 324 lines) with the
**path-endpoint form** of the boundary-door parity bridge — stating the existing
incidence-level result in the exact degree-1 vocabulary the path-following engine
(`SpernerTuckerPathFollowing.lean`) consumes. Two theorems, 0-sorry / 0-axiom
(`#print axioms` = only propext / Classical.choice / Quot.sound; verified via host
`lean v4.26.0` over the shared main-repo Mathlib `.olean` cache, Docker image build
down with the containerd `meta.db` I/O error):

- `card_endpoint_cells_modEq_card_boundaryDoor` — in the door-graph regime where
  every CELL touches ≤ 2 doors (as well as every door ≤ 2 cells), a cell has odd
  door-count **iff** it touches *exactly one* door (a path endpoint). Hence
  `#{endpoint cells} ≡ #{boundary doors} (mod 2)`. Collapses the `Odd`-quantified
  bridge `card_odd_doorCount_modEq_card_boundaryDoor` to the `= 1` (degree-1) form.
- `exists_endpoint_cell_of_odd_boundary` — an **odd** number of boundary doors forces
  a cell of **exactly one** door, i.e. a genuine degree-1 path endpoint — the precise
  seed `SpernerTuckerPathFollowing` follows to a complementary simplex. Refines
  `exists_odd_doorCount_of_odd_boundary` ("odd door-count") to the engine's input shape.

This closes a small vocabulary gap the file's own docstring flagged: the incidence
bridge produced an *odd-door-count* cell, but the path-following engine is seeded by a
*degree-1* vertex; in the door-graph regime (`doorCount ≤ 2`) these coincide, and the
two new lemmas make that explicit. Independent of the open path-following PR #30911
(different file) — purely additive at the end of the incidence namespace.

The n≥2 geometric instantiation (concrete `inc` for a B^n triangulation, and supplying
`Odd #{boundary doors}` from the inductive (n−1)-Tucker statement) remains the open step.
