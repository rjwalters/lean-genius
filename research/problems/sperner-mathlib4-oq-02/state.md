# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-30T17:30:00-07:00
**Iteration**: 13

## Iteration 13 addition (researcher-1, verified 0-axiom — `lake env lean`, Docker down)
Completed the dimension-free `hpair` of `proofs/Proofs/SpernerTuckerSimplexBoundaryPseudomanifold.lean`
(146 → 193 lines). The file had generalized the closed-pseudomanifold inputs `hdoor`/
`closed_incidence` of `∂Δ^{n+1}` to all dimensions (`boundary_simplex_closed_incidence`,
exact incidence `2`) but left the **pair bound `hpair` pinned to `n = 3` by `decide`**. Now
dimension-free, sharpened to an equality:

- `boundary_simplex_shared_door : i ≠ j → #{d | #d = n ∧ d ⊆ univ.erase i ∧ d ⊆ univ.erase j} = 1`
  — two distinct top cells `Sᵢ = univ.erase i`, `Sⱼ = univ.erase j` (the `(n+1)`-subsets of
  the `(n+2)`-vertex set) share *exactly one* door: the unique `n`-set `univ \ {i,j} =
  (univ.erase i).erase j`, which already has exactly `n` vertices, so any `n`-subset of it
  equals it (`eq_of_subset_of_card_le`). The filter-set is literally `{(univ.erase i).erase j}`.
- `boundary_simplex_hpair` — the `≤ 1` corollary (engine `hpair` shape), all `n`.

This finishes the closed-pseudomanifold characterization of `∂Δ^{n+1}` the file began:
`hdoor` (= 2 everywhere) AND `hpair` (unique shared door) now both hold dimension-free, no
per-dimension `decide`. 0 sorries / 0 axioms (`#print axioms` = propext/Classical.choice/
Quot.sound only — NO `native_decide`/`ofReduceBool`). The remaining open frontier is
unchanged and genuinely geometric: the `Odd #{boundary doors}` inductive bridge and the
analytic mesh→0 phase; the abstract door-counting *inputs* `hdoor`/`hsimplex`/`hpair` are
now all discharged for the canonical models.

## Iteration 12 addition (researcher-1, verified 0-axiom — `lake env lean`, Docker down)
Extended `proofs/Proofs/SpernerTuckerSimplexFacetPair.lean` (143 → 184 lines) with the
**dimension-free raw facet count** of a simplex — the structural fact behind the concrete
`hexagon_all_doors` (`= 3` at `n=2`) and tetrahedron (degree `4` at `n=3`):

- `subset_incidence_door_count : #v = n+1 → #{d | inc n v d} = n + 1` — in the canonical
  subset incidence (`inc n v d := #v = n+1 ∧ #d = n ∧ d ⊆ v`), an `(n+1)`-simplex is
  incident to exactly `n+1` facets, its `n`-element subsets (`(n+1).choose n = n+1` via
  `card_powersetCard` + `Nat.choose_succ_self_right`; the filter-set is literally
  `powersetCard n v`). Generalizes `hexagon_all_doors` to every dimension.
- `subset_incidence_three_le_doors : 2 ≤ n → #v = n+1 → 3 ≤ #{d | inc n v d}` — therefore the
  engine's `hsimplex` hypothesis (each simplex borders `≤ 2` doors) is **false** on the raw
  incidence for `n ≥ 2`. This makes precise *why* the Sperner colouring is required:
  `SpernerTuckerDoorLemma.card_doors_le_two` recovers `≤ 2` only after cutting the `n+1` raw
  facets down to the *complementary* doors; `n=1` (`n+1=2`) is the boundary case where the
  raw count already suffices.

0 sorries / 0 axioms (`#print axioms` = propext/Classical.choice/Quot.sound only; verified
host `lean v4.26.0` over the shared main-repo Mathlib `.olean` cache, Docker image build
down with the containerd `meta.db` I/O error). Modest but genuinely missing structural
brick: the cluster had this count only as per-dimension `decide` facts (hexagon `n=2`,
tetrahedron `n=3`), never the dimension-free form. The open frontier is unchanged: the
geometric `hdoor` (pseudomanifold `≤ 2`) and the `Odd #{boundary doors}` inductive bridge.

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
