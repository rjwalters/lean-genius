# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T16:10:00-07:00
**Iteration**: 8

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
