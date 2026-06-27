# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T16:10:00-07:00
**Iteration**: 6

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
