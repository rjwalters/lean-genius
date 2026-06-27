# Research State: sperner-mathlib4-oq-02

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T15:30:00-07:00
**Iteration**: 5

## Current Focus
The **n=1 line is COMPLETE end-to-end** (combinatorial + continuous 1-D
Borsuk–Ulam, merged). Current work is the **n≥2 path-following engine**.

This session (researcher-6) closes the **door-counting ⟹ max-degree-≤2 gap**:
`proofs/Proofs/SpernerTuckerDoorGraph.lean` (227 LOC, 0 sorries, 0 axioms). The
path-following engine (`SpernerTuckerPathFollowing.lean`) assumed
`∀ v, G.degree v ≤ 2` as a black box; this file **derives** it from the abstract
door-incidence structure `inc : V → D → Prop`: if each almost-complementary
simplex has ≤2 doors and each door joins ≤2 simplices, the shared-door graph
`doorGraph` has max degree ≤2 (`doorGraph_degree_le_two`, proved by a counting
injection — the neighbours of `v` inject into the ≤2 doors of `v`). Chained to
the quantitative Tucker conclusion `tucker_door_count` (odd boundary endpoints ⟹
odd interior complementary simplices) and `exists_complementary_simplex`. This
realizes the OQ title literally — the engine's degree bound comes *from*
door-counting, not as an assumption.

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
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 2 (engine-reusability assessment → direct-parity port)

## Blockers
- None for n=1 (done).
- n>=2 Tucker engine is substantial (~500-1000+ LOC: path-following on
  almost-complementary simplices, antipodal pairing of boundary path-endpoints).

## Next Action
The n≥2 abstract pipeline is now complete: door-incidence ⟹ degree≤2
(`doorGraph_degree_le_two`) ⟹ handshaking ⟹ `exists_complementary_simplex`. Two
*geometric* inputs remain to instantiate it:
- Build the concrete `inc : V → D → Prop` for a triangulation of B^n
  (V = almost-complementary simplices, D = complementary facets/doors) and
  discharge the two ≤2 bounds geometrically.
- Supply `Odd #{boundary endpoints}` from the inductive (n−1)-Tucker statement —
  NOT the raw boundary-ring count, which is provably EVEN
  (`SpernerTuckerBoundaryParity`).
- n>=2 Tucker ⟹ Borsuk–Ulam: continuous mesh→0 + compactness (analytic phase;
  dim 1 was discharged by IVT).
