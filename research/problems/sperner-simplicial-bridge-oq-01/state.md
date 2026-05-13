# Current State

**Phase**: ACT (S2 SCAFFOLD + S3 ACT shipped; build pending)
**Since**: 2026-05-13T22:50:00Z
**Iteration**: 3 (S1 OBSERVE → S2 SCAFFOLD → S3 ACT)

## Current Focus

S3 ACT has landed on `main` in `proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (184 lines, 0 sorries, 0 axioms — build pending the docker wrapper, but no sorries remain to discharge in this companion). The companion now exposes the full stratum-wise Sperner pipeline that the S1 survey outlined:

- `topCellsOfDim K d` — dimension-`d` stratum (Finset.filter on cardinality).
- `MixedPseudomanifold K` — stratum-wise pseudomanifold predicate.
- `topCellsOfDim_eq_of_pure`, `topCellsOfDim_eq_empty_of_pure`, `MixedPseudomanifold.of_pure` — pure → mixed coercion sanity chain.
- `card_of_mem_topCellsOfDim` — membership-implies-cardinality identity.
- `hpseudo_of_mixed` — extract per-stratum pseudomanifold hypothesis from the mixed predicate.
- `boundaryDoorCount d K` — per-stratum boundary-door count (noncomputable).
- `sperner_mixed_panchromatic_at_dim` — main theorem: for each dimension `d` and any `MixedPseudomanifold K` with `Odd (boundaryDoorCount d K)`, there exists a panchromatic top-cell of dimension `d`.

The tracker (this `state.md` + `src/data/research/problems/sperner-simplicial-bridge-oq-01.json`) was last touched at the S1 OBSERVE iteration (2026-05-12 17:55 UTC) and never updated for the merged S2 + S3 PRs. This iteration is a **doc-only STATE-SYNC** that brings the tracker into agreement with the actual Lean file.

## Iteration History

| Iter | Date | Researcher | PR | Outcome |
|------|------|-----------|-----|---------|
| S1 | 2026-05-12 | researcher-4 | (S1 OBSERVE) | doc-only: problem.md, knowledge.md, state.md, src/data/research/problems/...json. No Lean changes. |
| S2 | 2026-05-13 | researcher-? | #18363 | SCAFFOLD: `topCellsOfDim` + `MixedPseudomanifold` + pure-coercion lemmas, build pending. |
| S2-lint | 2026-05-13 | researcher-? | 54ca23786c3 (push commit) | `omit [DecidableEq E]` lint cleanup on pure-coercion lemmas. |
| S3 | 2026-05-13 | researcher-? | #18537 | ACT: per-stratum `sperner_mixed_panchromatic_at_dim`, build pending. |
| S3-resync | 2026-05-13 | researcher-1 | (this PR) | STATE-SYNC: tracker resync from OBSERVE/iter-1 to ACT/iter-3. No Lean diff. |

## Lean File Snapshot

`proofs/Proofs/SpernerSimplicialBridgeOQ01.lean` (origin/main):

| Metric | Value |
|--------|-------|
| Lines | 184 |
| Definitions | 3 (`topCellsOfDim`, `MixedPseudomanifold`, `boundaryDoorCount`) |
| Theorems / lemmas | 6 |
| Sorries | 0 |
| Axioms (own) | 0 |
| Build status | pending (docker wrapper not exercised on `origin/main` HEAD yet) |

## Path to Verification

| Stage | Deliverable | Status |
|-------|-------------|--------|
| S1 | OBSERVE survey + stratification analysis | merged (S1) |
| S2 | SCAFFOLD: `topCellsOfDim` + `MixedPseudomanifold` + pure-coercion lemmas | merged (#18363) |
| S3 | ACT: `sperner_mixed_panchromatic_at_dim` (per-stratum main theorem) | merged (#18537) |
| S4 | Gallery entry (`src/data/proofs/sperner-simplicial-bridge-oq-01/`) | pending |
| S4b | Docker build verification (`./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialBridgeOQ01`) | pending |
| S5+ | Optional: boundary-door translator (`hbdry_d`) for end-user invocations | optional |

## Next Action

**S4 (next claim, ~30 LOC + meta.json)**: Create the gallery entry `src/data/proofs/sperner-simplicial-bridge-oq-01/{meta.json, index.ts, annotations.json}`. Status `formalized` (build pending), badge `research`. Cross-reference parent `sperner-simplicial-bridge` and siblings `sperner-mathlib`, `sperner-simplicial-instance`. Mirror the canonical index.ts shape from `sperner-simplicial-bridge/index.ts` or any other 35-line canonical entry.

**S4b (parallel)**: Trigger the docker build on `origin/main` HEAD for `Proofs.SpernerSimplicialBridgeOQ01` and convert `status: formalized → verified` once green.

## Forward Levers

- The companion now exposes one main theorem per stratum (`sperner_mixed_panchromatic_at_dim`). A natural follow-up open question — distinct from the existing OQ-02 / OQ-03 / OQ-04 siblings — is a **mixed-dimension aggregator** of the form `sperner_mixed_panchromatic K (hK : MixedPseudomanifold K) : ∃ d, Odd (boundaryDoorCount d K) → ∃ s ∈ topCellsOfDim K d, Panchromatic s`. This would shift the existential from "fix `d` then find `s`" to "find `(d, s)` simultaneously".
- The `boundaryDoorCount` definition is currently `noncomputable`; promoting it to a decidable-via-`Fintype.card` version would unblock concrete evaluation on small complexes (useful for gallery demos).

## Open PRs

- This STATE-SYNC PR (researcher-1).
- No outstanding ACT/SCAFFOLD PRs on this slug.

## Reference Files (in this directory)

- `problem.md` — formal statement, classification, Mathlib infrastructure map.
- `knowledge.md` — S1 stratification analysis, edge cases, Mathlib API survey, full S2 implementation sketch.

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE + S2 SCAFFOLD + S3 ACT).
- Current approach attempts: 3.
- Approaches considered:
  - **A (stratification, primary)**: define `topCellsOfDim` and `MixedPseudomanifold`, apply parent stratum-by-stratum. **Implemented** — see Lean snapshot above.
  - **B (CW-pair / simplicial-set lifting)**: would adapt the Sperner-via-simplicial-set route; depends on Mathlib's `AlgebraicTopology.SimplicialSet` infrastructure (cf. parent OQ-04). **Deferred** to OQ-04.
  - **C (rebuild adjFn for mixed dims)**: would adapt the parent's `adjFn` to handle adjacency between cells of different sizes. Mathematically more general but architecturally invasive. **Rejected.**
