# Erdős 85: cold-build literal Lean axiom audit (2026-09-27)

Punchlist item B2. SINGLE-SEAT (claude), Sol re-audit pending. This supersedes the preliminary
overlay readout `AXIOM_AUDIT_OVERLAY_20260916.md` as the citation for the manuscript's axiom
statements; the two outputs are byte-identical (sha256 below).

## What was built

A fresh Docker build volume (`lean-e85-cold-20260927`, created 2026-09-27T17:35:13Z) so that
every `Proofs.*` module in the import cone was compiled from source in this run; only the
Mathlib dependency came from the standard `lake exe cache get` (8,560 files). Image: the pinned
`lean4-arm64:v4.31.0` build `sha256:a5ca6c4e3328a1832d5f9b814ab7c1e35616903b3956341962a5b1a96fb6dff6`
(tagged locally `lean4-arm64:v4.31.0-e85pinned`), Lean `4.31.0`, commit
`68218e876d2a38b1985b8590fff244a83c321783`, `aarch64-unknown-linux-gnu`. Limits: 32 GiB memory,
10 CPUs. Source: worktree of `erdos85/integration` at manuscript commit `b98c334cad9`; the last
commit touching `proofs/Proofs` is `b19b8ea7752d3c41bff4494ca0ce040c7e682da7` (2026-09-15).
Target blobs: `Proofs/Erdos85BinarySquareRegularCapstone.lean` = `580930c0d9c900529bf623a752c04b700abebc1a`,
`Proofs/Erdos85FiniteDropWitnesses.lean` = `5b0585c41353b006c2dc74cfaa2813417288227e` (the same blobs
the 2026-09-16 overlay audit recorded).

Command (inside the container, working directory `/workspace/proofs`):

```sh
lake exe cache get && lake build Proofs.Erdos85BinarySquareRegularCapstone Proofs.Erdos85FiniteDropWitnesses
# Build completed successfully (8680 jobs).  START 17:35:13Z  BUILD-OK 17:54:37Z
lake env lean /workspace/research/problems/erdos-85-wip-01/AXIOM_AUDIT_COLD_20260927/axioms.lean
# AXIOMS-RC 0  17:54:41Z
```

Input `axioms.lean` sha256 `f75243048b73c5b4b8eb880bdbc4084f0b0e34955f85f50c83ca9e9d64f32c21`;
output `axioms.out` sha256 `5319237249875a9369e10d91213e9cccf9aa7df18adde8cd80e2e14e61270f6f`
(identical to the 2026-09-16 overlay output). Full build log: Stripe
`artifacts/erdos85-sat49/axiom-audit-cold-20260927/build.log`.

## Literal output

See `axioms.out` beside this file. Summary:

| Statement | Axioms beyond propext, Classical.choice, Quot.sound |
|---|---|
| `Erdos85.not_erdos85Question_of_binarySquareRegularExclusion` (Theorem B) | none |
| `Erdos85.minDegreeForC4_fortyEight_eq_eight_checked` | 3 `native_decide` axioms (boza48Graph, its common-neighbour bound, its degree) |
| `Erdos85.seven_le_minDegreeForC4_fortyNine_checked` | 3 `native_decide` axioms (orderFortyNineDegreeSixGraph, common-neighbour bound, degree) |
| `Erdos85.minDegreeForC4_fortyEight_fortyNine_exact_checked` | the six above |
| `Erdos85.minDegreeForC4_fortyNine_lt_fortyEight_checked` | the three boza48Graph axioms |

Reading: Theorem B is standard-axiom-only. Every finite-witness statement depends on
`native_decide` and is therefore not standard-axiom-only (gallery policy: `axiomatized`). The
`_checked` finite-drop statements still take the order-49 nonexistence hypothesis; nothing here
discharges it.
