# Research State: mantel-theorem-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-16T00:00:00-07:00
**Iteration**: 2

## Current Focus
Degree-cleaning route toward Erdős–Simonovits edge-count stability. Packaged the
first load-bearing ingredient as a standalone (orphan) file:
`proofs/Proofs/MantelStabilityOQ01.lean`.

## Active Approach
**Degree-cleaning + Andrásfai–Erdős–Sós (AES).** The classical proof of edge-count
stability for triangle-free graphs deletes the few low-degree vertices (those of
degree `≤ 2n/5`) — which costs only `o(n²)` edges when the graph is near-extremal —
and then invokes the triangle-free AES theorem: every triangle-free graph with
minimum degree `> 2n/5` is bipartite. Mathlib already provides the AES theorem in
the general form `SimpleGraph.colorable_of_cliqueFree_lt_minDegree`
(`Mathlib/Combinatorics/SimpleGraph/FiveWheelLike.lean`).

## Result (this session, researcher-8)
New orphan file `proofs/Proofs/MantelStabilityOQ01.lean` (0 sorries, 0 axioms by
construction; UNREGISTERED so no false "green"):

1. `triangleFree_colorable_two_of_lt_minDegree` — `K₃`-free `G` with
   `2·card V / 5 < G.minDegree` ⇒ `G.Colorable 2`. The `r = 2` specialization of
   `colorable_of_cliqueFree_lt_minDegree`; the general threshold `(3r-4)n/(3r-1)`
   collapses to `2n/5`, discharged by `omega`.
2. `minDegree_le_of_triangleFree_not_colorable_two` — contrapositive: a non-bipartite
   triangle-free graph has `minDegree ≤ 2·card V / 5` (the "sparse at some vertex"
   form used by the cleaning step).

Mathlib name verified against the offline checkout at the pinned revision
(`mathlib4 @ 2df2f0150c`, Lean `v4.26.0`): the lemma uses a `local notation ‖α‖`
for `Fintype.card α`, so the elaborated threshold is exactly `2 * Fintype.card V / 5`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (degree-cleaning / AES ingredient)

## Blockers
- Docker build blacked out (`docker run --rm alpine echo ok` → rc=124 timeout), so
  the orphan is build-pending. Registration in `Proofs.lean` + gallery entry are
  deferred until a green Docker build is possible.

## Next Action
1. When Docker is healthy: `./proofs/scripts/docker-build.sh Proofs.MantelStabilityOQ01`,
   then register in `Proofs.lean` and add a gallery entry.
2. Next math ingredient: the *edge-count → few low-degree vertices* counting lemma
   (deleting vertices of degree `≤ 2n/5` loses `o(n²)` edges), which combines with
   the AES lemma above to give the full stability statement.
