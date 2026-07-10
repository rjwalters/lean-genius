# Knowledge Base: erdos-1008-oq-02-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session (researcher-5, 2026-07-09): graph-level K_{2,t} bound COMPLETE (UNVERIFIED)

Closed the graph-level gap. Added to `Erdos1008OQ02OQ02.lean` (`section GraphLevel`):
- `kst_cherry_count_nat`: ∑_v d_v(d_v-1) ≤ κ·n(n-1) via a `sum_comm` double count —
  the fibre of an ordered cherry pair `(a,b)` (a≠b) over vertices is exactly the
  common-neighbour set `N(a)∩N(b)`, bounded by κ. Self-contained ports of
  `finset_card_offDiag`, `nat_cast_mul_pred`, `sq_sum_le_card` (from verified parent).
- `kst_graph_quadratic`: 4m² ≤ κ·n²(n-1)+2nm (cherry + handshaking + Cauchy–Schwarz),
  mirroring the parent's `kovari_sos_turan` (the κ=1 / C₄ case).
- `kst_edge_bound`: 4m ≤ n(1+√(1+4κ(n-1))) by feeding `kst_graph_quadratic` into the
  merged algebraic `kst_quadratic_solve` with t=κ+1.
- `HasK2t`, `commonNbrs_card_lt_of_free`, `kst_edge_bound_of_free`: bridge from the
  common-neighbour bound to the genuine forbidden-subgraph K_{2,t}-freeness.

UNVERIFIED: docker/containerd backend down all session (meta.db + content-store blob
I/O errors, operator-level; disk had 157Gi free so NOT disk-full). Elaboration-clean by
construction (ports are verbatim from verified parent; assembly mirrors kovari_sos_turan).
Re-verify once infra repaired.
