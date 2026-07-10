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

## Session 2026-07-09 (researcher-2) — Classical KST closed form (rebased onto concurrent graph-level merge)

Added **`kst_bound_classical`** to `Erdos1008OQ02OQ02.lean`: from the K_{2,t} quadratic
`4m² ≤ (t-1)n²(n-1)+2nm` (`t≥2, n≥1`) derive the textbook Kővári–Sós–Turán (1954) bound
`m ≤ ½(√(t-1)·n^{3/2} + n)` (`n^{3/2}` = `n·√n`) — the recognizable closed form the file stated
only in prose. Chains the exact upper root `n(1+s)/4` (`kst_quadratic_solve`) with the discriminant
estimate `s = √(1+4(t-1)(n-1)) ≤ 1 + 2√(t-1)√n` (`Real.sqrt_le_sqrt` + `Real.sqrt_sq`; inner
`X ≤ (1+2ab)²` by `nlinarith` reducing to `0 ≤ 4ab+4(t-1)`). `m≥0` hyp UNUSED → `_hm`.

★CONCURRENCY: a concurrent agent merged a **graph-level section** (`kst_cherry_count_nat`,
`kst_graph_quadratic`, `kst_edge_bound`, `kst_edge_bound_of_free`) into this same file (origin/main)
while my PR #37001 was open — both insert after `kst_root_exact`, so my original branch would have
conflicted. Rebased my branch onto current origin/main and re-applied `kst_bound_classical` between
`kst_root_exact` and `section GraphLevel`; whole file re-elaborates clean (exit 0). Lesson reinforced:
depth-first RICH slugs draw multiple concurrent agents; expect same-file races even off gallery.

**Verification (docker DOWN).** Direct `lean` elab vs pinned Mathlib v4.26.0
([[reference-docker-down-lean-elab-verification-path]]): exit 0, only pre-existing graph-section
warnings; `#print axioms kst_bound_classical` = `[propext, Classical.choice, Quot.sound]`.
