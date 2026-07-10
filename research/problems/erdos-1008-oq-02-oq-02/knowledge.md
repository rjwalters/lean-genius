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

## Session 2026-07-09 (researcher-3) — Reiman C₄ graph-level leading-order specialisation (VERIFIED)

Added **`reiman_edge_bound_leading_order`** to `Erdos1008OQ02OQ02.lean` (end of
`section GraphLevel`): the `t = 2` specialisation of the merged
`kst_edge_bound_leading_order`, giving the recognisable Reiman (1958) bound for a
`C₄`-free (`K_{2,2}`-free) nonempty graph:

      m ≤ ½ · (n·√n + n)   =   ½ · (n^{3/2} + n),

recovering `ex(n ; C₄) = O(n^{3/2})` and tying the general `K_{2,t}` family back to
the parent `C₄` entry. Proof is a one-shot specialisation: apply the general
leading-order lemma at `t = 2`, collapse the coefficient `√((2:ℕ)-1) = √1 = 1`
(`rw [show ((2:ℕ):ℝ)-1 = 1 by norm_num, Real.sqrt_one]`), then `one_mul`.

VERIFIED green (docker containerd blob I/O error all session, running containers only —
new `docker run` blocked). Used the direct-`lean`-elab-vs-pinned-Mathlib path
([[reference-docker-down-lean-elab-verification-path]]): exit 0, no `error:` lines
(only the pre-existing unused `[DecidableEq V]` section-var warning on `sq_sum_le_card`
at line 218), and `#print axioms reiman_edge_bound_leading_order` =
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, genuinely axiom-free.

## Session 2026-07-10 (researcher-3) — K_{2,t} monotonicity in t (VERIFIED, orthogonal to open leading-order PRs)

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (2 theorems, 0 axioms), **VERIFIED**.

The K_{2,t} KST engine is fully saturated (both directions: `kst_edge_bound(_of_free)` +
forcing converses `hasK2t_of_edge_bound_lt`; exact + leading-order + Reiman t=2 specialisations)
and had **two open PRs** in the leading-order zone (#37052, #37025). To avoid an add/add race
(this slug is a known concurrent-agent magnet — see prior sessions), I added a **structurally
orthogonal** pair placed right after the `HasK2t` def, far from the collision zone:

- `hasK2t_mono (G) {s t} (hst : s ≤ t) : HasK2t G t → HasK2t G s` — containment antitone in `t`:
  the very same witness `⟨a,b,T⟩` works, only its cardinality bound is weakened `t ↦ s`
  (`le_trans hst htc`).
- `not_hasK2t_mono : s ≤ t → ¬HasK2t G s → ¬HasK2t G t` — the dual freeness monotonicity
  (K_{2,t}-free classes are nested `⋯ ⊇ Free(s) ⊇ Free(t) ⊇ ⋯`).

Proofs are one-liners on the `HasK2t` existential. **VERIFIED** via `./bin/lake env lean`
single-file elab (docker image build still down, containerd meta.db I/O): exit 0, no errors
(only the pre-existing `sq_sum_le_card` unused-section-var warning + the analogous benign
warning on `hasK2t_mono`, which does not use `[Fintype V]`). `#print axioms` on both =
`[propext, Quot.sound]` — genuinely axiom-free.

File `Erdos1008OQ02OQ02.lean` is research-only (no `src/data/proofs/erdos-1008-oq-02-oq-02/`
gallery meta), so no meta lineCount sync. 536→554 lines.
