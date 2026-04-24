# Knowledge Base: konigsberg-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Formalize Hierholzer's algorithm in Lean 4 for the directed Eulerian circuit theorem.
The parent file `KonigsbergOQ02.lean` contains `directed_euler_circuit_sufficient` as an
**axiom with a missing hypothesis** — it lacks `isStronglyConnected`. Without strong
connectivity, two disjoint balanced digraphs form a counterexample.

This file (`KonigsbergOQ02OQ01.lean`) provides the corrected theorem with full infrastructure.

---

## Session 2026-04-24 (Session 2) — Walk.splice and removeArcList Infrastructure

**Outcome**: progress

### What Was Done
- Proved `Walk.splice` (0 sorries): concatenate two walks sharing a vertex
- Proved `Walk.splice_nodup`: splice of arc-disjoint walks is Nodup
- Defined `removeArcList`: residual digraph removing a list of arcs
- Proved `Walk.ofRemoveArcList`: lift residual walk to parent graph
- Left `removeArcList_arcCount` and `removeArcList_balanced` as sorries with proof sketches

### Key Findings
- `isChain_append` (not deprecated `chain_append`) is the correct API for `consecutive` field in `Walk.splice`
- `removeArcList` must be a standalone def (not `Digraph.removeArcList`) to avoid namespace resolution conflicts
- `circuit_fst_perm_snd` gives the key count equality needed for `removeArcList_balanced`

### Files Modified
- `proofs/Proofs/KonigsbergOQ02OQ01.lean` (extended, ~440 lines)

### Next Steps
- Prove `removeArcList_balanced` using cmf bridge + circuit_fst_perm_snd
- Prove `removeArcList_arcCount` using Finset.card_sdiff
- Implement Hierholzer WF induction

---

## Session 2026-04-24 (Session 3) — removeArcList_arcCount and removeArcList_balanced Proved

**Outcome**: progress

### What Was Done
- Proved `removeArcList_arcCount` (0 sorries):
  - Key: residual arc set = D_arcs \ arcs_list.toFinset (via `removeArcList_adj_iff`)
  - `Finset.card_sdiff` + `List.toFinset_card_of_nodup` closes the goal
- Proved `removeArcList_balanced` (0 sorries):
  - Use `Finset.image` to define `A_src`/`A_tgt` (avoids needing nodup of mapped list)
  - `Finset.card_image_of_injOn` proves |image| = |filter| via Prod.snd injectivity on same-fst pairs
  - `cmf` bridge: `(l.map f).count b = (l.filter (decide (f a = b))).length` (inline list induction)
  - `circuit_fst_perm_snd` + `hperm.count_eq v` gives equal per-vertex fst/snd counts
  - Subtract equal amounts from balanced inDeg/outDeg via omega
- Updated summary in the Lean file to reflect proved status

### Key Findings
- `Finset.card_image_of_injOn` is the right tool when you need |image S| = |S| (not `List.Nodup.map`)
- `Chain'` (not `IsChain`) is the correct hypothesis type to match `circuit_fst_perm_snd`
- The cmf pattern appears in KonigsbergOQ02.lean and can be reproved inline identically

### Infrastructure Status After This Session
All building blocks for Hierholzer's algorithm are now proved:
1. `maximal_balanced_trail_is_circuit` (proved)
2. `Walk.splice` (proved)
3. `removeArcList_arcCount` (proved — NEW this session)
4. `removeArcList_balanced` (proved — NEW this session)

Remaining: `directed_euler_circuit_sufficient_corrected` (1 sorry: WF induction)

### Files Modified
- `proofs/Proofs/KonigsbergOQ02OQ01.lean` (removeArcList_arcCount proved, removeArcList_balanced proved)
- `src/data/research/problems/konigsberg-oq-02-oq-01.json` (builtItems, insights, nextSteps updated)

### Next Steps
- Implement WF induction in `directed_euler_circuit_sufficient_corrected`
  using `termination_by` on `D.arcCount` decreasing by circuit length each iteration

---

## Insights

- Axiom `directed_euler_circuit_sufficient` in KonigsbergOQ02.lean is MISSING `isStronglyConnected`
- `path_fst_snd_eq` and `circuit_fst_perm_snd` are `private` in OQ02 — must be reproved in child files
- Counting argument for `maximal_balanced_trail_is_circuit`: path_fst_snd_eq -> count balance -> u=v0
- `isChain_append` is the correct API (not deprecated `chain_append`) for `Walk.splice.consecutive`
- `removeArcList` as standalone def avoids namespace conflicts with `Digraph` dot notation
- `Finset.card_image_of_injOn` avoids needing `List.Nodup.map` (which may not exist)
- cmf bridge: `(l.map f).count b = (l.filter (fun a => decide (f a = b))).length` — inline list induction

---

## Dead Ends

- `List.count_map_eq_length_filter`: does not exist in current Mathlib — use inline cmf bridge
- `List.Nodup.map_of_injOn`: unreliable — use `Finset.card_image_of_injOn` instead
- `Digraph.removeArcList` with dot notation: namespace resolution fails — use standalone def
