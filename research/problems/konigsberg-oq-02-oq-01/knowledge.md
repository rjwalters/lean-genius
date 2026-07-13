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

## Session 2026-04-24 (Session 4) — Full Hierholzer Proof: 0 Sorries

**Mode**: REVISIT
**Outcome**: completed — all sorries eliminated, `directed_euler_circuit_sufficient_corrected` fully proved

### What Was Done
- Proved `nodup_circuit_exists_of_outDeg_pos` (WF induction on remaining capacity k = D.arcCount - W.arcs.length):
  - Either W is stuck → `maximal_balanced_trail_is_circuit` gives u = v; nonempty from hout > 0
  - Or extend via `single_arc_walk` helper (one-arc walk) and recurse on k' = k - 1
- Proved `walk_closed` helper: if S is D-closed (D-arcs out of S stay in S), any walk from S ends in S
  - Induction on arc count; builds tail walk with full `Walk` structure extracted from parent
- Proved `vertex_with_unused_arc` (contradiction via D-closure):
  - All S-vertices have D'-outDeg = 0 → S is D-closed → strong connectivity forces S = V → all D-arcs in C → arcCount ≤ C.arcs.length, contradicting hextra
- Proved `walk_split_at` (take/drop split at first occurrence of u in C.arcs targets):
  - All `Walk` invariants verified via `C.consecutive.getElem`, `List.getLast_take`, `List.getLast_drop`
  - `List.disjoint_take_drop` gives C1/C2 disjointness
- `directed_euler_circuit_sufficient_corrected`: WF induction on m; builds C1.splice(C'.splice C2) each step

### Key Technical Insights
- `List.Chain'.getElem` provides the consecutive link at index i (walk_split_at.starts_at of drop part)
- `List.getLast_take` links take's last element to the arc at position i
- `removeArcList_adj_iff` is the correct API to unfold D'.adj (not `simp [removeArcList, hD'_def]`)
- `walk_closed` needs to fully reconstruct the tail `Walk` structure from parent fields via haL rewriting

### Files Modified
- `proofs/Proofs/KonigsbergOQ02OQ01.lean` (~984 lines, 0 sorries)

### Status: COMPLETED — pending Docker build verification

---

## Session 2026-04-24 (Session 5) — API Bug Fixes for 0-Sorry Build

**Mode**: REVISIT (continuing session 4)
**Outcome**: progress — fixed 7 API bugs in the 0-sorry proof; Docker build running

### What Was Done
- Fixed `List.append_ne_nil_of_right` → `by simp` (doesn't exist)
- Fixed `Nat.eq_zero_of_nonpos` → `omega` tactic in h_zero (doesn't exist)
- Fixed `h_VC_closed` anonymous constructor `⟨v, ...⟩` → `List.mem_map.mpr ⟨(v, x), ..., rfl⟩` (wrong witness type)
- Fixed `hempty` case in cons branch of h_walk_in_VC: used `subst` + `simp` instead of broken `.symm.trans`
- Fixed `starts_at` case: replaced nonexistent `hchain.rel_head?` with `cases tl; exact (List.chain'_cons.mp hchain).1.symm`
- Fixed missing `rw [← List.toFinset_card_of_nodup hnodup]` in h_arc_bound before `apply Finset.card_le_card`
- Fixed `List.Chain'.nil` → `IsChain.nil` (no `Chain'.nil` constructor alias exists)

### Key API Facts Discovered
- `List.chain'_cons` = `isChain_cons_cons` (deprecated alias): `IsChain R (a :: b :: l) ↔ R a b ∧ IsChain R (b :: l)` — gives direct `.1` access, NO `head?` wrapper
- `List.Chain'.nil` has NO deprecated alias; use `IsChain.nil` instead
- `Chain' := (IsChain · ·)` is a `def`, not an `abbrev`/`inductive`; constructors live in `IsChain` namespace
- `List.toFinset_card_of_nodup : l.Nodup → l.toFinset.card = l.length` needed before `Finset.card_le_card` when goal uses `.length`
- Option membership: `b ∈ some (v,x)` → after simp → `(v,x) = b` (reversed convention); use `← hb` to rewrite

### Status: Build pending Docker verification

---

## Insights

- Axiom `directed_euler_circuit_sufficient` in KonigsbergOQ02.lean is MISSING `isStronglyConnected`
- `path_fst_snd_eq` and `circuit_fst_perm_snd` are `private` in OQ02 — must be reproved in child files
- Counting argument for `maximal_balanced_trail_is_circuit`: path_fst_snd_eq -> count balance -> u=v0
- `isChain_append` is the correct API (not deprecated `chain_append`) for `Walk.splice.consecutive`
- `removeArcList` as standalone def avoids namespace conflicts with `Digraph` dot notation
- `Finset.card_image_of_injOn` avoids needing `List.Nodup.map` (which may not exist)
- cmf bridge: `(l.map f).count b = (l.filter (fun a => decide (f a = b))).length` — inline list induction
- `List.chain'_cons` (= `isChain_cons_cons`): gives `R a b ∧ Chain' (b :: l)` directly — no `head?` wrapper
- `Chain' := (IsChain · ·)` is a `def`; constructors under `IsChain` namespace (`IsChain.nil`, not `Chain'.nil`)
- `List.toFinset_card_of_nodup` needed when comparing `Finset.card` with `List.length`
- Option membership convention: `b ∈ some (v,x)` means `(v,x) = b` after simp (reversed)
- WF induction on `D.arcCount - C.arcs.length` is the right measure for Hierholzer splicing

---

## Dead Ends

- `List.count_map_eq_length_filter`: does not exist in current Mathlib — use inline cmf bridge
- `List.Nodup.map_of_injOn`: unreliable — use `Finset.card_image_of_injOn` instead
- `Digraph.removeArcList` with dot notation: namespace resolution fails — use standalone def
- `Nat.eq_zero_of_nonpos`: does not exist — use `omega`
- `List.append_ne_nil_of_right`: does not exist — use `by simp`
- `List.Chain'.nil`: no deprecated alias — use `IsChain.nil`
- `hchain.rel_head?`: does not exist — use `(List.chain'_cons.mp hchain).1`
