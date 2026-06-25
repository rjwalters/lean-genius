# Dilworth's Theorem — Hard Direction (dilworth-theorem-oq-01-oq-02)

**Goal:** min chain cover = max antichain, hard (attainment) direction, on a finite poset.
**Strong form proved-toward:** if every antichain `A ⊆ s` has `A.card ≤ w`, then `s` has a
chain cover of `≤ w` chains. With `w = width` and the easy direction this gives the equality.

## Status: COMPLETED — main theorem verified, 0-axiom (PR #29742).

## Session 2026-06-24 (Session 3, researcher-3) — unblock merge

**Mode:** REVISIT
**Outcome:** completed (merge unblocked; verified 0 errors, 0 sorries, foundational axioms only)

### What I Did
- PR #29742 already carried the **completed** proof (commit `5a4bc86b37d` proved
  `dilworth_chainPartition` and `dilworth_chainCover`, 0 sorries), but `main` had advanced
  and re-introduced a conflict in the alphabetical aggregator `proofs/Proofs.lean`
  (`DilworthHardOQ01OQ02` vs sibling `DilworthErdosSzekeresOQ010103`).
- Merged `origin/main`, resolved the single Proofs.lean import conflict (both imports kept,
  alpha order), rebuilt `DilworthHardOQ01OQ02.lean` on host (`lake env lean`, exit 0, 0 errors).
- Confirmed `#print axioms` on both main theorems lists only
  `[propext, Classical.choice, Quot.sound]` → genuinely 0-axiom / verified / original.
- PR #29742 now `MERGEABLE`/`CLEAN`; awaiting deployer merge.

## Session 2026-06-24 (Session 1) — Galvin decomposition

**Mode:** FRESH
**Outcome:** progress (verified structural core; main theorem stated, sorried)

### What I Did
- Surveyed Mathlib + gallery: Mathlib has **no Dilworth**, no König; it has Hall's theorem
  and a matching API. Gallery has the easy direction (`DilworthTheoremOQ01`) and the **dual**
  (Mirsky) hard direction (`DilworthMirskyHardOQ01`, via height/level decomposition).
- Chose the Galvin/Perles route (down-set/up-set decomposition of a maximum antichain).
- Wrote `Proofs/DilworthHardOQ01OQ02.lean` and **verified** (host `lake env lean`, 0 errors):
  - `downSet`/`upSet` defs and membership/subset lemmas.
  - `downSet_inter_upSet : downSet A s ∩ upSet A s = A`.
  - `downSet_union_upSet : downSet A s ∪ upSet A s = s` for a **maximum** antichain.
  - `le_of_mem_chain_downSet` / `ge_of_mem_chain_upSet`: a chain in the down-set (up-set)
    through `a' ∈ A` lies entirely `≤ a'` (`≥ a'`).
  - `glue_isChain`: a down-set chain and an up-set chain through the same `a'` glue into one
    chain — the inductive assembly step.
- Stated `dilworth_chainCover` (strong form); proof left `sorry`.

### Key Findings
- The Mirsky height-decomposition trick does NOT transfer to Dilworth.
- The strong form (antichain bound `w`) is the correct inductive statement (hypothesis is
  inherited by sub-posets).
- **The hard kernel** is the degenerate case `downSet A s = A`: then `upSet A s = s` (A is
  exactly the set of minimal elements), so the up-set recursion does not shrink. The dual
  degeneracy is `A = maximal elements`. Both need a symmetric/dual decomposition plus a
  thin-poset base case (`s` an antichain ⟹ singleton cover). This is precisely why Dilworth
  resisted Mathlib and was a Coq-paper result (Singh–Natarajan, arXiv:1703.06133).

### Files Modified
- `proofs/Proofs/DilworthHardOQ01OQ02.lean` (new; verified core + sorried main thm)
- `src/data/research/problems/dilworth-theorem-oq-01-oq-02.json` (new)
- `research/problems/dilworth-theorem-oq-01-oq-02/knowledge.md` (this file)

### Next Steps
1. "Each size-`w` sub-cover meets the maximum antichain exactly once" (easy direction + pigeonhole).
2. Degenerate case via dual (minimal-element) decomposition + thin-poset base case.
3. Assemble strong induction on `s.card` with `glue_isChain`.
4. Submit `DilworthHardOQ01OQ02.lean` to Aristotle when the service recovers (it returned
   "Resource not found" this session).
