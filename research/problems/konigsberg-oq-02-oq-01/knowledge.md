# Knowledge Base: konigsberg-oq-02-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Formalize Hierholzer's algorithm for directed Eulerian circuits.
**Source bug**: `directed_euler_circuit_sufficient` in `KonigsbergOQ02.lean` (line 409) is
an axiom missing the strong connectivity hypothesis. Two disjoint balanced directed triangles
give a counterexample.

**Correct statement**: If D is strongly connected AND every vertex has indeg = outdeg, then
D has an Eulerian circuit.

---

## Session 2026-04-24 (Session 1) — Walk.splice + Hierholzer Infrastructure

**Mode**: FRESH
**Outcome**: progress — core infrastructure proved, 3 sorries remain

### What I Did
- Wrote KonigsbergOQ02OQ01.lean (436 lines) from scratch
- Proved `maximal_balanced_trail_is_circuit` (0 sorries): in a balanced digraph, any maximal
  Nodup trail where all out-arcs from the endpoint are used must be a closed circuit
- Proved `Walk.splice` (0 sorries): concatenate two walks D.Walk u v and D.Walk v w into D.Walk u w
- Proved `Walk.splice_nodup`: splice of arc-disjoint Nodup walks is Nodup
- Defined `isStronglyConnected` (standalone, not `Digraph.isStronglyConnected` — see namespace note)
- Defined `removeArcList D arcs` — residual subgraph removing listed arcs
- Stated `removeArcList_balanced` (sorry): balance preserved when removing a circuit
- Stated `removeArcList_arcCount` (sorry): arcCount formula for residual
- Stated `directed_euler_circuit_sufficient_corrected` (sorry): main theorem with WF induction

### Key Findings
- **Namespace rule**: `def Digraph.foo` inside `namespace N` creates `N.Digraph.foo`, which is
  NOT accessible via dot notation `d.foo` where `d : KonigsbergOQ02.Digraph V`. Must use
  standalone `def foo` and explicit arguments `foo D`.
- **Digraph structure field**: `loopless` is the correct field name (not `noSelfLoops`)
- **Decidable instance**: Use `inferInstance` for `DecidableRel (removeArcList D arcs).adj`,
  not `And.decidable` (unknown since Lean 4.x)
- **Chain deprecation**: `List.Chain'` → `List.IsChain` (deprecated since 2025-09-24)
- **Walk.splice consecutive proof**: Uses `isChain_append`, `List.mem_getLast?_eq_getLast`,
  `List.eq_cons_of_mem_head?` to bridge the last arc of w1 with first arc of w2

### Files Modified
- `proofs/Proofs/KonigsbergOQ02OQ01.lean` (new, 436 lines)
- `src/data/proofs/konigsberg-oq-02-oq-01/meta.json` (new)
- `src/data/proofs/konigsberg-oq-02-oq-01/index.ts` (new)

### Next Steps
1. Prove `removeArcList_balanced`: use `circuit_fst_perm_snd` to show equal per-vertex
   fst/snd counts in the circuit, subtract equal amounts from balanced outDeg/inDeg
2. Prove `removeArcList_arcCount`: bijectivity argument (Nodup arc list ⊆ D.arcs)
3. Complete WF induction for `directed_euler_circuit_sufficient_corrected`:
   - Measure: `D.arcCount - current_circuit_length`
   - Inductive step: find vertex u on C with unused out-arcs (strong connectivity + balance),
     build C' in residual via `maximal_balanced_trail_is_circuit`, splice via `Walk.splice`

---

## Insights

- Strong connectivity is NECESSARY for Euler circuits (two disjoint balanced triangles = counterexample)
- `maximal_balanced_trail_is_circuit` is the key sub-lemma: fst_count = outDeg at stuck vertex,
  snd_count ≤ inDeg = outDeg (by balance), so trail must have returned to start
- `Walk.splice` is the circuit extension operation: combining C at vertex u with C' gives a longer circuit
- `circuit_fst_perm_snd` (private in OQ02) needs to be reproved in OQ02OQ01 for `removeArcList_balanced`
- The WF induction for the main theorem is purely glue code: all mathematical substance is in
  `maximal_balanced_trail_is_circuit`, `Walk.splice`, and `removeArcList_balanced`

---

## Dead Ends

- Attempting `Digraph.removeArcList` with dot notation: namespace resolution fails in Lean 4
  because `def Digraph.foo` inside `namespace N` creates `N.Digraph.foo` not `N2.Digraph.foo`
  where `N2` is the type's home namespace
