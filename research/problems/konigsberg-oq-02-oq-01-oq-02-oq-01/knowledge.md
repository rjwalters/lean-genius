# Knowledge Base: konigsberg-oq-02-oq-01-oq-02-oq-01

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

## Session 2026-07-04 (Session 1) — Statement + reduction analysis

**Mode**: FRESH
**Outcome**: progress (ORIENT→ACT: compiling statement, sufficiency sorry)

### What I Did
- Claimed the problem (undirected Hierholzer sufficiency).
- Created `proofs/Proofs/KonigsbergOQ02OQ01OQ02OQ01.lean` stating
  `undirected_euler_circuit_sufficient` (1 sorry) and the full characterization
  `undirected_euler_circuit_iff` (necessity half fully proved via
  `IsEulerian.even_degree_iff`).
- Verified it builds in Docker (only the expected `sorry` warning); needed
  `import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected`.

### Key Findings
- Mathlib has Eulerian degree bookkeeping but no undirected existence/Hierholzer.
- The fully-proved DIRECTED analogue (`directed_euler_circuit_sufficient_corrected`
  in `KonigsbergOQ02OQ01.lean`, ~900 lines) is a structural template.
- **Naive doubling reduction FAILS**: splitting each undirected edge into two
  opposite arcs makes the digraph balanced/strongly-connected, but the resulting
  directed Eulerian circuit uses each undirected edge twice — not an undirected
  Eulerian circuit. A native undirected argument is required.

### Files Modified
- proofs/Proofs/KonigsbergOQ02OQ01OQ02OQ01.lean (new)
- src/data/research/problems/konigsberg-oq-02-oq-01-oq-02-oq-01.json (knowledge)

### Next Steps
- Port the 3-step Hierholzer sub-lemma structure (maximal trail is closed →
  edge removal preserves even degree → splice via shared vertex → induct on edges).
- Re-submit the sorry file to Aristotle from the main repo (MCP "Resource not
  found" from the worktree) as a KNOWN result.

## Session 2026-07-04 (Session 2) — Base case verified; plan corrected

**Mode**: REVISIT (depth line) | **Outcome**: progress (1 verified lemma)

### What I Did
- Confirmed via web search + local check that Mathlib4 still has NO undirected
  Eulerian existence/Hierholzer construction (only `even_degree_iff`,
  `card_odd_degree`).
- Confirmed the directed `Digraph` proof is NOT reusable: it is built on a bespoke
  `Digraph` type (own Walk/splice/removeArcList/arcCount), not `SimpleGraph.Walk`.
- Wrote and **verified** the induction base case in a new dev file:
  `euler_circuit_of_edgeSet_empty` (connected + `G.edgeSet = ∅` ⇒ Eulerian circuit
  via the `nil` walk). Compiles clean, 0 sorries.
- Aristotle backend was fully DOWN (`Resource not found` even for inline `1+1=2`),
  so the known-result delegation could not run this session.

### Key Findings
- **Definition correction**: Mathlib's `IsEulerian p := ∀ e ∈ G.edgeSet,
  p.edges.count e = 1` — a per-edge count condition, NOT `IsTrail ∧ covers-all`.
  Trail-ness is derived (`IsEulerian.isTrail`). The construction invariant is the
  count=1 condition. `IsEulerian` needs `[DecidableEq V]`.

### Files Modified
- proofs/Proofs/KonigsbergOQ02OQ01OQ02OQ01Dev.lean (new — base case, verified)
- src/data/research/problems/konigsberg-oq-02-oq-01-oq-02-oq-01.json (knowledge)

### Next Steps
- Sub-lemma A: maximal trail in an all-even graph is closed (parity/handshake).
- Sub-lemma B: `G.deleteEdges (closed trail edges)` preserves `∀ v, Even (degree v)`.
- Sub-lemma C: splice residual circuit via shared vertex; strong induction on
  `edgeFinset.card` using the verified base case.
- Resubmit the single sorry to Aristotle once the backend recovers.

## Session 2026-07-04 (Session 4) — Recovered Sub-lemma A + new Sub-lemma B parity core

**Mode**: REVISIT (depth line) | **Outcome**: progress (5 lemmas VERIFIED, 0 sorries)

### What I Did
- Found that PR #34697 (Session 3's verified Sub-lemma A) was **auto-closed as a false
  "superseded"** by the deployer's file-level race cleanup: the deployer saw the Dev
  file already exists on `main` (base case only, from #34679) and discarded the whole
  branch, silently dropping the extra verified lemmas. Confirmed
  `exists_unused_incident_edge_at_endpoint` was NOT on `main`.
- **Recovered** the three wrongly-discarded verified lemmas into the Dev file:
  `two_le_degree_of_even_of_connected`, `exists_unused_incident_edge_at_endpoint`,
  `eq_of_isTrail_edgeMaximal` (Sub-lemma A: a maximal trail is closed).
- **Proved a new lemma** advancing Sub-lemma B: `even_countP_incident_of_closed_trail`
  — for a *closed* trail `p : G.Walk u u` and any vertex `x`, `Even (p.edges.countP
  (x ∈ ·))`. This is the parity fact that makes edge-removal preserve the
  all-even-degree invariant. Proof: `IsTrail.even_countP_edges_iff` whose RHS is
  trivial when start = end (closed by `tauto`).
- Docker build clean: `⚠ Built Proofs.KonigsbergOQ02OQ01OQ02OQ01Dev` — 0 sorries, only
  a harmless unused-`[DecidableEq V]` linter warning on `two_le_degree_...`.
- This branch is a **strict superset** of main's Dev file (a MODIFY, not add/add), so
  it should not trip the file-level supersession auto-close that killed #34697.

### Key Findings
- The deployer's supersession cleanup is **file-existence based, not content based** —
  a branch that *adds new lemmas to an existing file* can be wrongly closed if that
  file's path already exists on main. Future depth-line work on this file must land as
  a MODIFY of main's version (branch from origin/main), not re-add the file.
- Sub-lemma B now factors into: (parity core — DONE) + the `deleteEdges` degree
  bookkeeping `(G.deleteEdges ↑p.edges.toFinset).degree w = G.degree w −
  p.edges.countP (w ∈ ·)`, which is the remaining mechanical step.

### Files Modified
- proofs/Proofs/KonigsbergOQ02OQ01OQ02OQ01Dev.lean (base case → +4 verified lemmas)
- src/data/research/problems/konigsberg-oq-02-oq-01-oq-02-oq-01.json (knowledge)

### Next Steps
- Sub-lemma B finish: relate `(G.deleteEdges E).degree w` to `G.degree w` minus the
  incident-edge count, then combine with `even_countP_incident_of_closed_trail` to get
  `∀ w, Even ((G.deleteEdges ↑p.edges.toFinset).degree w)`.
- Sub-lemma C: splice residual closed trail via a shared vertex (connectivity).
- Strong induction on `G.edgeFinset.card` assembling base case + A + B + C.
