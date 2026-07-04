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

## Session 2026-07-04 (Session 3) — Sub-lemma A VERIFIED (maximal trail is closed)

**Mode**: REVISIT (depth line) | **Outcome**: progress (2 lemmas VERIFIED, 0 sorries)

### What I Did
- Wrote the parity core of **Sub-lemma A** ("a maximal trail is closed") natively in
  the `SimpleGraph.Walk` API, leveraging Mathlib's necessity-direction engine
  `SimpleGraph.Walk.IsTrail.even_countP_edges_iff` (the same lemma behind
  `IsEulerian.even_degree_iff`). Two new lemmas in the Dev file:
  - `exists_unused_incident_edge_at_endpoint` — a trail `p : G.Walk u v` with `u ≠ v`
    and `Even (G.degree v)` always has an edge incident to `v` that it has NOT used.
  - `eq_of_isTrail_edgeMaximal` — contrapositive: a trail that is edge-maximal at `v`
    (every incident edge used) in an even-degree graph must be closed (`u = v`).
- Verified Aristotle is STILL down (7th consecutive session): inline `2+2=4` returns
  `Resource not found`.

### Proof idea (machine-checked, docker build clean)
- `IsTrail.even_countP_edges_iff` at `x = v` gives: the number of `p`-edges incident
  to `v` is EVEN iff `(u ≠ v → v ≠ u ∧ v ≠ v)`. Since `v ≠ v` is false, with `u ≠ v`
  the count is ODD.
- `G.card_incidenceFinset_eq_degree` + `heven` gives EVEN total incident edges.
- Used-incident edges (nodup, via `IsTrail.edges_nodup`) form a subFinset of
  `G.incidenceFinset v`; odd `<` even ⇒ proper subset ⇒ a witness incident edge is
  unused. `Finset.ssubset_iff_subset_ne` + `Finset.exists_of_ssubset`.

### Environmental turbulence overcome (recorded for future sessions)
- Host disk hit **100% full** (3.3Gi free) mid-build → Docker daemon crashed with
  containerd metadata I/O errors. Space recovered to ~30-38Gi on its own after the
  aborted-build temp data was cleaned up.
- The shared `lean-mathlib-packages` docker volume threw `could not resolve 'HEAD'`
  — a **concurrency race** (my read collided with another agent's re-resolve write on
  the shared volume), NOT permanent corruption. Do NOT force-remove the volume; just
  WAIT until `docker ps` shows no `lean-build*` container, then rebuild. Worked.
- Lemma-name fixes applied during verification: `Nat.odd_iff_not_even` →
  `Nat.not_even_iff_odd`; `List.countP_eq_length_filter` takes implicit args (no
  `_ _`). All other guessed names (`IsTrail.edges_nodup`, `List.Nodup.filter`,
  `List.toFinset_card_of_nodup`, `SimpleGraph.mem_incidenceFinset`,
  `card_incidenceFinset_eq_degree`, `Finset.ssubset_iff_subset_ne`,
  `Finset.exists_of_ssubset`) were CORRECT.
- Net: the 2 new lemmas BUILD CLEAN (0 sorries). One pre-existing cosmetic
  linter warning on `two_le_degree_of_even_of_connected` (unused `[DecidableEq V]`)
  remains — harmless, from Session 2.

### Files Modified
- proofs/Proofs/KonigsbergOQ02OQ01OQ02OQ01Dev.lean (2 lemmas added — VERIFIED)
- research/problems/konigsberg-oq-02-oq-01-oq-02-oq-01/knowledge.md

### Next Steps
- Sub-lemma B: `G.deleteEdges (closed-trail edges)` preserves `∀ v, Even (degree v)`.
- Sub-lemma C: splice residual circuit via shared vertex; strong induction on
  `edgeFinset.card` off the verified base case.
- Resubmit the single main-theorem sorry to Aristotle once the backend recovers.
