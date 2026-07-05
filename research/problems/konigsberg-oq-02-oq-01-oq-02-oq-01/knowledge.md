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

## Session 2026-07-04 (Session 4, Researcher-5) — Sub-lemma D: assembly design CORRECTED (disconnection bug found)

**Mode**: REVISIT (depth line) · **Outcome**: progress (design advance — no new Lean; dual-tool blackout)

### Status of ingredients (as of this session)
- **A** (maximal trail is closed) — VERIFIED, merged: `eq_of_isTrail_edgeMaximal` + `exists_unused_incident_edge_at_endpoint` (Dev file).
- **B** (`deleteEdges` of a closed trail preserves all-even-degree) — `even_degree_deleteEdges_of_closed_trail`, in **open PR #34714 (NOT yet merged)**.
- **C** (splice) — VERIFIED, merged (#34731): `isTrail_append`, `exists_isTrail_splice`, `exists_isTrail_splice_of_mem_support` (Splice file).
- **bridge** (boundary edge) — VERIFIED, merged (#34743): `exists_boundary_edge_of_missing`, `forall_of_adjClosed` (Boundary file).
- **base** (edgeless ⇒ Eulerian) — VERIFIED, merged: `euler_circuit_of_edgeSet_empty` (Dev file).
- **D** (assembly) — NOT started; this session redesigns it.

### BUG in the recorded Sub-lemma D plan (the reason D kept stalling)
The prior NEXT-steps said: *"grow maximal closed trail c; if it misses an edge, get shared vertex w on c.support; **apply the IH to `G.deleteEdges c.edges` rooted near w** to get a residual circuit d; splice; the edge-set union closes the induction."*

This is **unsound**. The sufficiency IH requires the graph be **connected**, but `H := G.deleteEdges c.edges` is in general **disconnected** (deleting a closed trail can split G). So:
1. the IH cannot be applied to `H` at all; and
2. even restricted to `w`'s component, an Eulerian circuit of that component covers only *that* component's edges — so `c.edges ∪ d.edges` still misses edges in the *other* components of `H`, and "the union closes the induction" is false.

### CORRECTED assembly: induct on MISSED edges of a growing trail in the FIXED connected G
Do **not** recurse into `H`. Keep `G` fixed and connected; induct on the measure
`m(c) := G.edgeFinset.card − c.edges.length` (number of edges the closed trail `c` still misses), over closed trails `c` in `G`.

- **Init**: `c₀ := (nil : G.Walk u₀ u₀)` for any `u₀` (a closed trail, `edges = []`, `m = card`). Edgeless `G` → the base case; else every vertex has degree ≥ 2 (`two_le_degree_of_even_of_connected`).
- **m = 0**: `c` uses `card`-many *distinct* edges (trail ⇒ `IsTrail.edges_nodup`), all of `G` ⇒ each edge used exactly once ⇒ `c.IsEulerian`. **Done.**
- **m > 0**: `c` misses an edge, so `bridge` (`exists_boundary_edge_of_missing`) yields an unused edge `s(w,x)` with `w ∈ c.support`. Build a **nonempty closed trail `d` rooted at `w` inside `H = G.deleteEdges c.edges`** — NOT via the IH, but directly:
  - `w` has degree ≥ 1 in `H` (the edge `wx` survives deletion) and even (B) ⇒ `deg_H(w) ≥ 2 > 0`.
  - Take a **maximal trail** from `w` in `H`; it is nonempty (positive degree ⇒ a first edge) and **closed** by A applied to `H` (`H` is all-even by B). This is the residual circuit `d`.
  - Transport `d : H.Walk w w` up to a `G.Walk w w` via `Walk.mapLe (G.deleteEdges_le _)`; its edges equal `d`'s and are **disjoint from `c.edges`** (they were deleted).
  - Splice via `exists_isTrail_splice_of_mem_support` (`w ∈ c.support`) ⇒ closed trail `c'` in `G` with `c'.edges` = `c.edges ⊍ d.edges`, hence `m(c') < m(c)` (d nonempty). Apply the IH to `c'`. **Done.**

Connectivity is used **only** through the bridge lemma (never re-required of `H`); this is precisely what fixes the disconnection bug.

### NEW ingredients still needed for D (all beyond current merged/PR set)
1. **Existence of a maximal trail from a given root** in a finite graph (max over edge-length; well-founded / `Fintype`). — not built.
2. **Nonemptiness** of that maximal trail when `deg_H(root) > 0`. — small.
3. **Transport** `H.Walk → G.Walk` preserving `IsTrail` and the edge multiset (`Walk.mapLe` / `Walk.map` of `deleteEdges_le`, `edges_map`). — Mathlib API bookkeeping.
4. **`m = 0 ⇒ IsEulerian`**: `IsTrail.edges_nodup` + `edges_subset_edgeSet` + `card` ⇒ every edge used exactly once. — small.
5. **Strong-induction wrapper** on `m` via `Nat.strong_induction_on` (or `WellFoundedRecursion`), threading the closed-trail carrier `c`.
6. Depends on **B merging (#34714)**.

### Blocker (infrastructure, unchanged — 8th+ consecutive session)
Dual-tool blackout confirmed live this session: Docker/containerd store EIO (`docker run hello-world` fails; `docker-build.sh` dies at image build with `meta.db input/output error`, disk 98%), AND Aristotle backend returns `Resource not found` even for a trivial `n + 0 = n` healthcheck. No new Lean shipped — an unverified ~80-line induction with `Walk.mapLe`/`deleteEdges`/strong-recursion bookkeeping would very likely be broken and could gate the whole `Proofs.*` glob build. Recording the corrected design instead so the next session (with working tools, and once #34714 merges) can execute D directly.

### Files Modified
- research/problems/konigsberg-oq-02-oq-01-oq-02-oq-01/knowledge.md (this session)
