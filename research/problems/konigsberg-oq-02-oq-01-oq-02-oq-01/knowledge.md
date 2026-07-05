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

## Session 2026-07-04 (Session 4) — Sub-lemma B VERIFIED + A/B packaged (committed)

**Mode**: REVISIT (depth line) | **Outcome**: progress (3 lemmas VERIFIED, 0 sorries)

Committed to branch `feature/researcher-11` (Docker verified in prior sub-sessions,
per commit messages — files build clean with only the single expected main-theorem
`sorry`):
- `even_countP_edges_of_closed` — a closed trail uses an EVEN number of edges
  incident to every vertex (specializes `IsTrail.even_countP_edges_iff` at a closed
  trail, whose RHS `(u≠u → …)` is vacuously true). This is the parity ingredient of
  edge removal.
- `even_degree_deleteEdges_of_closed_trail` (**Sub-lemma B**) — deleting a closed
  trail's edges preserves `∀ x, Even (degree x)`. Surviving incident edges of `x` are
  `A \ S` with `A = incidenceFinset x`, `S = p.edges.toFinset`; `#A = degree x` even,
  `#(A ∩ S) = countP` even ⇒ `#(A \ S)` even via `Finset.card_sdiff_add_card_inter`.
- `even_degree_deleteEdges_of_maximal_trail` — packages A+B in the shape the
  recursion consumes: from `heven` + edge-maximality at `v` (no existence of `u=v`
  assumed), get `u=v` via Sub-lemma A then Sub-lemma B ⇒ residual graph re-satisfies
  the all-even invariant. This is the induction-step invariant-preservation obligation.

**State after Session 4**: the Dev file (`KonigsbergOQ02OQ01OQ02OQ01Dev.lean`) holds
7 VERIFIED sorry-free lemmas covering the base case + the entire *invariant-
preservation* half of the Hierholzer induction step (greedy endpoint parity ⇒ closed;
edge removal ⇒ even-degree preserved). What remains for the main theorem is the
*constructive* half (Sub-lemma C).

## Session 2026-07-04 (Session 5) — Extremal engine drafted; DUAL-TOOL BLACKOUT

**Mode**: REVISIT (depth line) | **Outcome**: progress (2 lemmas DRAFTED, unverified)

### Tool status (both verification paths DOWN this session)
- **Aristotle**: 404 `Resource not found` on an inline `1+1=2` liveness check
  (8th consecutive session down).
- **Docker**: containerd content store has **I/O errors on the cached lean image
  blob itself** — `docker run <lean-image>` fails with
  `blob sha256:3d1c9c6b… input/output error`, and `docker images` returns empty
  (metadata store unreadable). Two stale `lean-build-*` containers have been "Up 3
  hours". Disk is fine (20Gi free, 37% used) — this is Docker Desktop
  containerd-metadata corruption needing a **daemon restart** (not disk pressure).
  No new Lean can be machine-checked this session.

### What I Did
Because `proofs/Proofs/*.lean` is globbed into the build, unverified Lean must NOT be
committed there (a non-compiling module would break the gallery build). So the next
two construction lemmas are **drafted here** for immediate verify-and-paste the moment
Docker recovers. Both reuse only API already exercised by the 7 verified lemmas, plus
a small `Sym2`/`concat` layer flagged below.

**Draft L1 — trail length bound (HIGH confidence; verified-API only):**
```lean
/-- A trail uses at most `edgeFinset.card` edges: its edge list is nodup and ⊆ the
edge set. Makes trail-lengths a bounded ℕ-set, so a MAXIMUM-length trail exists — the
extremal seed of Hierholzer (a max-length trail cannot be extended ⇒ is closed). -/
theorem trail_edges_length_le_card
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.edges.length ≤ G.edgeFinset.card := by
  classical
  have hsub : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    rw [List.mem_toFinset] at he
    rw [mem_edgeFinset]
    exact p.edges_subset_edgeSet he
  calc p.edges.length
      = p.edges.toFinset.card := (List.toFinset_card_of_nodup hp.edges_nodup).symm
    _ ≤ G.edgeFinset.card := Finset.card_le_card hsub
```

**Draft L2 — open trail into an even vertex is not maximal-length (MODERATE conf.):**
```lean
/-- An open trail (`u ≠ v`) into an even-degree vertex is strictly extendable: append
an unused incident edge at `v` to get a longer trail from `u`. With `trail_edges_
length_le_card` this is the extremal engine — a MAXIMUM-length trail must be closed. -/
theorem exists_longer_trail_of_open
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) (hne : u ≠ v)
    (heven : Even (G.degree v)) :
    ∃ (w : V) (q : G.Walk u w), q.IsTrail ∧ p.edges.length < q.edges.length := by
  classical
  obtain ⟨e, heIn, heOut⟩ := exists_unused_incident_edge_at_endpoint hp hne heven
  rw [SimpleGraph.mem_incidenceFinset] at heIn
  obtain ⟨heEdge, heV⟩ := heIn          -- heEdge : e ∈ G.edgeSet, heV : v ∈ e
  set w : V := heV.other with hwdef
  have hspec : s(v, w) = e := Sym2.other_spec heV
  have hadj : G.Adj v w := by rw [← SimpleGraph.mem_edgeSet, hspec]; exact heEdge
  have hunused : s(v, w) ∉ p.edges := by rw [hspec]; exact heOut
  refine ⟨w, p.concat hadj, ?_, ?_⟩
  · refine ⟨?_⟩                         -- IsTrail = ⟨edges.Nodup⟩
    rw [SimpleGraph.Walk.edges_concat, List.nodup_concat]
    exact ⟨hp.edges_nodup, hunused⟩
  · rw [SimpleGraph.Walk.edges_concat, List.length_concat]
    exact Nat.lt_succ_self _
```

### API risk notes for next session (fix these names first if L2 fails to elaborate)
- `Sym2.other_spec heV : s(v, heV.other) = e` — verify exact name/orientation; the
  `[DecidableEq V]` variant is `Sym2.Mem.other'` / `Sym2.other_spec'`. If `heV.other`
  dot-notation fails, use `Sym2.Mem.other heV`.
- `List.nodup_concat : (l.concat a).Nodup ↔ l.Nodup ∧ a ∉ l` — check the conjunct
  order; if `edges_concat` yields `p.edges ++ [s(v,w)]` (append, not `.concat`),
  rewrite with `List.nodup_append`/`List.length_append` + `List.length_singleton`
  instead.
- `SimpleGraph.Walk.edges_concat` RHS form (`.concat` vs `++ [·]`) governs which of
  the two bullets above applies. `mem_incidenceFinset` unfolding to
  `e ∈ edgeSet ∧ v ∈ e` is CONFIRMED (used verbatim in the verified
  `exists_unused_incident_edge_at_endpoint`).

### Why this is the right next step (not enumeration theater)
The remaining gap is the *constructive* half of Hierholzer (Sub-lemma C). The
**extremal** formulation replaces an awkward well-founded greedy recursion with a
finite-max argument: (a) trail-lengths are bounded [L1], so a max-length trail exists;
(b) a max-length trail is edge-maximal at its endpoint, hence CLOSED [L2 + Sub-lemma A
`eq_of_isTrail_edgeMaximal`, already verified]; (c) a closed max-length trail uses
EVERY edge — else connectivity gives an unused edge at a visited vertex and rotation
yields a longer trail (the remaining harder step). L1+L2 are (a)+(b); they turn the
main `sorry` into just step (c) + the rotation lemma.

### Files Modified
- research/problems/konigsberg-oq-02-oq-01-oq-02-oq-01/knowledge.md (drafts staged)
- src/data/research/problems/konigsberg-oq-02-oq-01-oq-02-oq-01.json (metadata refresh)

### Next Steps
1. When Docker recovers: paste L1 + L2 into the Dev file, `docker-build.sh
   Proofs.KonigsbergOQ02OQ01OQ02OQ01Dev`, fix the flagged names, commit VERIFIED.
2. Prove existence of a maximum-length trail (`Finset.exists_max`-style over the
   bounded length set; needs care with the dependent endpoint type — consider indexing
   trails by `Σ w, G.Walk u w` for a fixed start `u`, or over the nonempty finite set
   of achievable lengths).
3. Sub-lemma C step (c): closed max-length trail is Eulerian — the rotation lemma
   (`p.rotate`? / reindex a closed trail to start at any visited vertex) + connectivity
   to locate an unused incident edge at a visited vertex.
4. Resubmit the main-theorem `sorry` to Aristotle as a KNOWN result once its backend
   returns (it is classical undirected Hierholzer).
