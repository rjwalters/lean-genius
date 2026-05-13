# Research State: sperner-simplicial-instance-oq-01

## Current State
**Phase**: OBSERVE (S1 candidate ranking complete via `sessions/2026-05-12-s01.md`)
**Path**: full
**Since**: 2026-05-12T13:53:33-07:00
**Last Updated**: 2026-05-12 (Session 1 / S1 OBSERVE researcher-11)
**Iteration**: 1

## Session 1 — S1 OBSERVE: candidate-ranking + S2 ACT path (researcher-11, 2026-05-12)

**Mode.** OBSERVE doc-only.  No `.lean` edits.

**Outcome.** Enumerated four candidate constructions for the
"verify the standard 2-simplex triangulation as a concrete
`Triangulation` instance" open question, mirrored against the
parent's 1-d `intervalTriangulation` template (lines 808–994 of
`proofs/Proofs/SpernerSimplicialInstance.lean`).  Ranked by S2
LOC + utility.

* **Candidate A** (trivial 1-cell, `Triangulation ℕ 2`): ~30 LOC, ~30 min.
* **Candidate B** (trivial 1-cell sorted, `Triangulation (Fin 3) 2`): ~20 LOC, ~15 min.
* **Candidate C** (m × m subdivision, `Triangulation (ℕ × ℕ) 2` with `m²` + `(m-1)²` cells): ~250–400 LOC across 6–8 sessions.
* **Candidate D** (Freudenthal): rejected — wrong shape (cube, not simplex).

**Alignment with seeker-init JSON design.** The JSON tracker
`src/data/research/problems/sperner-simplicial-instance-oq-01.json`
(seeker-pre-populated) locks in a Candidate-C-flavored design with
`LatticePoint m` subtype + `TriCell m` inductive (up/down) +
case-table adjacency, estimating ~300 LOC into the parent file
with 0–1 strategic `sorry` (`adj_vertex` case explosion).  S1's
ranking confirms this is the right S2 target *for the main
ACT chain*, but also flags Candidate A as a useful **smoke-test
predecessor** before the C chain starts.

**Mathlib audit.** `gh api search/code` on
`YoungDiagram repo:leanprover-community/mathlib4` confirmed
Mathlib has no `Triangulation` analogue at v4.26.0 — the parent's
`Triangulation V n` structure is the only working API.  No
off-the-shelf chain.  This matches `oq-01`'s framing: the work is
entirely project-side.

## Adjacent open questions

From `src/data/proofs/sperner-simplicial-instance/meta.json`
`conclusion.openQuestions`:

1. **`oq-01` (this slug)** — 2-simplex Triangulation instance.
2. **`oq-02`** — Connect `AbstractSimplicialData.toTriangulation` to
   `Mathlib.Geometry.SimplicialComplex`.
3. **`oq-03`** — Prove `boundary_doors_odd` for the n-simplex.
4. **`oq-04`** — Brouwer fixed point (consumes `oq-01` + `oq-03`).
5. **`oq-05`** — Computable Scarf algorithm.
6. **`oq-06`** — Gale's Hex theorem (consumes `oq-01`).

`oq-01` is the **load-bearing** prerequisite for `oq-03`, `oq-04`,
and `oq-06`.

## Next Action

**S2 ACT (recommended).**  Ship Candidate A (or B) as a
build-verified `trivialTriangle : Triangulation ℕ 2` (or
`Triangulation (Fin 3) 2`) instance inserted between line 994 of
`SpernerSimplicialInstance.lean` and `end Triangulation`.  ~30 LOC,
0 sorries.  Establishes the build-verified baseline for the 2-d
case; useful as a fixture for future `boundary_doors_odd` work on
`oq-03`.

**S2-Continued / S3+ (recommended).**  Begin the Candidate C
chain per the seeker-init JSON's locked design:
1. `LatticePoint m` abbrev + `TriCell m` inductive (S3 — ~80 LOC).
2. `triVtx m c k`, `vertex_injective` (S4 — ~50 LOC).
3. `triAdj m c k`, `adj_ne` (S5 — ~60 LOC).
4. `adj_symm`, `adj_vertex` (S6–S7 — ~100 LOC, possibly 1 strategic sorry).
5. `standardTriangleTriangulation m hm : Triangulation _ 2` (S8 — ~10 LOC).

## Active Approach

Doc-only S1 OBSERVE complete; S2 ACT to be picked up by next
researcher (Candidate A or Candidate C step 1).

## Attempt Count

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (S1 OBSERVE candidate ranking)

## Blockers

None.

## Trap notes

* No race: `gh pr list --search "sperner-simplicial-instance-oq-01"` returns only PR #18166 (seeker batch, non-research).
* Worktree `.lake` symlink-loop risk per `feedback_researcher_lake_symlink_loop_and_wipe.md`: any S2 Lean ACT should commit + push first, let Doctor verify from clean worktree.
