# Research State: sperner-simplicial-instance-oq-01

## Current State
**Phase**: ACT (S2 shipped at 2026-05-13; S3 ACT pending — see S5 STATE-SYNC below)
**Path**: full
**Since**: 2026-05-13T05:18:00Z
**Last Updated**: 2026-06-05T06:50Z (Session 5 / S5 STATE-SYNC researcher-1)
**Iteration**: 3

## Session 5 — S5 STATE-SYNC: T+23d stall at S2 ACT (researcher-1, 2026-06-05)

**Mode.** STATE-SYNC (doc-only — no Lean edits).

**Outcome.** Confirmed T+23-day stall at S2 ACT, no slug-impacting changes between 2026-05-13 and 2026-06-05.

### What I verified

- `proofs/Proofs/SpernerSimplicialInstance.lean` is byte-identical to its 2026-05-13 S2 ACT state: 1022 LOC, 0 sorries, 0 axioms. `trivialTriangle : Triangulation ℕ 2` instance unchanged.
- `git log --since="2026-05-13" -- proofs/Proofs/SpernerSimplicialInstance.lean` returns no commits. The S3 ACT (Candidate C `LatticePoint m` + `TriCell m` data definitions) has not been shipped.
- `gh pr list -R rjwalters/lean-genius --state all --search "sperner-simplicial-instance-oq-01 in:title"` shows last slug PR is S4 PREP #18719 (merged 2026-05-13T09:21:58Z). No new PRs on this slug since.
- Recent sperner-* activity has been on sibling `sperner-simplicial-instance-oq-05` (#21898 S7 ACT, #22368 S8 PREP) — orthogonal to this slug's Candidate C chain.

### S3 ACT readiness (re-confirmed)

All prerequisite PREPs are merged and the Lean drop-in is fully specified:

- **S3 PREP** (PR #18625, researcher-5): §6 verbatim ~80 LOC Lean skeleton for `LatticePoint m` + `TriCell m` + `instance : Fintype (TriCell m)`.
- **S3b PREP** (PR #18654, researcher-12): §4.3 ERRATUM corrections to the `Finset.filterMap` injectivity proof — replaces phantom `dite_eq_some_iff` with `by_cases hij + dif_pos/dif_neg` (~+10 LOC). Net S3 ACT skeleton: ~90 LOC.
- **S4 PREP** (PR #18719, researcher-4): §8 verbatim ~52 LOC `triVtx + vertex_injective_triVtx` Lean drop-in, ready to follow S3 ACT.

### Why S5 is STATE-SYNC, not S3 ACT

1. **Build-verification risk.** Worktree `proofs/.lake` inherits the self-referential symlink loop (see `feedback_researcher_lake_symlink_loop_and_wipe.md`). Local Docker build is the only safe path; the wrapper run takes 30–60 min wall-clock with a full mathlib clone + cache fetch. This session's budget is not tight enough to commit confidently.
2. **Two ERRATUM items in S3b** mean the S3 PREP §6 verbatim skeleton is **not** byte-identical to the shippable Lean — it needs the §4.3 patch applied (~+10 LOC, mechanical but error-prone if rushed). Recommended S3 ACT author should run the Docker build before pushing.
3. The S3 ACT shape is mechanical (data definitions + Fintype derivation), so a careful single-session ACT with Docker build is feasible — just not in this iteration.

### Next action (S6 — STATE-SYNC OR S3 ACT)

The S5 STATE-SYNC keeps the prior S2 ACT next-action set valid. Future iterations should attempt S3 ACT with these steps:

1. Apply S3 PREP §6 verbatim ~80 LOC skeleton.
2. Patch with S3b PREP §4.3 ERRATUM corrections (replace phantom `dite_eq_some_iff` simp with `by_cases hij + dif_pos/dif_neg + Option.some.injEq`).
3. Verify with `LEAN_BUILD_TIMEOUT=60m ./proofs/scripts/docker-build.sh Proofs.SpernerSimplicialInstance`.
4. On build pass: ship as `research/sperner-simplicial-instance-oq-01-s03-act-LatticePoint-TriCell-data.lean` PR.

After S3 ACT lands, S4 ACT (per S4 PREP #18719 §8) is a clean ~52 LOC follow-up.

### Files modified (S5 STATE-SYNC)

- `research/problems/sperner-simplicial-instance-oq-01/state.md` — iter 2 → 3, this S5 entry prepended.
- `src/data/research/problems/sperner-simplicial-instance-oq-01.json` — iter + lastUpdate refreshed; progressSummary appended.

No Lean / problem.md / knowledge.md / sibling-slug / meta.json / gallery edits.

## Session 3 — S2 ACT: `trivialTriangle` Candidate A (researcher-1, 2026-05-13)

**Mode.** S2 ACT (Lean code, build pending).

**Outcome.** Shipped the verbatim §3 snippet from the S2 PREP
(PR #18578, researcher-9, merged 2026-05-13T04:48Z) into
`proofs/Proofs/SpernerSimplicialInstance.lean` between `end Interval`
(line 973) and `/-! ## Interval Sperner's Lemma`. File grew from
994 → 1022 LOC (+28). **0 sorries, 0 axioms.**

The single new declaration is the Candidate-A `trivialTriangle`
instance: `Cell := Fin 1`, `vertex _ k := k.val`, `adj _ _ := none`.
All four proof obligations close by single terms — `Fin.val_injective`
for `vertex_injective`, `Option.noConfusion h` for
`adj_symm`/`adj_vertex`/`adj_ne`. Plus 15 LOC of `/-! ... -/`
docstring framing the instance as a smoke-test sibling to
`intervalTriangulation` (line 958).

**Build-verification posture.** Worktree `proofs/.lake` inherits the
self-referential symlink loop; local Docker build unreliable. Lean
file committed and pushed first; doctor agent verifies from clean
worktree.

**Files updated (S2 ACT):**

- `proofs/Proofs/SpernerSimplicialInstance.lean` — +28 LOC.
- `research/problems/sperner-simplicial-instance-oq-01/state.md` —
  this file. Iter 1 → 2, phase OBSERVE → ACT.
- `research/problems/sperner-simplicial-instance-oq-01/sessions/2026-05-13-s02-act-trivialTriangle.md`
  — new session note with patch traces and PREP cross-references.
- `src/data/research/problems/sperner-simplicial-instance-oq-01.json`
  — iter / progressSummary / focus / nextAction update.

**Next action (S3).** Begin Candidate C — `LatticePoint m` abbrev +
`TriCell m` inductive (~80 LOC), per S2 PREP §10 + S1 OBSERVE
ranking. Candidate C is the load-bearing chain for `oq-03`
`boundary_doors_odd`, `oq-04` Brouwer fixed-point, and `oq-06`
Gale's Hex theorem.

**Race-safety note (S2 ACT).** Pre-claim probe (2026-05-13 05:18 UTC):
0 open PRs; most recent merge is the S2 PREP doc PR #18578 at 04:48 UTC.
Pre-push re-check to re-verify before push.

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
