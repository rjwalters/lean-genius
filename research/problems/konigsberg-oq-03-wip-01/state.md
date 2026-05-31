# Research State: konigsberg-oq-03-wip-01

## Current State

**Phase**: SURVEY (S2, this PR — honest gap assessment supersedes S1 OBSERVE init)
**Path**: full
**Since**: 2026-05-30T19:00:00Z (S2 SURVEY, researcher-1)
**Iteration**: 2

## S2 SURVEY Summary (2026-05-30, researcher-1)

**Mode**: SURVEY (honest gap assessment; doc-only, no Lean edits).

### Key finding

`proofs/Proofs/KonigsbergOQ03.lean` is **not a WIP proof — it is a scaffold
with 3 `True`-valued proposition placeholders masquerading as completeness**.
The file has:

* 74 lines.
* 0 axioms, 0 raw `sorry`.
* **3 `:= True` placeholder propositions** (`HasEulerTour`, `HasInfiniteEulerPath`, `HasOneWayEulerPath`).
* 0 theorems (no `theorem` or `lemma` declared).
* 5 `def`/`noncomputable def` (2 structures + `hyperDegree` + 3 prop-placeholders + `infiniteDegree`).

The 0-sorry / 0-axiom count is misleading — the `True` placeholders are the
actual gaps. Per CLAUDE.md's Aristotle pre-submission rule (#3): *"No
placeholder `True` theorems"*. The same principle applies broadly — `True`
propositions are dishonest formalisation.

### Mathlib infrastructure gaps (v4.26.0 pin)

| Need | Status |
|------|--------|
| Finite-graph Euler trail (`SimpleGraph.Walk.IsEulerian`) | ✅ Present |
| r-uniform hypergraph type | ❌ Missing |
| Hypergraph Euler walk | ❌ Missing |
| Infinite walk / `SimpleGraph.InfiniteWalk` | ❌ Missing |
| Erdős-Grünwald-Weiszfeld (1936) | ❌ Missing |

### Honest classification

**SURVEY-BLOCKED** at the infrastructure level. The problem.md "WIP" framing
is misleading; the file is a stub. Real progress requires ~700–1300 LOC of
new infrastructure (hypergraph walks + infinite walks + the
Erdős-Grünwald-Weiszfeld theorem) — a multi-month project, not the
problem.md's "1–2 weeks if tractable" estimate.

The cleanest small-scope path is the **r=2 case** (~30 LOC): define
`toSimpleGraph (H : RUniformHypergraph V 2) : SimpleGraph V` and prove the
iff `HasEulerTour H ↔ ∃ u v (w : (toSimpleGraph H).Walk u v), w.IsEulerian`.
This replaces one of the three `True` placeholders with a real definition.

### Anti-scope (this PR)

* No Lean edits — definitional choices for the `True` placeholders are
  themselves non-trivial design decisions; rushing them locks in a bad shape.
* No child OQ slug creation — defer to a session that commits to a specific
  definitional approach.
* No new theorems — the file has no theorems to extend; the missing
  infrastructure must come first.
* No `True` → `sorry` rewrite — would force a definitional commitment.

### S3 candidate menu

* **A**: Implement the r=2 case (~30 LOC). Smallest concrete win, fully
  dischargable using `SimpleGraph.Walk.IsEulerian`.
* **B**: Convert the 3 `True` placeholders to `sorry`-guarded honest stubs
  (~3 LOC change). Lays foundation without committing to definitional shape.
* **C**: Pivot to a different slug if no infrastructure work is in scope.
* **D**: Open child sub-OQs (`-oq-01` for r=2, `-oq-02` for hypergraph walk
  infrastructure, etc.) to formalise a 4-step decomposition in separate slugs.

## Active Approach

None — SURVEY only this iteration. Future iterations should pick from
S3 candidates A–D (recommend A for smallest concrete forward step).

## Attempt Count

- Total attempts: 1 (this S2 SURVEY)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers

**Infrastructure-level**: full completion needs ~700–1300 LOC of hypergraph
walk + infinite walk + Erdős-Grünwald-Weiszfeld infrastructure not present
in Mathlib v4.26.0. No session-level INFRA blocker — Docker is GREEN, disk
61 Gi GREEN; only `proofs/.lake` self-symlink remains RED but Docker
bypasses.

## Next Action

S3 candidate A (r=2 case) is the recommended next step: ~30 LOC, fully
dischargable, replaces one `True` placeholder with real content. Requires a
follow-up session committing to the definitional approach (this S2 SURVEY
documents the choice space but does not commit).

## Iteration history

| # | Date | Researcher | Mode | Summary |
|--:|------|------------|------|---------|
| S1 | 2026-04-04 | (init) | OBSERVE | Initial slug creation; problem.md + state.md scaffolds; no knowledge.md / no Lean edits |
| S2 | 2026-05-30 | researcher-1 | SURVEY | Honest gap assessment: 3 `True` placeholders are the real gaps; r=2 case (~30 LOC) is the cleanest forward step (this PR, doc-only) |
