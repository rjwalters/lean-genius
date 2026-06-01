# Research State: konigsberg-oq-03-wip-01

## Current State

**Phase**: ACT (S3, this PR — r=2 case implemented per S2 SURVEY S3 candidate A)
**Path**: full
**Since**: 2026-06-01 (S3 ACT, researcher-1)
**Iteration**: 3

## S3 ACT Summary (2026-06-01, researcher-1)

**Mode**: ACT (Lean + meta sync; build-verified via Docker).

Implemented S2 SURVEY's "S3 candidate A": the r=2 case for `HasEulerTour`.
Replaced the `:= True` placeholder with the meaningful definition

```lean
def HasEulerTour {V : Type*} [DecidableEq V] (H : RUniformHypergraph V 2) : Prop :=
  ∃ u (p : (toSimpleGraph H).Walk u u), p.IsEulerian
```

backed by a new `def toSimpleGraph : RUniformHypergraph V 2 → SimpleGraph V`
(adjacency: `u ≠ v ∧ {u, v} ∈ H.edges`, symm via `Finset.pair_comm`,
loopless via the `u ≠ v` clause) and the sanity lemma
`hasEulerTour_iff_simpleGraph_eulerian` confirming definitional
equivalence to Mathlib's `SimpleGraph.Walk.IsEulerian` (`Combinatorics/SimpleGraph/Trails.lean:79`).

### Net file deltas

| Metric | Before (S2) | After (S3) | Δ |
|--------|-------------|------------|---|
| LOC | 74 | 114 | +40 |
| theorems | 0 | 1 | +1 |
| defs+structures | 7 | 8 | +1 |
| `True` placeholders | 3 | 2 | -1 |
| sorries | 0 | 0 | 0 |
| axioms | 0 | 0 | 0 |

The remaining 2 `True` placeholders (`HasInfiniteEulerPath`,
`HasOneWayEulerPath`) require Mathlib's missing `SimpleGraph.InfiniteWalk`
infrastructure — out of scope for an r=2 iteration. The S2 SURVEY's
"infrastructure-level blocker" remains in force for the infinite-graph
case.

Build verified: `./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ03` (see
S3 session memo for log).

See `sessions/2026-06-01-s3-act-r2-eulertour-implementation.md` for the
implementation walkthrough, design-decision rationale, and update plan for
future iterations.

## Prior State (S2 SURVEY, 2026-05-30, doc-only)

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

Replace remaining `True` placeholders (`HasInfiniteEulerPath`,
`HasOneWayEulerPath`) once Mathlib gains `SimpleGraph.InfiniteWalk` support
OR explicitly construct an `InfiniteWalk` type in this file (out of scope
for a single iteration; would be ~200–400 LOC of new infrastructure).

## Attempt Count

- Total attempts: 2 (S2 SURVEY + this S3 ACT)
- Current approach attempts: 1 (S3 candidate A: r=2 case)
- Approaches tried: 1

## Blockers

**Infrastructure-level (remaining)**: full completion still needs
~500–900 LOC of infinite-walk + Erdős-Grünwald-Weiszfeld infrastructure
not present in Mathlib v4.26.0. The r=2 hypergraph case is now CLOSED
(this S3 ACT). Pure-hypergraph `r ≥ 3` is NP-complete (Lonc-Naroski
2010) and would only formalise as a non-existence-of-poly-time-algorithm
result.

## Next Action

**S4 candidate menu** (future iterations):

* **(infinite-walk path)** Define `InfiniteWalk` as either a stream-based or
  list-extension on the existing `SimpleGraph.Walk`; replace
  `HasInfiniteEulerPath`'s `True` placeholder. ~200–400 LOC. Risk: needs to
  decide between coinductive / `Stream'` / `Walk.append`-iterated approaches.
* **(EGW theorem)** Once `InfiniteWalk` exists, state + prove the
  Erdős-Grünwald-Weiszfeld characterisation (1936). ~150–300 LOC.
* **(parent-companion)** Re-survey the parent file `Proofs/Konigsberg.lean`
  and the sibling file `Proofs/KonigsbergOQ03OQ02.lean` for any shared
  infrastructure work that should land in a common helper module.
* **(skip / new slug)** If infinite-walk machinery is out of scope, open
  a child slug (`konigsberg-oq-03-wip-01-oq-01`) for the EGW formalisation
  specifically and park `konigsberg-oq-03-wip-01` in `axiomatized-stable`
  state until the child completes.

## Iteration history

| # | Date | Researcher | Mode | Summary |
|--:|------|------------|------|---------|
| S1 | 2026-04-04 | (init) | OBSERVE | Initial slug creation; problem.md + state.md scaffolds; no knowledge.md / no Lean edits |
| S2 | 2026-05-30 | researcher-1 | SURVEY | Honest gap assessment: 3 `True` placeholders are the real gaps; r=2 case (~30 LOC) is the cleanest forward step (PR #21222, doc-only) |
| S3 | 2026-06-01 | researcher-1 | ACT | r=2 Euler-tour case implemented per S2 SURVEY candidate A: `toSimpleGraph` map + meaningful `HasEulerTour` def via `SimpleGraph.Walk.IsEulerian` + sanity lemma. 74 → 114 LOC (+40), 0 → 1 theorem, 7 → 8 defs, `True` placeholders 3 → 2. Docker build verified clean. (this PR) |
