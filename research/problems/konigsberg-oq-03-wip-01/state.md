# Research State: konigsberg-oq-03-wip-01

## Current State

**Phase**: STATE-SYNC (S6 — S4+S5 Docker-GREEN retroactive verification at T+6d/T+5d; build-uncertainty banner removed)
**Path**: full
**Since**: 2026-06-09 (S6 STATE-SYNC, researcher-1)
**Iteration**: 6

## S6 STATE-SYNC Summary (2026-06-09, researcher-1)

**Mode**: STATE-SYNC (doc-only; Docker build closure of S4 ACT 2026-06-03 + S5 ACT 2026-06-04 unverified work).

`./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ03` →
`✔ [7743/7743] Built Proofs.KonigsbergOQ03 (24s)` → `Build completed successfully (7743 jobs)`.

Both S4 ACT (T+6d) and S5 ACT (T+5d) are now **retroactively Docker-verified GREEN**. The host Docker daemon recovered between 2026-06-04 and 2026-06-09 (Server Version 29.5.3, overlayfs storage); both ACTs' code is correct as written. This closes the 5-day build-verification gap that S4 + S5 explicitly flagged.

| Session | Delta | Build status |
|---------|-------|--------------|
| S4 ACT (2026-06-03) | +88 LOC, +1 thm, discharged 2 `True` placeholders | **Retroactively GREEN at S6** |
| S5 ACT (2026-06-04) | +54 LOC, +7 thm | **Retroactively GREEN at S6** |
| S6 STATE-SYNC (this) | 0 LOC | Docker GREEN: 7743 jobs, 24s |

File invariants at S6 (matches both S5 and origin/main): 256 LOC, 9 theorems, 14 defs+structures, 0 axioms, 0 sorries. Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) unchanged.

**S7 candidate menu** (carried forward verbatim from S5, now empirically validated):

1. **(EGW statement)** — state EGW as a `theorem ... := by sorry`. ~5 LOC + def.
2. **(one-edge graph Euler walk)** — `¬ HasInfiniteEulerPath G` for a single-edge `InfiniteGraph`. ~20 LOC.
3. **(sibling DRY refactor — cross-slug)** — collapses ~100 LOC across parent + `KonigsbergOQ03OQ02`.
4. **(EGW proof — multi-week)** — locally-finite case via König's lemma.

**Recommended for S7**: (1) + (2) in one session — both small, both concrete, both Docker-verifiable in a ~30s cycle now that Docker is restored.

Full record in `sessions/2026-06-09-s6-statesync-docker-green-retroactive.md`.

---

## Prior State (S5 ACT, 2026-06-04)

## S5 ACT Summary (2026-06-04, researcher-1)

**Mode**: ACT (theorems only; build NOT verified at write time — Docker daemon broken on host; **retroactively Docker-GREEN at S6 STATE-SYNC 2026-06-09**).

Added **7 small theorems** in two groups:

1. **Three sibling-parity accessors** (`InfiniteWalk.step_is_adj`,
   `IsEulerWalk.covers`, `IsEulerWalk.injective`) ported line-for-line
   from `KonigsbergOQ03OQ02.lean`. Brings the parent's `InfiniteWalk` /
   `IsEulerWalk` API into parity with the sibling.

2. **Four no-edge sanity theorems** — for an `InfiniteGraph` with no
   adjacencies: walk types are `IsEmpty`, and the
   `HasOneWayEulerPath` / `HasInfiniteEulerPath` predicates evaluate
   to `False`. These confirm the S4-discharged predicates are
   non-degenerate.

### Net file deltas

| Metric | Before (S4 ACT, `origin/main`) | After (this S5 ACT) | Δ |
|--------|--------------------------------|---------------------|---|
| LOC | 202 | 256 | +54 |
| theorems | 2 | 9 | +7 |
| defs+structures | 14 | 14 | 0 |
| `:= True` placeholders | 0 | 0 | 0 |
| sorries | 0 | 0 | 0 |
| axioms | 0 | 0 | 0 |

The S4 ACT's recommended S5 candidate "trivial closure lemma" originally
suggested a constant `InfiniteWalk` on a no-edge graph as a vacuous
`IsEulerWalk`. That proposal is mathematically wrong:
`InfiniteGraph.loopless` forbids `G.adj v v`, so no constant walk
satisfies `step_adj`. This S5 ACT delivers the *correct* dual: when
there are no edges, no walk exists at all. The resulting
`isEmpty_of_no_edges` theorems are 1-line term proofs grounded in the
`step_adj` field of the walk structures.

### Build status — NOT verified locally

Same Docker breakage as the S4 ACT memo. Confidence grounded in:

* **Pattern equivalence**: the three accessors are line-for-line ports
  of sibling theorems that already build under `Mathlib v4.26.0`.
* **Trivial term proofs**: every theorem reduces to a single field
  projection (`w.step_adj 0`, `hEuler.1`, `hEuler.2`) or
  `rintro ⟨w, _⟩; exact h _ _ (w.step_adj 0)`.
* **No new imports**: `IsEmpty`, `rintro` are all `import Mathlib`-resident.

See `sessions/2026-06-04-s5-act-accessors-and-no-edge-sanity.md` for the
full implementation walkthrough and the S6 candidate menu.

## Prior State (S4 ACT, 2026-06-03)

## S4 ACT Summary (2026-06-03, researcher-1)

**Mode**: ACT (Lean infrastructure port + bindings; build NOT verified — Docker daemon corrupted on this host, see session memo).

Discharged the **remaining two `:= True` placeholders** in
`proofs/Proofs/KonigsbergOQ03.lean` — `HasInfiniteEulerPath` and
`HasOneWayEulerPath` — by porting the ℕ-indexed `InfiniteWalk` /
ℤ-indexed `BiInfiniteWalk` formalisation pattern already shipped in
sibling file `Proofs/KonigsbergOQ03OQ02.lean`, adapted to use the
parent's own `InfiniteGraph` structure (avoiding the sibling's
locally-redeclared duplicate).

The S3 ACT's "S4 candidate option 3 (parent-companion survey)" surfaced
the sibling's existing infrastructure (~85 LOC of `InfiniteWalk` /
`IsEulerWalk` / `BiInfiniteWalk` / `IsBiInfiniteEulerWalk` definitions),
eliminating the need for the S2 SURVEY's projected from-scratch
~200-400 LOC infinite-walk build.

### Net file deltas

| Metric | Before (S3 ACT, `origin/main`) | After (this S4 ACT) | Δ |
|--------|--------------------------------|---------------------|---|
| LOC | 114 | 202 | +88 |
| theorems | 1 | 2 | +1 (`InfiniteWalk.step_ne`) |
| defs+structures | 8 | 14 | +6 |
| `:= True` placeholders | 2 | **0** | **−2** |
| sorries | 0 | 0 | 0 |
| axioms | 0 | 0 | 0 |

The slug is now fully placeholder-free. All three Eulerian predicates
— `HasEulerTour` (r=2 hypergraphs, S3 ACT), `HasInfiniteEulerPath`
(bi-infinite, this S4 ACT), `HasOneWayEulerPath` (one-way infinite,
this S4 ACT) — are bound to genuine mathematical content via
`SimpleGraph.Walk.IsEulerian` / `IsEulerWalk` / `IsBiInfiniteEulerWalk`.

### Build status — NOT verified locally

Docker daemon on this host is broken (containerd content-store I/O
error reading the `lean4-arm64:v4.26.0` image's blob; the image cannot
be inspected or rebuilt without user intervention). Build verification
deferred to CI / next-auditor pass. Confidence in the code grounded in:

- **Pattern equivalence**: every new declaration is a near-line-for-line
  copy of a sibling-file declaration in `KonigsbergOQ03OQ02.lean`,
  which is in the gallery and demonstrably builds under the same
  `Mathlib v4.26.0` pin.
- **No new imports**: parent already has `import Mathlib`; new code
  uses only Mathlib-resident symbols (`ℕ`, `ℤ`, `Set`, `≠`, `∃`, `∨`, `∧`).
- **Only adaptation**: substituted the sibling's locally-redeclared
  `InfiniteGraph` with the parent's own (identical fields / signature).

See `sessions/2026-06-03-s4-act-infinitewalk-discharge.md` for the full
implementation walkthrough, design-decision rationale, the
parent-sibling DRY refactor opportunity (queued in
`konigsberg-oq-03-oq-02` slug's next-action), and S5 candidate menu.

## Prior State (S3 ACT, 2026-06-01)

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

All three Eulerian predicates remain bound to genuine content; the
slug is **placeholder-free with 9 theorems** (up from 2 at S4). API
parity with sibling `KonigsbergOQ03OQ02` is now in place
(`step_is_adj` / `covers` / `injective` accessors), and the
predicates are confirmed non-degenerate via the no-edge sanity
theorems. See `## Next Action` for S6 candidate menu (EGW statement,
one-edge graph, sibling DRY refactor).

## Attempt Count

- Total attempts: 4 (S2 SURVEY + S3 ACT r=2 case + S4 ACT infinite/bi-infinite predicates + this S5 ACT accessors+no-edge sanity)
- Current approach attempts: 1 (S5: trivial closure lemma via no-edge non-existence + sibling-parity accessors)
- Approaches tried: 3

## Blockers

**None at the infrastructure level for the *predicate-definition* stage.**
All three placeholder definitions now resolve to meaningful Props. Remaining
blockers concern the *theorem-statement and proof* stage:

* **Erdős–Grünwald–Weiszfeld theorem proof**: still requires ~150–300 LOC
  of graph-theoretic compactness / König's lemma machinery, much of
  which exists in Mathlib but the combination has never been assembled
  for the EGW characterisation. Multi-week project for a single
  researcher.
* **Pure-hypergraph r ≥ 3 Euler tour decidability**: NP-complete
  (Lonc–Naroski 2010), so the formalisation target would shift from
  "characterising existence" to "proving NP-completeness", which is a
  separate complexity-theory project entirely.

## Next Action

**S6 candidate menu**:

* **(EGW statement)** State the Erdős–Grünwald–Weiszfeld characterisation
  as `theorem ... := by sorry` once a `Connected` predicate is committed
  for `InfiniteGraph`. ~5 LOC + supporting def. Useful Aristotle target.
* **(one-edge graph Euler walk)** For an `InfiniteGraph` with exactly
  one edge `{u, v}`, prove `¬ HasInfiniteEulerPath G` (a single edge
  cannot support a non-repeating bi-infinite walk). Smaller than EGW,
  exercises the `IsEdgeInjective` condition. ~20 LOC.
* **(sibling DRY refactor — cross-slug)** Claim
  `konigsberg-oq-03-oq-02`, refactor the sibling to import this parent
  and drop its locally-redeclared `InfiniteGraph` / `InfiniteWalk` /
  `IsEulerWalk` / `BiInfiniteWalk` duplicates. Collapses ~100 LOC of
  duplication. Pure refactor, no new math.
* **(EGW proof — multi-week)** Prove the locally-finite case of EGW
  using `SimpleGraph.Walk.IsEulerian` extension lemmas + König's
  lemma. Requires assembling graph-theoretic compactness machinery
  not yet aggregated in Mathlib for this purpose.
* **(skip)** Park this slug as theorem-rich-but-EGW-deferred and
  return to other slugs.

Recommended for S6: (EGW statement) + (one-edge graph) in one
session — both small, both concrete. Sibling DRY refactor remains a
separate claim.

## Iteration history

| # | Date | Researcher | Mode | Summary |
|--:|------|------------|------|---------|
| S1 | 2026-04-04 | (init) | OBSERVE | Initial slug creation; problem.md + state.md scaffolds; no knowledge.md / no Lean edits |
| S2 | 2026-05-30 | researcher-1 | SURVEY | Honest gap assessment: 3 `True` placeholders are the real gaps; r=2 case (~30 LOC) is the cleanest forward step (PR #21222, doc-only) |
| S3 | 2026-06-01 | researcher-1 | ACT | r=2 Euler-tour case implemented per S2 SURVEY candidate A: `toSimpleGraph` map + meaningful `HasEulerTour` def via `SimpleGraph.Walk.IsEulerian` + sanity lemma. 74 → 114 LOC (+40), 0 → 1 theorem, 7 → 8 defs, `True` placeholders 3 → 2. Docker build verified clean (PR a8a1307aecf / #21877) |
| S4 | 2026-06-03 | researcher-1 | ACT | Discharged remaining 2 `True` placeholders by porting sibling `KonigsbergOQ03OQ02.lean`'s `InfiniteWalk` / `BiInfiniteWalk` / `IsEulerWalk` / `IsBiInfiniteEulerWalk` infrastructure adapted to parent's own `InfiniteGraph`. 114 → 202 LOC (+88), 1 → 2 theorems, 8 → 14 defs, `True` placeholders 2 → 0. Build NOT verified (Docker daemon broken on host). (PR #22179) |
| S5 | 2026-06-04 | researcher-1 | ACT | Sibling-parity accessors (`step_is_adj` / `covers` / `injective`) + four no-edge sanity theorems (walk types `IsEmpty` and Eulerian predicates `False` for no-edge graphs). 202 → 256 LOC (+54), 2 → 9 theorems. S4 ACT's S5 "trivial closure lemma" suggestion corrected (constant walk doesn't satisfy `step_adj`; no-edge non-existence is the correct dual). Build NOT verified (Docker daemon still broken). (this PR) |
