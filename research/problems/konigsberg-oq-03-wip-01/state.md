# Research State: konigsberg-oq-03-wip-01

## Current State

**Phase**: ACT (S12 — satisfiability witnesses shipped, Docker-GREEN)
**Path**: full
**Since**: 2026-07-24 (S12 ACT, researcher-2)
**Iteration**: 12

## S12 ACT Summary (2026-07-24, researcher-2)

**Mode**: ACT (Lean + tracker sync; Docker-verified GREEN, 8576 jobs).

Shipped the S11 menu item (b) — the file's first *positive* Eulerian results,
new "Satisfiability witnesses (S12)" section (6 decls, 0 sorry / 0 axiom):

- **`rayGraph : InfiniteGraph ℕ`** (`m ~ n` iff consecutive) + **`rayWalk`**
  (identity walk) + **`rayWalk_isEulerWalk`** →
  **`rayGraph_hasOneWayEulerPath`** — first witness for `HasOneWayEulerPath`.
  Coverage: edge `{n, n+1}` traversed at step `n` (`⟨u, rfl, h⟩` in the
  matching direction branch); injectivity: identity-walk `sameEdge` reduces to
  linear equations, `omega` closes both branches.
- **`lineGraph : InfiniteGraph ℤ`** + **`lineWalk : BiInfiniteWalk`** →
  **`lineGraph_hasInfiniteEulerPath`** — first witness for
  `HasInfiniteEulerPath` (ℤ-identity walk on the two-ended line).
- **`rayGraph_arcSet_infinite` / `lineGraph_arcSet_infinite`** — each witness
  paired with the S11 finite-arc impossibility in contrapositive: Euler path ⇒
  infinitely many arcs. Closes the S11↔S12 loop.

**S13 menu**: (a) `¬ HasInfiniteEulerPath rayGraph` (one-ended ⇒ no bi-infinite
path: bounded ℤ-tail pigeonholes into finitely many arcs, unbounded tails cross
every high edge twice — discrete-crossing argument, ~100+ LOC); (b)
`¬ HasOneWayEulerPath lineGraph` (same mechanism); (a)+(b) would prove the two
predicates incomparable (ray: one-way ✓ / bi-infinite ✗; line: converse) — the
natural EGW-flavored next result. (c) EGW necessity for locally finite graphs
(S12 menu item (a), unchanged). Session memo:
`sessions/2026-07-24-s12-act-ray-line-witnesses.md`.

---

## S11 ACT Summary (2026-07-24, researcher-1)

**Mode**: ACT (Lean + tracker sync; Docker-verified GREEN).

**Unblock condition met**: `docker info` OK this session — the S9/S10
verification-blackout blocker is lifted. Shipped S8 candidate menu item (b),
the `_of_finite_edges` generalization, as a new "Finite-edge generalization"
section:

- **`arcSet`** — the directed-arc set `{p : V × V | G.adj p.1 p.2}`.
  Directed arcs beat `Sym2` here: the step map lands in `arcSet`
  definitionally (`w.step_adj n` *is* the membership proof), and arc-set
  finiteness is equivalent to undirected-edge finiteness (2-to-1).
- **`InfiniteWalk.not_isEdgeInjective_of_finite_arcs`** (core, walk-level):
  the step map `n ↦ (vertex n, vertex (n+1))` of an edge-injective walk is
  injective (equal directed arcs at distinct steps hit the `Or.inl` branch of
  `sameEdge`), so it would inject ℕ into the finite arc set —
  `Set.infinite_of_injective_forall_mem` + `Set.Finite.not_infinite`.
  Only the edge-*injectivity* half of the Eulerian condition is needed.
- **`not_hasOneWayEulerPath_of_finite_arcs`** /
  **`not_hasInfiniteEulerPath_of_finite_arcs`** — Euler-path corollaries
  (the ℤ-indexed case extracts injectivity `by_contra` on the index equality,
  since `IsBiInfiniteEulerWalk` states `m ≠ n → ¬sameEdge`).
- **`not_hasOneWayEulerPath_of_finite`** /
  **`not_hasInfiniteEulerPath_of_finite`** — `[Finite V]` corollaries via
  `Set.toFinite`.

These strictly generalize the S5 no-edge and S7 single-edge sanity theorems.

### Net file deltas

| Metric | Before (S7, `origin/main`) | After (S11) | Δ |
|--------|---------------------------|-------------|---|
| LOC | 302 | 373 | +71 |
| theorems | 11 | 16 | +5 |
| defs | 13 | 14 | +1 (`arcSet`) |
| sorries / axioms | 0 / 0 | 0 / 0 | 0 |

Build: `./proofs/scripts/docker-build.sh Proofs.KonigsbergOQ03` →
`✔ [8576/8576] Built Proofs.KonigsbergOQ03 (2.8s)` under the v4.31 toolchain
(first build of this slug since the v4.26 → v4.31 migration — also confirms
the migrated file is GREEN).

**S12 menu**: (a) EGW necessity direction for locally finite graphs
(Euler path ⇒ ≤ 2 odd-degree vertices; needs degree counting over
`infiniteDegree`); (b) satisfiability witness — the ray graph on ℕ
(`adj n (n+1)`) has a one-way Euler path (recommended: small, concrete,
shows `HasOneWayEulerPath` is non-vacuous); (c) cross-slug DRY refactor
(separate claim of `konigsberg-oq-03-oq-02`); (d) EGW proof (multi-week,
blocked route).

---

## S9 flag BLOCKED (2026-06-13, researcher-1)

**Mode**: doc/tracker-only (no Lean touched).

The Lean file is already complete-as-stated for everything verifiable:
**302 LOC, 11 theorems, 0 sorry, 0 axiom** on origin/main (S7 #22934 merged).
The only `:= True` token left is inside a docstring describing past
placeholders, not a live gap. No verifiable forward step exists today:

- **Docker daemon HUNG** (`docker info` rc=124, confirmed this session) and
  CI does not build Lean. The S8 candidate menu (single-edge one-way Euler
  walk; `_of_finite_edges` generalization; cross-slug DRY refactor) is all
  *new* sorry-free Lean — unbuildable/unverifiable until Docker recovers.
- **The core open question is multi-week, not a session task.** The Erdős–
  Grünwald–Weiszfeld (1936) characterization needs König's-lemma compactness
  machinery not aggregated in Mathlib v4.26.0 (>1000 LOC foundational); the
  r ≥ 3 hypergraph Euler-tour decision problem is NP-complete (Lonc–Naroski
  2010), so it has no degree-condition closed form to formalize.

This slug has now had two doc-only STATE-SYNCs (S6, S8); a third would be
PREP churn. Flagging BLOCKED so it is not re-claimed during the blackout.
**Unblock when:** Docker recovers (then pursue S8 menu items 1–3, each
Docker-verifiable in a ~30s cycle), or commit multi-week EGW infrastructure.

Files touched (1): this state.md block + iteration-history table back-fill
(S6/S7/S8/S9 rows were missing — the head narrative had advanced past them).

---

## S8 STATE-SYNC Summary (2026-06-13, researcher-1)

**Mode**: STATE-SYNC (doc/tracker-only; no Lean touched).

Two drifts corrected after **S7 ACT (#22934)** merged ("single-edge graphs
have no infinite Euler path", +2 sorry-free theorems):

1. **JSON `leanFiles` was stale at S4-era values** (202 LOC / 2 thm / 14 def)
   — never updated through S5 (256/9) or S7. Corrected to the canonical
   origin/main counts: **303 LOC** (`wc -l` 302 + 1) / **11 thm** / **13 def**
   / 0 sorry / 0 axiom.
2. **state.md head was at S6** while JSON `currentState` had advanced to
   S7/S8 — this block re-aligns the human narrative.

**No S9 ACT this session**: verification blackout 2026-06-13 (Docker daemon
HUNG, `docker info` rc=124; Aristotle backend 404). The S8 candidate menu is
all new sorry-free Lean (single-edge one-way Euler walk; `_of_finite_edges`
generalization; cross-slug DRY refactor) — unbuildable/unverifiable today, and
CI does not build Lean, so deferred until Docker recovers rather than
blind-shipped. File is already 0-sorry / 0-axiom, so no urgency.

Files touched (2): this state.md block + JSON `leanFiles` / `currentState`.

---

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
| S5 | 2026-06-04 | researcher-1 | ACT | Sibling-parity accessors (`step_is_adj` / `covers` / `injective`) + four no-edge sanity theorems (walk types `IsEmpty` and Eulerian predicates `False` for no-edge graphs). 202 → 256 LOC (+54), 2 → 9 theorems. S4 ACT's S5 "trivial closure lemma" suggestion corrected (constant walk doesn't satisfy `step_adj`; no-edge non-existence is the correct dual). Build NOT verified (Docker daemon still broken). (PR #22592) |
| S6 | 2026-06-09 | researcher-1 | STATE-SYNC | Docker recovered (Server 29.5.3): `✔ [7743/7743] Built Proofs.KonigsbergOQ03 (24s)`. S4 + S5 ACTs retroactively Docker-verified GREEN; closed the 5-day build-verification gap. 0 LOC. |
| S7 | 2026-06-09 | researcher-1 | ACT | Single-edge `InfiniteGraph` has no infinite Euler path: +2 sorry-free theorems. 256 → 302 LOC, 9 → 11 theorems, 0 sorry / 0 axiom. (PR #22934, merged) |
| S8 | 2026-06-13 | researcher-1 | STATE-SYNC | Corrected stale JSON `leanFiles` (S4-era 202/2/14 → canonical 303/11/13) and re-aligned state.md head (was at S6) to the merged S7 state. No Lean touched; verification blackout (Docker hung, Aristotle 404). |
| S9 | 2026-06-13 | researcher-1 | BLOCKED | Flag BLOCKED: Docker still hung (`docker info` rc=124); S8 candidate menu is all new sorry-free Lean (unverifiable today) and the core OQ (EGW characterization / r≥3 NP-completeness) is multi-week open infrastructure. File already 0-sorry / 0-axiom; no urgency. Back-filled S6–S9 iteration rows. (this PR) |
| S10 | 2026-06-14 | researcher-3 | STATE-SYNC | Propagated the S9 BLOCKED decision into the canonical JSON: it was still `status:"active"` / `phase:"STATE-SYNC"` / iter 8, so claim-random kept re-serving the slug during the blackout. Set `status:"blocked"` / `phase:"BLOCKED"` / iter 9, populated `blockers`, rewrote `nextAction` as the unblock plan, fixed `leanFiles.lineCount` 303→302 (`wc -l`=302), and back-filled `progressHistory` rows S5–S9 (canonical array had stopped at S4). Docker still down (`docker info` rc=124, confirmed). No Lean touched. (this PR) |
| S11 | 2026-07-24 | researcher-1 | ACT | Docker recovered — unblocked. Shipped S8 menu item (b): `arcSet` def + 5 sorry-free finite-edge impossibility theorems (`InfiniteWalk.not_isEdgeInjective_of_finite_arcs` core + finite-arc and `[Finite V]` Euler-path corollaries), strictly generalizing the S5 no-edge and S7 single-edge results. 302 → 373 LOC, 11 → 16 theorems, 0 sorry / 0 axiom. Docker-GREEN under v4.31 (8576 jobs, 2.8s — first post-migration build of this slug). JSON un-blocked (`status:"active"`, EGW / r≥3 routes recorded as structured blockers). (this PR) |
