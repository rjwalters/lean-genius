# Current State

**Phase**: ACT (S6 — `sperner_parity_hyper` closed; **file at 0 sorries, 0 axioms, Docker-verified**)
**Since**: 2026-05-12T20:45:00Z (S1 OBSERVE)
**Iteration**: 15
**Last update**: 2026-06-12 (researcher-2) — **S6 ACT**: closed the final sorry `sperner_parity_hyper` by adding three Σ-type bookkeeping lemmas (`per_cell_door_parity_hyper`, `card_doors_eq_sum_hyper`, `doors_partition_hyper`) mirroring the verified parent helpers, then transcribing the parent `sperner_parity` calc. Only non-mechanical step: product→Σ bridge uses `Fintype.sum_sigma` (forward) in place of parent's `← Fintype.sum_prod_type'`. **Also fixed a latent S5 compile bug**: line 203 referenced `SpernerMathlib.door_count_parity`, but the parent declares it in `namespace Sperner` (no `SpernerMathlib` namespace exists) — S5 was never Docker-verified so the broken reference never surfaced; corrected to `Sperner.door_count_parity`. File 462 → 557 LOC. Sorries 1 → 0. **Docker-verified** (`Proofs.SpernerMathlibHyper`, 7744 jobs, exit 0). See `sessions/2026-06-12-s6-act-sperner-parity-hyper-closed-zero-sorries.md`.

| Session | Date | Mode | PR | Title / focus | LOC |
|---|---|---|---|---|---|
| **S2 ACT** | 2026-05-31 | ACT | #21489 | Ship `SpernerMathlibHyper.lean` 289 LOC / 3 sorries / 0 axioms — hypergraph API with `IsDoorHyper`, `IsPanchromaticHyper`, `adjMapHyper`, door-transfer lemmas, structural sorries per S2c/S2d/S2e PREP. | +289 |
| **S3 ACT** | 2026-06-01 | ACT | #21683 | Close strict case of `door_count_parity_hyper` (~38 LOC pigeonhole). Equality case remains as the sole sorry inside the by_cases. | +55/-2 |
| **S4 ACT** | 2026-06-04 | ACT | (#22???) | Close `even_card_interior_doors_hyper` via `Sperner.even_card_fpf_invol` on `adjMapHyper adj`. 41-LOC body; +40 LOC net. Sorries 3 → 2. Two PREP-unanticipated elaboration quirks (match non-reduction under `simp only`; structure-eta as rfl). | +40 |
| **S5 ACT** | 2026-06-05 | ACT | (merged) | Close `door_count_parity_hyper` equality case via `Fintype.equivFinOfCardEq` + `Equiv.swap` transport to `Sperner.door_count_parity n f'`. ~80-LOC body; bearers from S2d PREP except `Fin.eq_castSucc_of_ne_last` replaced with explicit pigeonhole. Sorries 2 → 1. (Shipped with a broken `SpernerMathlib.door_count_parity` ref — never Docker-verified; fixed in S6.) | +80 |
| **S6 ACT** | 2026-06-12 | ACT | (this PR) | Close `sperner_parity_hyper` (final sorry) via 3 Σ-type bookkeeping lemmas mirroring parent helpers + `Fintype.sum_sigma` product→Σ bridge; fix S5 `Sperner`-namespace ref. **File at 0 sorries, 0 axioms, Docker-verified (7744 jobs).** Sorries 1 → 0. | +95 |

## Session Log (STATE-SYNC, 2026-05-13, researcher-1)

state.md had drifted from "Phase: OBSERVE / Iteration 1 / lastUpdate
2026-05-12T20:45" to its current frozen form after **nine** subsequent
merged sessions (S1b/S1c/S1d/S1e/S2 PREP/S2 PREP audit/S2c/S2d/S2e),
each landing a doc-only PREP/OBSERVE PR that left state.md untouched.
This STATE-SYNC adds 1-entry-per-merged-session and refreshes Phase /
Iteration / Last Update so a returning agent can pick up cold.

| Session | Date | Mode | PR | Title / focus | LOC |
|---|---|---|---|---|---|
| S1 | 2026-05-12 | OBSERVE | #18282 | Axioms audit + hypergraph weakening map — (captured in original S1 Summary below) | +400 |
| **S1b** | 2026-05-12 | OBSERVE | #18344 | `IsDoorHyper` top-color gap — the `knowledge.md` § 4.1 proposed `IsDoorHyper` lacked a top-color asymmetry needed for the parity argument; fix is parameterise on a fixed `top : P`. | doc |
| **S2 PREP** | 2026-05-12 | PREP | #18360 | Σ-type ergonomics + file skeleton for `SpernerMathlibHyper.lean` — concrete adjMap / dependent-index ergonomics analysis; ships the file skeleton (not the file itself). | doc |
| **S1c** | 2026-05-13 | OBSERVE | #18366 | `hadj_ne` strong/weak mismatch — identifies a precise hypothesis-form mismatch in the hypergraph generalisation; refines knowledge.md § 2.3 (OQ-01-C minimality). | +413 |
| **S1d** | 2026-05-13 | OBSERVE | #18387 | `hadj_ne` derivability + self-loop classification — extends S1c by classifying the self-loop corner case and showing partial derivability of `hadj_ne` under stronger boundary hypotheses. | +407 |
| **S1e** | 2026-05-13 | OBSERVE | #18411 | Per-cell door parity by color multiplicity — introduces the `hι_size : ∀ s, |ι s| ≤ |P|` constraint, refines the per-cell parity step, and surfaces the non-pure-complex multiplicity-parity argument. | +301 |
| **S2 PREP audit** | 2026-05-13 | PREP | #18638 | `hι_size` integration into S2 PREP skeleton + Mathlib v4.26.0 API audit — 5 Mathlib names verified at SHA `2df2f01` via Contents API; integrates the S1e constraint into the S2 PREP file skeleton. | doc |
| **S2c PREP** | 2026-05-13 | PREP | #18688 | Cardinality dichotomy + Equiv-transport for `door_count_parity_hyper` — splits the parity proof into a two-case architecture (`|ι s| = |P|` vs `|ι s| < |P|`) with Equiv-transport on the equality side; ships skeleton with 2 sub-sorries. | doc |
| **S2d PREP** | 2026-05-13 | PREP | #18727 | Fills S2c PREP sub-sorries with concrete Mathlib bearer chains — promotes the S2c skeleton from "2 sub-sorries" to a complete paste-ready proof recipe for the S2 ACT implementer. | +617 |
| **S2e PREP** | 2026-05-13 | PREP | #18788 | `even_card_interior_doors_hyper` Σ-pair involution bearer chain — orthogonal to door_count_parity_hyper; surfaces 4 Σ-bearers not previously cited (`Sigma.instFintype`, `instDecidable…`, etc.). | doc |

**Cumulative doc footprint**: 9 session markdown files in `sessions/` +
`problem.md` + `knowledge.md` + this `state.md` = ~1.8K LOC of analysis.
**Zero Lean changes across all 9 sessions.** `proofs/Proofs/SpernerMathlibHyper.lean`
(target of S2 ACT) has NOT yet been created on `main`.

## ACT readiness assessment (post-STATE-SYNC)

- **S2 ACT** is ready to ship `proofs/Proofs/SpernerMathlibHyper.lean` (~120 LOC,
  0–1 strategic sorries) integrating: (a) S2 PREP file skeleton (#18360); (b) S1e
  `hι_size` constraint (#18411); (c) S2 PREP audit Mathlib bearers (#18638);
  (d) S2c+S2d two-case `door_count_parity_hyper` recipe (#18688 + #18727); (e) S2e
  Σ-pair involution recipe for `even_card_interior_doors_hyper` (#18788); (f) S1b
  top-color asymmetry fix (#18344).
- **S2 ACT scope**: hypergraph-generalised API (`IsDoorHyper`, `IsPanchromaticHyper`,
  `even_card_interior_doors_hyper`, `door_count_parity_hyper`, `sperner_parity_hyper`,
  `exists_panchromatic_hyper`). Build-pending convention applies (worktree `.lake`
  recursive). The Σ-type ergonomics is the highest-risk surface; mitigated by S2
  PREP's pre-audited `Sigma.casesOn` / `match` translation.
- **Non-pure complex (OQ-01-B)**: deferred per S1 §5 + S1e refinement. The
  per-cell parity argument now has an explicit multiplicity-based form (S1e) that
  is workable but cosmetically heavier than the pure top-dim restriction reduction.
- **Boundary-axioms minimality (OQ-01-C)**: S1c + S1d refined `hadj_ne` analysis;
  the load-bearing status is preserved (recommendation: keep as axiom).

**Recommended next session**: S2 ACT — `SpernerMathlibHyper.lean` (~120 LOC).
Build-pending. After S2 ACT lands, S3 closes the strategic sorries (if any)
following S2d's bearer chains.

---

## Original Current Focus (frozen at S1, 2026-05-12T20:45 — researcher-1)

S1 OBSERVE — axiomatic audit of `proofs/Proofs/SpernerMathlib.lean`
(897 lines, 0 sorries) and weakening map for the two open
generalisations posed by the slug: (A) hypergraph generalisation
(cell-dependent index type `ι s`), (B) non-pure complex
generalisation (mixed cell dimensions).

## Active Approach

**Doc-only S1 OBSERVE.** No Lean changes. Deliverable is three
markdown files + one JSON gallery entry:

- `problem.md` — formal signature targets, three sub-OQs (A: hypergraph,
  B: non-pure, C: boundary-axioms minimality), acceptance criteria.
- `knowledge.md` — § 1 axioms inventory, § 2 weakening map per proof
  step, § 3 Mathlib alignment, § 4 S2 formal signature proposal, § 5
  non-pure counter-example sketch, § 6 recommended S2 scope, § 8 risk
  register, § 9 sister-slug compatibility, § 10 cost estimate.
- `state.md` (this file).
- `src/data/research/problems/sperner-mathlib-oq-01.json` —
  gallery entry, status `in-progress`, knowledge payload.

## S1 Summary

### Key findings

1. **Hypothesis-based axiomatisation already exists.** The current
   file uses three named hypotheses (`hadj_symm`, `hadj_vertex`,
   `hadj_ne`) carried as theorem parameters — not a `structure`.
   Generalising to hypergraphs is *not* a structural redesign but a
   *parameter substitution*: replace `Fin (d + 1)` with `ι s`
   throughout.
2. **Pureness is implicit, in the type `Fin (d + 1)`.** Removing
   pureness requires switching to a cell-dependent index type and
   accepting that the parity statement's *meaning* changes (cells of
   different dimensions cannot be panchromatic with respect to a
   common palette of fixed cardinality `d + 1`).
3. **Mathlib does not subsume the abstraction.** Both
   `AbstractSimplicialComplex` (uses `Finset V`, no per-face index)
   and `SimplicialSet` (category-theoretic, much heavier) miss the
   indexed-face data that the parity argument relies on.

### Locked S2 scope (hypergraph generalisation)

- Target file: `proofs/Proofs/SpernerMathlibHyper.lean` (~120 LOC).
- Replace `Fin (d + 1)` with `ι : Cell → Type*` carrying
  `Fintype (ι s)` and `DecidableEq (ι s)`.
- Replace coloring codomain `Fin (d + 1)` with an abstract palette
  `P : Type*` carrying `Fintype P` and `DecidableEq P`. This makes
  the panchromatic predicate dimension-agnostic.
- Adapt `IsDoor`, `IsPanchromatic`, `even_card_interior_doors`,
  `door_count_parity`, `sperner_parity`, `exists_panchromatic` to
  the dependent-index form.
- Net new public API: `IsDoorHyper`, `IsPanchromaticHyper`,
  `even_card_interior_doors_hyper`, `sperner_parity_hyper`,
  `exists_panchromatic_hyper`.
- Build target: 0 sorries if mechanical adaptation works; 1
  strategic sorry tracking the per-cell parity step if not.

### Non-pure complexes (OQ-01-B): deferred

S1 OBSERVE conjectures Sperner's parity *fails* on non-pure
complexes in the literal sense, salvageable only by restriction to
the pure top-dimensional sub-complex. The restriction lemma reduces
to the existing pure case and yields no new mathematical content;
deferred to S3 as a possible corollary, but not a primary deliverable.

A 3-cell sketch (2-simplex + two 1-simplex faces) is included in
`knowledge.md` § 5; a fully formal counter-example requires careful
choice of `vertex` and `adj` to keep the involution well-typed
across dimensions.

### Boundary-axioms minimality (OQ-01-C): partially answered

`hadj_ne` is **load-bearing** under the current axioms because the
corner case `adj s k = some ⟨s, k⟩` (self-face-loop) is admitted by
`hadj_symm` + `hadj_vertex` alone. **Recommendation:** keep
`hadj_ne` as an axiom; deferring removal saves a non-trivial corner-
case argument and the axiom costs one line.

## Blockers

None mathematical. The S2 hypergraph generalisation is a mechanical
adaptation; the only Lean-level risk is `Σ`-type ergonomics in
`adjMap`-style auxiliary definitions, mitigable by `match` /
`Sigma.casesOn`.

**Operational:** worktree `proofs/.lake` is recursive
(`feedback_researcher_lake_symlink_broken.md`); local docker build
is ~25–45 min. S1 OBSERVE is doc-only — no build needed.

## Next Action

**S2 ACT — any researcher.** Create
`proofs/Proofs/SpernerMathlibHyper.lean` with the hypergraph-
generalised API. Concrete starting skeleton in `knowledge.md` § 4.1.

Estimated effort: 60 min focused Lean (most of which is `Σ`-type
manipulation in `adjMap` and `even_card_interior_doors`).

## Attempt Counts

- Total attempts: 1 (S1 OBSERVE)
- Current approach attempts: 1
- Approaches tried: 1 (axiomatic audit + weakening map)

## Open files

- `problem.md` — formal scope and signature targets (this PR).
- `knowledge.md` — axiomatic audit and weakening map (this PR).
- `state.md` (this file).
- (downstream) `proofs/Proofs/SpernerMathlib.lean` — source of the
  axioms being audited; **not touched** in S1.

## Race awareness

OQ-01 has zero open PRs and zero recent merges at push time
(verified 2026-05-12 20:45 UTC via `gh pr list --search "sperner-
mathlib-oq-01 in:title"`). The slug was seeker-selected (recently)
and currently has no prior research activity. Sibling slug
`sperner-simplicial-bridge-oq-01` (PR #18234, merged 2026-05-12
~17:00 UTC) targets a *concrete* simplicial-bridge formalisation —
**not** the abstract hypergraph generalisation here, so there is no
duplication. Re-entry risk: a parallel S1 OBSERVE; mitigated by the
doc-only character (any duplicate work is wasted survey effort, not
proof effort).
