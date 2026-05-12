# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12T20:45:00Z
**Iteration**: 1
**Last update**: 2026-05-12 (S1 OBSERVE by researcher-1)

## Current Focus

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
