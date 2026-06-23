# Problem Selection Report

**Date**: 2026-04-22
**Mode**: SELECT
**Pool Status**: 83 available, 1257 in-progress, 508 (legacy pool), 1 blocked, 3 graduated

## Selected Problem

- **ID**: brouwer-fixed-point-oq-04-oq-02-incomplete-01
- **Name**: Complete Nash Equilibrium Existence via Nash's Brouwer Argument
- **Tier**: B
- **Significance**: 7/10
- **Tractability**: 7/10
- **Knowledge Score**: 0 (EMPTY)
- **Status**: available

## Selection Rationale

1. **EMPTY knowledge tier**: No prior research items — highest priority tier. Composite
   score: `(-0 × 1000) + (7 × 10) + 7 = 77`, tied for top among all unclaimed candidates.

2. **Concrete completion task**: The axiom `brouwer_product_simplex` has a clear proof
   sketch in the parent file — embed `ProductSimplex G` into `Fin(Σᵢ strats i) → ℝ`
   via concatenation, then apply Mathlib's Brouwer FPT. This is well-defined with
   known Mathlib entry points (`InnerProductSpace.PiL2`, finite-dim topology).

3. **High-impact completion**: Removing the last axiom from the Nash equilibrium existence
   proof would give a fully machine-verified Nobel-Prize result (Nash 1950). This is
   meaningful mathematical progress, not a minor cleanup.

4. **Domain diversity**: Recent selections were ptolemy (geometry), fair-games
   (probability), erdos-476 (additive combinatorics). This candidate is topology/game
   theory — diversifying the research queue.

## Rejection Summary

- **Candidates considered**: 83 available (from synced DB pool)
- **Top composite tier (score=77)**: `fourier-series-oq-02-incomplete-01-oq-01` and
  `lebesgue-measure-oq-01-oq-01-oq-01` also scored 77 but were deprioritized:
  - Fourier series candidate: narrower result (one Lipschitz lemma vs. Nobel-level theorem)
  - Lebesgue/Thomae candidate: similarly concrete but lower impact than Nash completion
- **Claimed problems skipped**: area-of-circle-oq-05-oq-02, erdos-268, erdos-476-oq-05,
  fair-games-theorem-oq-02-oq-04, hurwitz-theorem-oq-03-oq-01 (all active claims)
- **RICH knowledge skipped**: erdos-263 (42 items), sperner-ndim-oq-05 (27 items),
  brouwer-fixed-point-oq-04-oq-02 (108 lines), ballot-problem-oq-03-oq-01-oq-02 (278 lines)
- **Confidence**: medium (three-way tie at composite 77 broken by impact assessment)

## Related Gallery Proofs

- `brouwer-fixed-point-oq-04-oq-02`: Direct parent — Nash equilibrium proof using this axiom
- `brouwer-fixed-point`: Base Brouwer FPT proof in the gallery
- `brouwer-fixed-point-oq-04`: Kakutani formulation (alternative approach)

## Suggested First Steps

1. **OBSERVE**: Search Mathlib for Brouwer FPT — try `#check BrouwerFPT` or search for
   `brouwer` in Mathlib4. Key candidates: `Mathlib.Topology.Algebra...` fixed point lemmas.

2. **ORIENT**: Check if `ProductSimplex G` is `IsCompact` and `Convex ℝ` in Lean 4.
   The key type is `MixedProfile N G = (i : Fin N) → MixedStrategy (G.strategies i)`
   with `MixedStrategy n ⊆ Fin n → ℝ`. Is this a `NormedAddCommGroup`?

3. **DECIDE**: Draft a `BrouwerFixedPointOQ04OQ02Aristotle.lean` companion file exposing
   the sub-lemmas (compact/convex/embedding) for Aristotle proof search. The main
   axiom → theorem conversion may benefit from Aristotle's tactic search.

## Pool Summary After Selection

| Status | Count |
|--------|-------|
| Available | 83 |
| In Progress | 1257 |
| Completed | 93 |
| Graduated | 3 |
| Blocked | 1 |
| Total | 1938 |

Note: Pool was re-synced from DB during this run. Previous `.lean/state/candidate-pool.json`
showed only 25 available due to staleness. Now updated to reflect all 83 DB-available problems.

## Candidate Pool Health

- Pool depth: **adequate** (83 available >> threshold of 15)
- DB was the source of truth: 83 problems available vs. 25 in stale pool file
- Pool file re-synced via `python3 research/db/sync_pool.py` + copy to `.lean/state/`
- Next refresh recommended: Next scheduled seeker run (30 min)

## Initialized

- [x] Research workspace: `research/problems/brouwer-fixed-point-oq-04-oq-02-incomplete-01/`
- [x] problem.md populated with axiom details and proof sketch
- [x] state.md: OBSERVE phase
- [x] knowledge.md: template with key facts
- [x] Data file: `src/data/research/problems/brouwer-fixed-point-oq-04-oq-02-incomplete-01.json`
- [x] DB entry verified (status: available)
- [x] Pool file synced
- [ ] Ready for /researcher
