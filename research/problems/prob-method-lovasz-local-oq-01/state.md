# Research State: prob-method-lovasz-local-oq-01

## Current State
**Phase**: S1 OBSERVE (complete)
**Path**: full
**Since**: 2026-05-12
**Iteration**: 1

## Current Focus

S1 OBSERVE complete: surveyed the open question, decomposed into three
sub-tasks (OQ-01-A / OQ-01-B / OQ-01-C), surveyed Mathlib API readiness,
and identified the duplication with `lovasz-local-lemma-oq-03`.

Next action: **S2 ACT — OQ-01-A skeleton**. Create `Proofs/MoserTardos.lean`
with the algorithm definition (`MTProblem`, `MTState`, `step`, `run`) and
sorry-listed statements of `mt_expected_step_bound` and `mt_terminates_as`.
Build-verify under Docker.

## Active Approach

**Approach 2** — Direct witness-tree proof (Moser–Tardos 2010 §4),
decomposed into:

- **OQ-01-A**: Algorithm + probability space (PMF-based finite model)
- **OQ-01-B**: Witness trees + tree-probability bound
- **OQ-01-C**: Galton-Watson / generating-function sum to `xᵢ/(1-xᵢ)`

Approach 1 (symmetric-only) and Approach 3 (entropy-compression) explicitly
rejected as insufficient for the full OQ — see `problem.md`.

## Attempt Count
- Total attempts: 1 (S1 only)
- Current approach attempts: 0 (S2 not yet started)
- Approaches considered: 3 (recommended: Approach 2 with A/B/C decomposition)

## Blockers

- **Mathlib gap**: no Galton–Watson branching-process API. Mitigation: use
  direct generating-function calculation in OQ-01-C.
- **Mathlib gap**: no general "rooted labelled tree" type. Mitigation: define
  `inductive WitnessTree` from scratch in OQ-01-B.
- **Sibling duplication**: `lovasz-local-lemma-oq-03` is the same problem.
  Coordinate at S2; do not block S2 on dedup.

## Next Action

**S2 ACT — Algorithm skeleton in `Proofs/MoserTardos.lean`**:

1. Define:
   - `structure MTProblem` — (n variables, m events, alphabets, dep graph)
   - `def MTState`, `def isViolated`, `def step` (one resampling), `def run`
2. State (with `sorry`):
   - `theorem mt_expected_step_bound`
   - `theorem mt_terminates_as`
3. Build-verify with Docker.
4. Open PR titled `research(prob-method-lovasz-local-oq-01): S2 ACT — algorithm
   skeleton + sorry-listed bound`.

## Open Sub-Tasks (Roadmap)

| Step | Deliverable | Tractability | Est. LOC |
|------|-------------|--------------|----------|
| S1 OBSERVE (done) | problem.md / knowledge.md / state.md / JSON | trivial | 1100 markdown |
| S2 ACT OQ-01-A | algorithm skeleton + bounded stmts | medium | ~300 LOC, 1-2 PRs |
| S3-S5 OQ-01-B | witness trees + tree-prob bound | hard | ~500 LOC, 2-3 PRs |
| S6-S8 OQ-01-C | Galton–Watson sum bound | hard | ~400 LOC, 2-3 PRs |
| S9 complete | Final integration + bound proof | medium | ~100 LOC |

Total estimated: 5-8 PRs after S1, comparable to a marquee sub-theorem.
