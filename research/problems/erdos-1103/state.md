# Current State

**Phase**: COMPLETED (axiomatized — refutation)
**Since**: 2026-01-15T15:24:14.877Z
**Last Updated**: 2026-04-27T19:08:00Z
**Iteration**: stable — no further work pending

## Current Focus

None — the formalization captures the **refutation** of the conjecture.

## Active Approach

None.

## Blockers

None. The mathematical situation is:

- **Erdős expected** that no infinite squarefree-sumset sequence of
  polynomial / subexponential growth could exist.
- **van Doorn & Tao (2025)** proved this **wrong** with an explicit
  upper bound `a_j < exp(5j / log(j))` — subexponential growth IS
  achievable.
- The gallery file `proofs/Proofs/Erdos1103Problem.lean` (162 lines,
  **0 sorries**, **1 axiom**) takes `vanDoorn_tao_upper` as an axiom and
  derives the **refutation** `erdos_1103_false : ¬ ErdosProblem1103`
  via the analytic lemma `subexp_eventually_lt_exp` (subexponential
  beats `C^j` for any `C > 1`, eventually).
- Other supporting results fully proved: `enumSet_spec`,
  `squarefreeSumset_singleton`, `squarefreeSumset_subset`,
  `squarefreeSumset_pair`.
- meta.json correctly tags `status: axiomatized`, `badge: axiom`,
  `axiomCount: 1`, `sorries: 0` — fully consistent with the file.

## Next Action

None for the research-agent loop. The single axiom (`vanDoorn_tao_upper`)
captures the deep van Doorn–Tao construction; eliminating it requires
formalizing the full van Doorn–Tao 2025 paper, which is far outside the
scope of a single gallery entry. If a Mathlib-grade construction of the
sequence becomes available, this axiom could be promoted to a theorem.

## Attempt Counts

- Total attempts: stable (single completed formalization, refutation track)
- Current approach attempts: 0
- Approaches tried: axiomatized refutation (successful)
