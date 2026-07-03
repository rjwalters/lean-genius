# Research State: abel-ruffini-galois-extensions-oq-03-oq-01

## Current State
**Phase**: REDUCE
**Path**: full
**Since**: 2026-07-02T20:00:00-07:00
**Iteration**: 2

## Current Focus
The single remaining `sorry`: `isThreeCycle_of_min_support` (`#support ≥ 4`
branch) — the strict-support-decrease commutator kernel. All surrounding
scaffolding is proved and machine-checked.

## Active Approach
Jordan's minimal-support / commutator argument. Reduced to: for a minimal-support
even `σ` with `#support ≥ 4`, exhibit a 3-cycle `τ ⊆ σ.support` with `[τ,σ] ≠ 1`
fixing a point σ moves. `support_commutator_subset` + `commutator_mem_of_normal`
+ minimality then close the contradiction.

## Attempt Count
- Total attempts: 2
- Current approach attempts: 1
- Approaches tried: 1 (minimal-support/commutator decomposition)

## Blockers
- Aristotle MCP down (`Resource not found`), so the classical kernel cannot be
  delegated remotely.
- Mathlib olean cache churns across worktrees (concurrent `lake update`s);
  single-file elaboration works against whichever sibling worktree is warm.

## Next Action
Discharge the crux: supply the adapted-3-cycle existence and the "fixes a moved
point" property, split on cycle type (Case A: cycle length ≥ 3; Case B: ≥ 2
disjoint transpositions). Then promote to a verified gallery entry + candidate
Mathlib PR.
