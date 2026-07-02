# Current State

**Phase**: PARTIAL (feasibility map + verified design)
**Since**: 2026-07-02
**Iteration**: 2

## Current Focus

Make the "optimal exponent c₀" a first-class, well-defined invariant of Erdős
#1004 and reframe the parent's two conjecture Props (`Erdos1004Conjecture`,
`SmallCaseConjecture`) as single quantitative statements about `c₀`.

## Active Approach

Structural / order-theoretic. Define `AchievableExponent : ℝ → Prop`, prove it is
downward-closed (via `run_prefix` + `Real.rpow_le_rpow_of_exponent_le` +
`Nat.floor_le_floor`), define `c₀ : EReal := sSup {…}` in a complete lattice, and
prove `conjecture_iff_c₀_top` and `smallCase_iff_c₀_pos`. All 0-axiom, no analytic
number theory. Full design with exact Mathlib API in knowledge.md.

## Blockers

1. **Environment (this iteration):** no Mathlib olean cache anywhere in the repo
   (`Mathlib.olean` absent under `proofs/.lake`), disk at 99% (~11 GiB free), and
   worktrees are being reaped under disk pressure. A verification build (`import
   Mathlib`) would require a full multi-hour Mathlib compile that cannot run
   safely — so no Lean artifact was compiled/shipped this iteration.
2. **Mathematics (the hard core):** the *value* of `c₀` is blocked. `c₀ > 0`
   needs distribution-of-totient-values / sieve input (EPS 1987), absent from
   Mathlib; `c₀ = ⊤` is the open Erdős problem itself.

## Next Action

When a Mathlib build is available (olean cache present, disk healthy): create
`proofs/Proofs/Erdos1004OQ0201.lean` importing `Proofs.Erdos1004Problem`,
implement the four structural theorems from knowledge.md, verify 0-axiom via
`lake env lean`, and add a new gallery entry under a fresh child slug
`erdos-1004-oq-02-oq-01` (do NOT overwrite the existing verified `erdos-1004-oq-02`
gallery entry, which is a different result — totient fiber finiteness).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (structural invariant `c₀`; design complete, verification
  deferred on environment)
