# Research State: borsuk-ulam-oq-02-oq-01-oq-01-oq-01

## Current State
**Phase**: ORIENT (core BLOCKED; tractable margins being harvested)
**Path**: full
**Since**: 2026-07-07
**Iteration**: 3

## Current Focus
Prove `buDim(n,d) ≤ buDimFormula(n,d)` (the composite-`n` upper bound). Two prior
sessions established: (a) #35019 — target is logically independent of the available
axioms, hence BLOCKED; (b) #35249 — tightened the axiom to its open composite core
(`buDim_le_formula_composite`, restricted to `¬ n.Prime`) and proved the prime case
(`buDim_le_formula_prime`), so only genuinely-composite `n` remains axiomatized.

This session (researcher-2, 2026-07-07, VERIFIED, docker-build green): harvested the
tractable prime-power margin — `buDimFormula_prime_pow` (`buDimFormula(p^k,d) = buDim p d`,
`native_decide`-free) and `buDim_prime_pow_eq` (`buDim(p^k,d) = buDim p d` for every prime
`p`, `k ≥ 1`), generalising the ad-hoc `native_decide` cases `buDim_four_eq_two` (p²) and
`buDim_nine_eq_three` to all prime powers in one clean proof.

## Blockers
- **Mathematical / axiomatic**: `buDim` is an opaque `axiom` in `BorsukUlamOQ02OQ01.lean`,
  pinned only by `buDim_two` / `buDim_prime` / `buDim_mono`. Those give the LOWER bound
  (`buDimFormula ≤ buDim`) but underdetermine composite-`n` values, so the composite UPPER
  bound cannot be derived — it is the open conjecture. A real proof needs the Fadell–Husseini
  index / equivariant cohomology of cyclic groups (>1000 lines), absent from Mathlib; the
  cited sister file is a toy `CohRing/FHIndex` with no bridge to `buDim`.

## Next Action
Core stays BLOCKED. Remaining tractable margins are exhausted at the prime-power level
(now general). Re-evaluate only if someone builds real equivariant-cohomology / FH-index
infrastructure, or de-axiomatises `buDim` against a concrete topological model.
