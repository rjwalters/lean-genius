# Research State: algebraic-numbers-countable-oq-04

## Current State

**Phase**: COMPLETED (axiomatized)
**Path**: full
**Since**: 2026-04-28
**Iteration**: 3 (last touched 2026-04-29 for gallery meta.json drift fix)

## Current Focus

Gallery entry promoted as axiomatized. The Lean file
`proofs/Proofs/AlgebraicNumbersCountableOQ04.lean` (640 lines) formalizes
Baker's theorem with four axioms and derives elementary consequences
sorry-free.

## Active Approach

None — work scope complete.

## Outcome

- **Lean file**: `proofs/Proofs/AlgebraicNumbersCountableOQ04.lean` (640 lines, 0 sorries)
- **Axioms** (4, all stated forms of Baker's 1966 / Wüstholz 1993 results):
  - `baker_homogeneous` — homogeneous Baker theorem
  - `baker_inhomogeneous` — inhomogeneous form (with constant term β₀)
  - `baker_quantitative` — explicit lower bound `|Λ| > B^{-C}`
  - `baker_wustholz_bound` — Baker–Wüstholz 1993 bound
- **Derived (sorry-free)**: log₂(3) irrationality (elementary, via unique
  factorization), transcendence of log₂(3) from `baker_homogeneous`,
  Q̄-linear independence of {log 2, log 3} from Baker
- **Gallery**: `src/data/proofs/algebraic-numbers-countable-oq-04/meta.json`
  marked `status: axiomatized`, `badge: axiom`, `axiomCount: 4`, dated 2026-04-24

## Blockers

None at the axiomatized scope.

## Why Not "verified"

Baker's theorem is one of the deepest results in transcendence theory. A
full formalization requires:
- Siegel's lemma (linear algebra of integral solutions)
- Baker's auxiliary function construction
- Extrapolation argument (Schwarz lemma + Liouville-type bound)
- p-adic / archimedean estimates

Estimated >5000 lines of Lean and likely multi-year effort. The
axiomatized entry is the appropriate scope for the gallery.

## Next Action

None at this scope. The pool entry should be marked `completed` so the
seeker stops surfacing it.

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 0
