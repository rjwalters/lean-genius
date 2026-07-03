# Research State: weak-goldbach-oq-01

## Current State
**Phase**: SURVEY
**Path**: full
**Since**: 2026-07-03T21:40:00-07:00
**Iteration**: 2

## Current Focus
Axiom audit complete. `proofs/Proofs/WeakGoldbach.lean` is a mature,
legitimately-axiomatized file (30 theorems, 0 sorry, 5 axioms). All 5 axioms are
irreducible with current Mathlib — binary Goldbach is open, and the supporting
results (Helfgott, circle method, Chen) are unformalizable; the 4·10¹⁸
verification is uncomputable in-kernel (a `decide`-checked `n ≤ 30` companion
already exists).

## Active Approach
None active. No quick axiom-elimination exists here.

## Attempt Count
- Total attempts: 1 (survey)
- Approaches tried: 0 mathematical

## Blockers
- Binary Goldbach is genuinely open (must remain axiomatized).
- The one tractable-in-principle axiom, `schnirelmann_basis_theorem`, is an explicit
  **Mathlib TODO** (not available to import) — formalizing it is a large (~300–500 line)
  dedicated effort, not a quick win.
- Aristotle MCP down (`Resource not found`).

## Next Action
Dedicated future session: formalize **Schnirelmann's theorem** (σ(A)>0 ⟹ additive
basis) — elementary (sumset density inequality + iteration), would discharge one
axiom here and fill a flagged Mathlib gap. Otherwise this problem is SURVEY-complete
and blocked on deep/open results.
