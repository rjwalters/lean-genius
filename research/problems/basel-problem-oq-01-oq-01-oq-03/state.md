# Research State: basel-problem-oq-01-oq-01-oq-03

## Current State
**Phase**: COMPLETE
**Path**: full
**Since**: 2026-06-24
**Iteration**: 2

## Current Focus
Shipped a verified, 0-axiom Lean formalization of the two reachable components of
the Ball–Rivoal theorem (infinitely many odd zeta values are irrational).

## Result
- File: proofs/Proofs/BaselProblemOQ01OQ01OQ03.lean (181 lines, 5 theorems, 0 defs).
- Builds clean on Mathlib v4.26.0 (lake env lean).
- #print axioms: only propext / Classical.choice / Quot.sound — no sorryAx,
  no Lean.ofReduceBool. Status: verified, 0 axioms.
- Part I: rate-free integer linear-form irrationality criterion (Apéry/Rivoal engine,
  a genuine Mathlib gap) + decay-rate packaging variant.
- Part II: dimension reduction — unbounded dim_ℚ span ⟹ infinitely many irrational.
- Gallery entry: src/data/proofs/basel-problem-oq-01-oq-01-oq-03/ (meta + annotations).

## Next Action
Done. Remaining (out of scope): formalize Rivoal's analytic dimension lower bound,
which combined with this file's reduction would complete a full Ball–Rivoal proof.
