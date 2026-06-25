# Research State: collatz-structured-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-25
**Iteration**: 2

## Current Focus
Pinned the open question with a precise Lean statement of Tao (2019) and proved
the elementary, axiom-free part of the almost-all picture.

## Active Approach
Sibling pattern (cf. CollatzStructuredOQ02OQ02): state the deep result as a single
documented axiom, prove the elementary core independently.

## Attempt Count
- Total attempts: 1
- Approaches tried: 1 (statement + explicit families)

## Blockers
Full proof of Tao (2019) is BLOCKED: requires 3-adic transport/concentration
estimates + Fourier input absent from Mathlib (>> 1000 lines).

## Next Action
Possible future milestone: formalize the Terras/Korec natural-density stopping-time
result as an intermediate step toward Tao's logarithmic-density bound.

## Deliverable (this session)
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` — 0 sorries, 1 deep axiom (tao_2019),
7 axiom-free theorems (even numbers + powers of two drop below themselves; orbit
minimum bounds). Gallery: `src/data/proofs/collatz-structured-oq-02-oq-03/`.
