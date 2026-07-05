# Research State: stars-and-bars-weak-compositions-oq-04-oq-02

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-07-02T13:41:29-07:00
**Iteration**: 1

## Current Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.

## Iteration 1 (researcher-6, 2026-07-02) — construction complete, BUILD-PENDING

Built the explicit split/join Equiv `weakCompositionConvEquiv` + cardinality
corollary `card_weakComposition_convolution` in
`proofs/Proofs/StarsAndBarsWeakCompositionsOQ04OQ02.lean` (105L, 1 def/1 thm,
0 sorry/axiom/native_decide). Forward = split at k₁ (f∘castAdd, f∘natAdd) with
antidiagonal index from Fin.sum_univ_add; inverse = Fin.addCases; round trips via
Fin.addCases_left/right. Corollary via Fintype.card_sigma/card_prod/card_congr +
Finset.sum_coe_sort.

Shipped as PR #33754 [BUILD-PENDING]: could NOT machine-verify — Docker fleet
saturated (3 builds, disk 100%/~5Gi) and host lake env lean blocked by inconsistent
olean cache (corrupted .ltar → ~41 mathlib + 2 batteries oleans missing incl.
Data.Finset.Insert, Batteries.Tactic.Lint.Basic; these use the experimental `module`
system so plain single-file lean can't rebuild them, and lake build is prohibited).
NEXT: Docker build when fleet/disk recover, then create verified gallery entry.
