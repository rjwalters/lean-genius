# Knowledge: lagrange-theorem-oq-01-oq-02

## Status: COMPLETED

**Iteration 2026-06-10 (researcher-1)**: OBSERVE — answer already on disk; marking complete.

## Summary

A₄ has no subgroup of order 6 — proved in `proofs/Proofs/LagrangeTheoremOQ01OQ02.lean`
(122 lines, 8 theorems, 0 sorries, 0 axioms; gallery `status: "verified"`).

The main result `A4_no_subgroup_order6` is proved by exhaustive enumeration:
`native_decide` over all 2¹² = 4096 subsets of the 12-element group checks the
three subgroup axioms (`1 ∈ S`, closed under `·`, closed under `⁻¹`) and finds
no 6-element subset satisfies all three. The Subgroup-level theorem then lifts
via `Fintype.card_subtype` (subgroup ↔ filtered `Finset` of the universe).

## What this iteration changed

- `src/data/research/problems/lagrange-theorem-oq-01-oq-02.json`: phase
  `NEW` → `COMPLETED`, status `active` → `completed`, `currentState` and
  `lastUpdate` refreshed. The progressSummary, builtItems, insights, and
  nextSteps from the prior session are preserved verbatim.
- This file: created as the OBSERVE record.

No Lean source was edited. The file built cleanly when last verified and uses
only `native_decide` for the heavy lifting — robust across Mathlib renames.

## Follow-up questions (deferred to future seeker work)

Documented in `src/data/proofs/lagrange-theorem-oq-01-oq-02/meta.json`:

1. Subgroup lattice of A₄: `{e}`, 3 × ℤ₂, 4 × ℤ₃, V₄, A₄ — formalize as a
   complete classification.
2. Conjugacy-class argument as an alternative proof: no union of class sizes
   from `{1, 3, 4, 4}` containing `1` sums to `6`.
3. Hall's theorem for solvable groups (positive companion to this negative
   result).

The pool's existing `nextSteps` track #1 and a Hall variant of #3. These are
substantial new problems, not a continuation of this one — better selected
fresh by the seeker than scaffolded onto this entry.
