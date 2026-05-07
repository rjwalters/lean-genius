# Research State: hurwitz-theorem-wip-01

## Current State

**Phase**: OBSERVE
**Path**: full
**Since**: 2026-05-07T18:10:00Z
**Iteration**: 2

## Current Focus

Survey complete: full inventory of what is proved upstream of the blocking
sorry, mapping the gap to the missing Mathlib API. Problem confirmed BLOCKED
on real Clifford algebra structure classification (~1000 lines of upstream
Mathlib infrastructure needed).

## Active Approach

**Wait** — until Mathlib gains Clifford structure / Bott periodicity API.
Localized 2 sorries (HurwitzTheorem.lean:1937, HurwitzOnlyIf.lean:111) both
collapse to the same blocker.

## Attempt Count

- Total attempts: 1
- Approaches tried:
  1. (S2 — this session) OBSERVE / SURVEY: enumerate proved infrastructure,
     classify what's left, identify Mathlib gap precisely.

## Blockers

1. Mathlib has no real Clifford algebra periodicity / structure classification.
2. Mathlib has no Artin-Wedderburn for real semisimple algebras.
3. No minimum-faithful-real-rep-dimension lemma derivable from current
   `Mathlib.LinearAlgebra.CliffordAlgebra.*` (which only provides the universal
   property and basic conjugation).

## Next Action

Highest-EV options, in order:

1. **(option B) Refactor `HurwitzOnlyIf.hurwitz_only_if_ring`** into a concrete
   bridge lemma (`nsquareIdentity_of_normedDivisionRing`, ~80 lines) plus the
   call to `HurwitzTheorem.hurwitz_only_if`. Sorry count unchanged but the
   non-Mathlib part of the proof becomes provable. Net effect: same total
   axioms/sorries but one of the two sorries becomes "calls a sorry-axiom"
   instead of "needs new infra". Future-blocked by the same Cl gap.

2. **(option D) Wait** for Mathlib upstream. Re-check
   `Mathlib.LinearAlgebra.CliffordAlgebra.*` periodically.

3. **(option A) Small-case decomposition** for $n = 6, 10$. ~400 lines per
   case, hand-coded Wedderburn structure of $\mathrm{Cl}(0, 5)$ and $\mathrm{Cl}(0, 9)$.
   Narrows but does not eliminate the open sorry; arguably not worth the work
   if Mathlib will land it eventually.

4. **(do NOT)** Submit to Aristotle. Sorry is OPEN (genuine missing infra),
   not a routine lemma — Aristotle is the wrong tool.
