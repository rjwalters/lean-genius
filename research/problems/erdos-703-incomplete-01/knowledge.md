# Knowledge: erdos-703-incomplete-01

## Overview

Initial knowledge for problem `erdos-703-incomplete-01`.

## Gallery Proof Summary

- Gallery: `erdos-703` — Forbidden r-Intersection Families
- Sorries: 1, Axioms: 2
- Tags: erdos, combinatorics, set-families, extremal, intersection-problems

## Known Results

(To be populated during OBSERVE phase)

## Key References

- Gallery: `src/data/proofs/erdos-703/`
- Lean source: `proofs/Proofs/` (check namespace `Erdos703`)

## Session (researcher-1, 2026-07-09): activate the L-avoiding predicate

**Mode**: REVISIT (MODERATE) · **Outcome**: progress (4 theorems, UNVERIFIED —
docker corrupted). Branch `research/erdos703-lavoiding-lemmas`.

The state's suggested "next action" (even-parity Frankl–Füredi family) was already
done by a later session (`franklFurediEven_avoids_r` / `_card_le_T` exist). The one
genuinely-dead object left was `avoidsLIntersections` (Part VII, Frankl–Wilson
`L`-avoiding predicate): defined but with **zero lemmas**. Added its basic API:
- `avoidsRIntersection_iff_avoidsLIntersections_singleton (r F)`: `r`-avoidance ↔
  `{r}`-avoidance. `unfold` both, `simp only [Finset.mem_singleton, ne_eq]`
  (needed `ne_eq` to normalize `≠` to `¬ =` on both sides).
- `avoidsLIntersections_of_subset_family (hsub : F' ⊆ F)`: term-mode
  `fun A B hA hB => hF A B (hsub hA) (hsub hB)` (Finset subset applies as a function).
- `avoidsLIntersections_of_subset_forbidden (hL : L ⊆ L')`: antitone in the forbidden
  set, `fun A B hA hB hmem => hF A B hA hB (hL hmem)`.
- `avoidsLIntersections_empty`: `intro A B _ _; simp` (`x ∉ ∅`).

Gallery meta `erdos-703` synced (both blocks): lineCount 638→679, theoremCount 21→25;
axiomCount stays 1 (`frankl_rodl_1987` untouched).

**BLOCKER:** docker corrupted fleet-wide (containerd `meta.db` I/O error at image
build). UNVERIFIED; proofs are trivial membership facts, correct by inspection.
