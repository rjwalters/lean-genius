# Research State: collatz-structured-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T05:00:00-07:00
**Iteration**: 4

## Current Focus
Repaired and **verified** the previously-broken 115/128 density floor. The prior commit
(#30735) referenced four mod-128 theorems that were never written, so the file did not
compile. This session authored the three missing mod-128 drop theorems (`7, 15, 59 mod 128`,
each dropping in 11 residue-determined steps to `81m+d`) plus the 8-way packaging theorem,
and confirmed EXIT 0 with `#print axioms` showing only `propext/Classical.choice/Quot.sound`.

## Active Approach
Deep result stays a single documented axiom (`tao_2019`); the elementary residue-dynamics
core is extended one dyadic level via the shared `affine_residue_attainsBelow` helper, then
assembled into a disjoint-family counting bound (`attainsBelow_density_lower_128`).

## Attempt Count
- Total attempts: 5
- Approaches tried: statement + explicit families; n≡1 mod 4 family; colMin bridge;
  mod-16/mod-32 refinements; mod-128 refinement (committed broken); **mod-128 repair + verify (this session)**

## Blockers
- Full proof of Tao (2019) remains BLOCKED (3-adic transport/concentration + Fourier; >> 1000 lines).
- Build host: Docker is back up but disk at 99% (~190Mi free). Verified offline via
  `LAKE_UNSAFE=1 ./bin/lake env lean` against the worktree's cached Mathlib oleans (EXIT 0).

## Next Action
The next dyadic improvement past 115/128 is at level 256 (density 237/256), but this is
diminishing returns — each level adds only a handful of residue classes and the path to
density 1 is the Terras/Korec finite-stopping-time theorem, not finite residue computation.
Future milestone: formalize Terras/Korec natural-density stopping-time toward Tao's bound.

## Deliverable (this session)
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` — now COMPILES (was broken):
- `mod_onetwentyeight_seven_attainsBelow`, `mod_onetwentyeight_fifteen_attainsBelow`,
  `mod_onetwentyeight_fiftynine_attainsBelow` (the three missing 11-step drop theorems);
- `even_or_mod_four_one_or_mod_onetwentyeight_attainsBelow` (8-way packaging).
Verified EXIT 0 offline; all new theorems axiom-free (`propext/Classical.choice/Quot.sound`).
Still 1 deep axiom (`tao_2019`), 0 sorries, 39 theorems. meta.json counts corrected.
