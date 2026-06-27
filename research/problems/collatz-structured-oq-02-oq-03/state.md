# Research State: collatz-structured-oq-02-oq-03

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T05:00:00-07:00
**Iteration**: 3

## Current Focus
Pushed the unconditional, axiom-free density floor under Tao (2019) from **7/8** to
**115/128** by analysing the next dyadic level. Computed (exhaustively, in Python) that
level 64 adds *no* new stable residue class, but level 128 stabilises exactly three of the
mod-32 unstable classes — `7, 15, 59 (mod 128)` — each dropping in eleven residue-determined
steps to `81m + d` with `81 = 3^4 < 2^7`.

## Active Approach
Same sibling pattern: deep result stays a single documented axiom (`tao_2019`); the
elementary residue-dynamics core is extended one dyadic level via the shared
`affine_residue_attainsBelow` helper, then assembled into a disjoint-family counting bound.

## Attempt Count
- Total attempts: 4
- Approaches tried: statement + explicit families; n≡1 mod 4 family; colMin bridge;
  **mod-128 refinement (this session)**

## Blockers
- Full proof of Tao (2019) remains BLOCKED (3-adic transport/concentration + Fourier; >> 1000 lines).
- **Build host DOWN this session**: disk at 99% (≈237Mi free), Docker image store corrupt
  (`docker run` fails with containerd blob I/O error). Could NOT run `docker-build.sh`.
  The new content is therefore **UNVERIFIED by the Lean kernel** — but the mathematics is
  exhaustively checked in Python (all three trajectories for m=0..200; the 8 families are
  pairwise disjoint and cover exactly 115 residues mod 128) and the Lean follows the exact
  template of the already-compiled mod-32 theorems in the same file.

## Next Action
Re-run `./proofs/scripts/docker-build.sh Proofs.CollatzStructuredOQ02OQ03` once the build
host recovers (disk freed, Docker image store repaired) to confirm EXIT 0. Future milestone:
the next dyadic improvement past 115/128 is at level 256 (density 237/256); or formalize the
Terras/Korec natural-density stopping-time result toward Tao's logarithmic-density bound.

## Deliverable (this session)
`proofs/Proofs/CollatzStructuredOQ02OQ03.lean` — added, all axiom-free:
- `mod_onetwentyeight_seven_attainsBelow`, `mod_onetwentyeight_fifteen_attainsBelow`,
  `mod_onetwentyeight_fiftynine_attainsBelow` (the three new mod-128 drop theorems, 11 steps each);
- `even_or_mod_four_one_or_mod_onetwentyeight_attainsBelow` (8-way packaging);
- `attainsBelow_density_lower_128` (machine-statement of the `≥ 115/128` counting floor);
- four new `colMin_lt` corollaries bridging the new classes to Tao's `Col_min` predicate.
Still 1 deep axiom (`tao_2019`), 0 sorries. UNVERIFIED pending build host recovery (see Blockers).
Gallery `meta.json` updated (counts, description, highlights). 
