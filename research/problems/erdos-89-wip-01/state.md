# Research State: erdos-89-wip-01

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-07-09T17:33:18-07:00
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

## Status (researcher-1, 2026-07-23) — regular n-gon: g(n) ≤ ⌊n/2⌋, first new ladder entry 2 ≤ g(7) ≤ 3

Phase ACT. New file `Erdos89WIP01Ngon.lean` (0 axioms, 0 sorries, Docker-verified,
8578 jobs): the regular n-gon on the unit circle realises at most ⌊n/2⌋ distinct
distances (`minDistinctDistances_le_half`), halving the progression bound n − 1.

Method: ONE trig identity carries the whole file — the chord-length formula
`dist_ngonPoint : dist = 2·|sin(π(i−j)/n)|` (from (cosA−cosB)² + (sinA−sinB)²
= 4·sin²((A−B)/2), closed by `linear_combination`). Vertex injectivity is DERIVED
from the formula (coincidence ⟹ sin = 0 with argument in (−π, π) ⟹ i = j via
`Real.sin_eq_zero_iff_of_lt_of_lt`) — no per-vertex coordinate lemmas, in contrast
to the pentagon witness's dozens of bespoke dist_* lemmas. Chord census: index
m = |i−j| reflects to min(m, n−m) ∈ [1, ⌊n/2⌋] via `Real.sin_pi_sub`
(`two_sin_mem_image`), so the distance set embeds in the ⌊n/2⌋-element image.

Payoff: one uniform witness recovers the ENTIRE known upper ladder (g(3) ≤ 1,
g(4) ≤ 2, g(5) ≤ 2 — tight against the exact values; g(6) ≤ 3 re-derived via the
hexagon, independent of pentagon-plus-centre) and adds the first NEW entry:
`minDistinctDistances_seven_mem_Icc : 2 ≤ g(7) ≤ 3` (heptagon; previous best
in-file was g(7) ≤ 6).

Upper side now SATURATED at the elementary layer: the n-gon's ⌊n/2⌋ is optimal
among single-orbit constructions for small n; beating it needs Erdős's √n-grid
(large n, real analytic number theory). All remaining ladder work is LOWER bounds
— g(6) = 3 and g(7) = 3 both reduce to the planar two-distance-set ≤ 5-points
theorem, the registered blocker (reopen: two-distance-set / incidence machinery
in Mathlib).
