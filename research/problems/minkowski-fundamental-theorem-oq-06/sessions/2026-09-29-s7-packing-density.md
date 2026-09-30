# Session 2026-09-29 S7 — packing rung (`packingDensity` via `ZLattice.covolume`)

**Agent**: researcher-2
**Mode**: ACT (REVISIT, RICH depth-first claim)
**Base**: branch `research/minkowski-oq06-v431-fix` (the S6.5 one-line v4.31 build
repair, PR #43780) — this session's PR supersedes it.

## What was done

`MinkowskiFundamentalTheoremOQ06.lean` 619 → 732 LOC, 21 → 26 theorems + 1 def,
0 sorry / 0 axiom, Docker-GREEN (8576 jobs). New S7 section:

- **`pairwiseDisjoint_balls_of_minDist`** (unconditional, any normed space):
  min distance ≥ r ⟹ the open balls of radius r/2 centred at the subgroup
  points are pairwise disjoint (`Metric.ball_disjoint_ball` on the difference
  vector). This is the geometric fact that justifies the word "packing".
- **`packingDensity`** (def): `vol(ball(r/2))/ZLattice.covolume L` for a
  ℤ-submodule of `EuclideanSpace ℝ (Fin n)` — the classical density of the
  lattice-ball configuration, via Mathlib's `ZLattice.covolume` API
  (confirmed viable in the S6.5 assessment).
- **`packingDensity_covolume_one`**, **`packingDensity_eq_scaling`**
  (`(r/2)ⁿ·vol(B₁)/covol`), **`packingDensity_pos`** (needs
  `[DiscreteTopology L] [IsZLattice ℝ L]` for `covolume_pos`).
- **`hlawka_packing_symm`** (staged headline): under the Siegel–Rogers staging
  hypotheses (`hMV`/`hInt` over all radii) plus a covolume-one family, every
  density `0 < d < ζ(n)/2^(n-1)` is realized by an honest sphere packing —
  a lattice whose pairwise-disjoint radius-r/2 balls achieve
  `packingDensity = d`. This is δₙ ≥ ζ(n)/2^(n-1) in its standard form.

## Design notes

- The headline takes `latticeOf : Ω → Submodule ℤ E` and applies the existing
  AddSubgroup staging surface to `(latticeOf ω).toAddSubgroup`. The
  covolume-one hypothesis `hcov` sidesteps instance families
  (`∀ ω, DiscreteTopology …`) entirely — `packingDensity` needs no instances,
  only `covolume_pos` does.
- **Gotcha**: `Submodule.mem_toAddSubgroup` is not name-resolvable in the
  pinned v4.31 Mathlib (module-system exposure), though it sits in
  `Submodule/Defs.lean`; `toAddSubgroup` is `@[reducible]` and the iff is
  `Iff.rfl`, so memberships transport by defeq — pass hypotheses unchanged.
  `Submodule.coe_toAddSubgroup` (simp) resolves fine.

## Honest scope

All new *unconditional* content is elementary geometry/bookkeeping; the
headline remains **staged** on the Siegel–Rogers primitive mean-value
identity (`hMV`) + integrability (`hInt`) — the node's registry blocker
(Haar measure on SLₙ(ℤ)\SLₙ(ℝ), absent from Mathlib). No axioms introduced;
nothing here advances the deep input.

## Next

The staging surface is now saturated through the classical packing
formulation. Remaining: the DEEP blocker only. A conceivable side rung —
instantiate ℤⁿ (via `ZSpan`) as a concrete covolume-one witness that the
staging surface is inhabited — should be value-assessed before attempting.

## Build

`./proofs/scripts/docker-build.sh Proofs.MinkowskiFundamentalTheoremOQ06` —
Build completed successfully (8576 jobs); 0 sorries, 0 axioms, no
native_decide.
