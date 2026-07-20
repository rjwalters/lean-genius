# State: erdos-214-incomplete-01

**Phase**: COMPLETED
**Since**: 2026-07-08
**Attempts**: 2
**Status**: completed
**Last Updated**: 2026-07-08 (researcher-3)

## Progress Summary

researcher-3 (2026-07-08): **repaired a broken-on-main build** and added verified
geometric content.

- **BUILD REPAIR**: the gallery file did not compile on main. An orphaned `/--`
  doc-comment (L71) documented nothing — it was followed by a `/- Part 3 -/` block
  comment rather than a declaration — producing a parse error
  (`unexpected token '/--'; expected 'lemma'`). Math PRs bypass Lean CI, so this
  latent breakage went unnoticed. Fixed by converting `/-- … -/` → `/- … -/`.
  Confirmed: origin/main version fails to parse; after the fix it builds.
- **dist_sq**: coordinate form of the plane distance for arbitrary points,
  `dist p q = √((p₀-q₀)²+(p₁-q₁)²)`.
- **scaledLattice_unitDistanceFree**: the scaled lattice `√2·ℤ²` is
  unit-distance-free. Distinct lattice points are at squared distance
  `2·((a₁-a₂)²+(b₁-b₂)²)`; `=1` would force `2m=1` for an integer `m`. This is an
  explicit **infinite** unit-distance-free set, so Problem #214's hypothesis is
  non-vacuous (`juhasz_stronger` applies to a genuine family, not the empty one).

Axiom count unchanged (1: `juhasz_stronger`, Juhász 1979 — deep incidence geometry
absent from Mathlib → BLOCKED). File 237→263 lines, theoremCount 8→10, 0 sorries.
docker-build VERIFIED (Lean v4.26.0).

## Gotcha logged

`scaledLattice_unitDistanceFree` first crashed the elaborator (exit 135 / SIGBUS)
when proved via a `ring`-normalised `hfac` equality + two-step `rw`. Rewriting to a
single `hX` equality closed by `rw [hp0…]; push_cast; nlinarith [h2]` (with
`Real.mul_self_sqrt`, folding `2·m` as an `Int` cast) elaborates cleanly.

## Blockers

`juhasz_stronger`: Juhász's 1979 4-point congruent-copy theorem — deep incidence
geometry, not in Mathlib. BLOCKED (not eliminable in one session).

## Session 2026-07-08 (researcher-8) — geometric infrastructure

Added 5 verified axiom-free theorems around the definitions (core still BLOCKED on
`juhasz_stronger`): `dist_self`, `dist_comm`, `isUnitSquare_of_isometry` (isometry
invariance — the reusable form of the inline argument in `unit_square_from_stronger`),
`IsUnitSquare.distinct` (four pairwise-distinct vertices), and the capstone
`complement_contains_distinct_unit_square` (complement contains a unit square on four
distinct points). File 263→328 lines, theoremCount 10→15, 0 sorries, axiomCount
unchanged (1). docker-build VERIFIED (2364 jobs, exit 0, Lean v4.26.0).

## Next Action

Optional follow-up: `Set.Infinite ScaledLattice` (strengthen non-vacuity to genuinely
infinite), a concrete FINITE unit-distance-free configuration, or the open 5-point case
(`HoldsFor5Points`). Core theorem remains BLOCKED on `juhasz_stronger`.

## Session 2026-07-09 (researcher-8) — UDF cardinality is unbounded

Core theorem still BLOCKED on `juhasz_stronger` (deep incidence geometry, not in
Mathlib — confirmed again). Added 3 verified axiom-free theorems answering the
"maximum size of a unit-distance-free set" half of #214 for the plane:
`IsUnitDistanceFree.mono` (subset of a UDF set is UDF), `exists_unitDistanceFree_finset_card`
(a UDF finset of every cardinality `n`, via an `n`-subset of the infinite
`scaledLattice_infinite`), and `no_maximum_unitDistanceFree_card` (hence no finite
cap). File 382→414 lines, theoremCount 20→23, 0 sorries, axiomCount unchanged (1).
docker-build VERIFIED (2364 jobs, exit 0, Lean v4.26.0).

## Session 2026-07-19 (researcher-1) — v4.31 re-verify + thread-close triage

No new theorems (none session-sized remain). Triage + re-verification session:

- **v4.31 re-verify (host, `lake env lean`, EXIT 0, zero deprecations)**: both
  `Erdos214Incomplete01OQ01.lean` (901 lines, 0 sorries / 0 axioms) and
  `Erdos214Problem.lean` (1 documented axiom `juhasz_stronger`, 0 sorries) compile
  clean under `leanprover/lean4:v4.31.0`. Both last touched under v4.26 (#38407),
  pre-flip #39062 — confirmed no v4.31 repair needed.
- **Distance-spectrum thread CLOSED (saturated)**: the all-`n` master
  characterization `scaledLattice_realizes_sqrt_iff` (landed #38407) subsumes every
  earlier avoidance lemma (√6/√12/√24/√56, mod-4/8/16, odd-prime obstructions) and
  the √(2p)/√(2pq) realizability results. The "remaining open" notes in the prior
  tracker (full sum-of-two-squares characterization; √(2pq) products) were written
  *before* #38407 and are now done. No session-sized frontier remains here.
- **Core still BLOCKED**: `juhasz_stronger` (Juhász 1979 4-point congruent-copy
  incidence geometry) is not in Mathlib; `HoldsFor5Points` is the equivalent-strength
  5-point analog. Registered as a structured `currentState.blockers` entry
  (reopen bar: materially new mechanism / Mathlib gains the incidence theorem).
- **Pool status → `blocked`** to stop wasteful depth-first re-serving of a saturated
  problem.
