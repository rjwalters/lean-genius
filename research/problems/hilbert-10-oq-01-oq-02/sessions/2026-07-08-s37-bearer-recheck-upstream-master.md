# Session 37 — bearer recheck on upstream master (researcher-10, 2026-07-08)

**Trigger**: random picker reclaimed the slug 2026-07-08 — the first pickup at/past
the 30-day dormancy recheck anchor (2026-07-03) set by S32 and re-affirmed by
S34/S35/S36. A recheck is therefore *due*, not premature.

## Goal
Re-verify the standing S32/S34/S35 "upstream-blocked" verdict for the iter-27a
Σ₂(ℤ) attack: have any of the 5 missing bearers landed in upstream Mathlib
**master** since S35 (2026-06-18)? This distinction sets the unblock path —
a pin-bump (if landed on master) vs. genuine from-scratch formalization (if still
absent everywhere).

## Method
1. GitHub code search on `leanprover-community/mathlib4` (`gh api search/code`)
   for each bearer identifier — reports current **master**, not the pin.
2. Contents-API listing of `Mathlib/Algebra/BrauerGroup` and `Mathlib/NumberTheory`.
3. Sanity control: `LegendreSymbol` (must stay non-zero) to prove the index is live.

## Findings (2026-07-08, upstream master)

| Bearer | Upstream master | Note |
|---|---|---|
| `HilbertSymbol` (rational) | absent | code search `total_count` = 0 |
| `HasseMinkowski` | absent | `total_count` = 0 |
| Brauer **rational** classification | absent | `Algebra/BrauerGroup/` = only `Defs.lean` (abstract) |
| `PoonenNonSquaresDiophantine` | absent | `total_count` = 0 |
| `Hilbert10Rational` / H10-over-ℚ | absent | `NumberTheory/` = only `Dioph.lean` + `DiophantineApproximation` |
| **control** `LegendreSymbol` | **present (17)** | index live — the 0-counts are real absences, not a dead query |

Identical to the S34/S35 baseline: **5/5 bearers still absent on master**; zero motion
in 20 days.

## Verdict
- Standing verdict **unchanged**: the iter-27a Σ₂(ℤ) attack remains genuinely
  upstream-blocked. Because the bearers are absent from **master** (not merely from
  the v4.26.0 pin), a pin-bump would **not** unblock it — the required Hilbert-symbol
  / Hasse–Minkowski / rational-Brauer / Poonen infrastructure does not exist upstream
  yet and would have to be built from scratch (a large, multi-file effort, out of
  scope for a single research cycle).
- In-file re-export surface remains exhausted (S33); the affine-pullback closure grid
  was subsequently completed (#27100). No single-cycle in-file Lean delta is available
  this cycle.
- **Docker verification infra is currently down** (shared `lean-mathlib-packages`
  olean volume corrupt — exit 135 / SIGBUS on `Mathlib.Data.Fintype.Pi`, see issue
  #35184), so even an in-file delta could not be build-verified this session. This is
  an independent, additional reason no Lean change is shipped.

## Next recheck
Re-anchor the 30-day dormancy window to **2026-08-07**. Recheck protocol: query
upstream **master** (not just the pin) for the 5 bearers, with `LegendreSymbol` as the
live-index control. Invariants at time of writing: pin v4.26.0, 0 sorries, 1 axiom,
badge `axiom`, status `axiomatized`.
