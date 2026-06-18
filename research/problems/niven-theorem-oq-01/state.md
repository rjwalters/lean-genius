# Research State: niven-theorem-oq-01

## Current State
**Phase**: DONE (merged & live)
**Path**: full
**Since**: 2026-06-18T06:45:00Z
**Iteration**: 3

## Outcome — COMPLETE
Niven's theorem is formalized, machine-checked, and live in the gallery.

- **PR #25163** (`feature/researcher-8-niven-mathlib`) — **MERGED 2026-06-16T20:34Z**.
- `proofs/Proofs/NivenTheorem.lean` — **registered** at `proofs/Proofs.lean:2702`
  (`import Proofs.NivenTheorem`), **0 sorry / 0 axiom / no native_decide**.
- Gallery entry `src/data/proofs/niven-theorem-oq-01/` — `status: verified`,
  `badge: mathlib`, `axiomCount: 0`, `sorries: 0`.

## What the proof does
A *presentation* (not original formalization — Niven is already in Mathlib v4.26,
`Mathlib/NumberTheory/Niven.lean`, Meiburg–Broshi 2025):

1. **`two_cos_int_of_rational`** — for `θ = (m/n)·π` with `cos θ ∈ ℚ`, `2·cos θ ∈ ℤ`.
   Delegates the deep algebraic-integer step to
   `Real.isIntegral_two_mul_cos_rat_mul_pi (m/n)` (gives `IsIntegral ℤ (2 cos θ)`),
   then `IsIntegral.exists_int_iff_exists_rat` (a rational algebraic integer is an
   integer, i.e. `ℤ` integrally closed in `ℚ`).
2. **`niven`** — enumeration tail kept explicit for pedagogy:
   `|cos θ| ≤ 1` forces `2 cos θ ∈ {-2,-1,0,1,2}` via `interval_cases`, giving
   `cos θ ∈ {0, ±1/2, ±1}`.

## Blockers
None. (The original 2026-06-16 attempt logged a "Docker blackout / build-pending"
blocker; that was resolved by the fleet build that merged PR #25163. The prior
state.md text claiming the PR was still open was stale.)

## Next Action
None — problem complete. Tracker synced to `completed`; the claim pool should no
longer serve this slug.
