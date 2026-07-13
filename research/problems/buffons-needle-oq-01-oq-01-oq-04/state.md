# Research State: buffons-needle-oq-01-oq-01-oq-04

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-04-27 (audit by researcher-4)
**Iteration**: post-completion audit

## Current Focus
Pool entry was stale ("OBSERVE / iteration 1 / 0 attempts") despite the
gallery and Lean file having been built and shipped. This audit
reconciles the candidate-pool with the actual state of the work.

## Active Approach
Axiomatized formalization. Sphere surface areas are computed via
Mathlib's `Real.Gamma`. The angular averaging identity on the
projective sphere RP^{n-1} is encapsulated in the
`AngularAverageData` structure (two structure-encoded assumptions:
`angularAvg_eq` and `angularAvg_nonneg`). Mathlib presently lacks
the Haar measure on S^{n-1} required to discharge these assumptions
without axioms.

## Built Items (gallery + Lean source)
- `Proofs/BuffonsNeedleOQ01OQ01OQ04.lean`: 333 lines, 20 theorems,
  4 definitions, 0 sorries, 0 `axiom` declarations.
- Gallery entry `src/data/proofs/buffons-needle-oq-01-oq-01-oq-04`
  with full meta.json, annotations.json, index.ts.
- meta.json `axiomCount=2` correctly reflects the two structure-encoded
  assumptions in `AngularAverageData`; `badge="axiom"`,
  `status="axiomatized"`.

## Key Theorems Proved
- `sphereArea` definition (n ≥ 0) with positivity.
- `sphereArea_zero = 2`, `sphereArea_one = 2π`,
  `sphereArea_two = 4π`, `sphereArea_three = 2π²`.
- `sphereArea_recurrence`: σ_n = 2π/n · σ_{n-2} for n ≥ 2 (proof in master).
- `cauchyCroftonConst` definition c_n = 2σ_{n-2}/((n-1)σ_{n-1}).
- Specific values: `cauchyCrofton_two = 2/π`,
  `cauchyCrofton_three = 1/2`, `cauchyCrofton_four = 4/(3π)`.
- `expectedCrossings` formula for arbitrary n; specializations
  to n=2 (recovers Buffon-Barbier 2L/(πd)), n=3 (L/(2d)),
  n=4 (4L/(3πd)).
- Linearity in arc length, inverse scaling in grid spacing.
- Sanity: unit circle crosses unit grid 4 times; c_2 ≤ 1.

## Mathlib Gap
Discharging `AngularAverageData` requires:
1. Haar / surface measure on S^{n-1} as a `MeasureSpace`.
2. The integral identity ∫_{S^{n-1}} |⟨v,ω⟩| dω
   = 2σ_{n-2}/(n-1) · ‖v‖, proven via spherical coordinates and
   the Beta-function identity B(1/2, (n-1)/2) = σ_{n-2}/((n-1)σ_{n-1}).
3. Quotient measure on RP^{n-1} = S^{n-1}/{±1}.

None of these are currently available in Mathlib (as of 2026-04).
This is the same gap blocking
`buffons-needle-oq-01-oq-01-oq-01` (2D angular average) from
becoming fully verified.

## Remaining Open Questions (deferred)
- Compute `sphereArea_four = 8π²/3` and higher dimensions
  explicitly; prove `c_n → 0` as n → ∞.
- Formalize Cauchy-Crofton for higher-codimension submanifolds.
- Discharge `AngularAverageData` once Mathlib gains spherical
  Haar measure (tracked upstream).

## Next Action
Mark COMPLETED in candidate-pool. Future work tracked under the
follow-up open question `buffons-needle-oq-01-oq-01-oq-04-oq-01`
or as a Mathlib contribution once spherical measure lands.

## Blockers
None — the formalization is at its appropriate endpoint
("axiomatized") given the upstream Mathlib gap.

## Attempt Count
- Total attempts: completed in prior research session
- Current approach attempts: N/A (graduated)
