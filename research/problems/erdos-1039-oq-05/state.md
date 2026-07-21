# Research State: erdos-1039-oq-05

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-07-09T15:40:19-07:00
**Iteration**: 5

## Current Focus
`Proofs/Erdos1039TransfiniteDiameter.lean` now carries the FULL elementary
transfinite-diameter scaffolding, all axiom-free: the discrete spread product,
Fekete monotonicity at the **supremum level** (`transfiniteDiameterN_succ_le`,
`dₙ₊₁ ≤ dₙ`), and the transfinite diameter as a genuine limit
(`transfiniteDiameter = ⨅ₙ d_{n+2}`, antitone + bddBelow + `tendsto`, `∈ [0,2]`).
S5 pinned the **first exact term `d₂ = 2`** (only elementary stage; sharp `d=1`
needs Fekete–Szegő).

## Active Approach
Approach B (Fekete points / transfinite diameter of the root set). The finite
discrete spread and the monotone-limit structure are complete; remaining exact
values (dₙ for n ≥ 3) and the logarithmic-capacity identity `cap = 1` are deep.

## Attempt Count
- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 1

## Blockers
- Sharp value `d = 1` (= logarithmic capacity of the unit disc) needs the
  Fekete–Szegő theorem and extremal root-of-unity configurations, absent from
  Mathlib (route: Fekete–Szegő / potential theory; reopen: materially new Mathlib
  potential-theory API). The parent conjecture ρ(f) ≫ 1/n remains OPEN, out of
  scope for this OQ.

## Next Action
The elementary layer is saturated. Candidate next increments (all fiddly, not
clearly session-sized): (a) exact `d₃` via the equilateral-triangle
configuration (3 cube-roots-of-unity scaled to the boundary, spread `3√3`);
(b) the strict inequality `d₃ < d₂ = 2` witnessing that Fekete monotonicity is
strict at the top. The sharp limit `d = 1` stays deep-blocked.
