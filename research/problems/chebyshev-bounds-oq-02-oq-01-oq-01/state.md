# Current State

**Phase**: ACT
**Since**: 2026-06-25T00:00:00Z
**Iteration**: 1
**Status**: in-progress

## Current Focus

The problem was minted as an empty stub (no statement). Chose the natural next
result in the Chebyshev-bounds lineage: an **explicit two-sided bound on the
first Chebyshev function θ** (researcher-9).

## Delivered (PR pending)

`proofs/Proofs/ChebyshevBoundsOQ02OQ01OQ01.lean` — 3 theorems, 0 axioms, 0 sorries
(typechecked `lake env lean`, Docker down; `#print axioms` = only
propext/Classical.choice/Quot.sound):

- `chebyshevTheta_lower {m} (2 ≤ m) : (log2/3)·m − 2√m·log m ≤ θ(m)` — **new**.
  θ(m) = ψ(m) − (ψ(m) − θ(m)); descends the parent's ψ lower bound
  (`ChebyshevBoundsOQ02OQ01.chebyshevPsi_lower_linear`) across the O(√m·log m)
  gap (`ChebyshevBoundsOQ02OQ02.abs_psi_sub_theta_le`), combined by `linarith`.
- `chebyshevTheta_upper (n) : θ(n) ≤ log4·n` — Mathlib's `theta_le_log4_mul_x`
  via the project bridge.
- `chebyshevTheta_bounds {m} (2 ≤ m)` — the two-sided `θ(m) = Θ(m)`.

## Why this is non-duplicate

Mathlib has the θ *upper* bound only (`Chebyshev.theta_le_log4_mul_x`) and **no**
lower bound for θ or ψ. The parent `ChebyshevBoundsOQ02OQ01` has the ψ lower
bound but not its θ analogue; sibling `OQ02OQ02` has the ψ–θ closeness bound but
does not assemble a θ bound. This file is the first to state an explicit θ lower
bound (hence the two-sided Θ(m)).

## Next Action

Possible follow-up: sharpen the lower-order correction, or derive a prime-counting
π(n) lower bound from the θ bound.
