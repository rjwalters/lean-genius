# S10 — Top-level docstring convention reconciliation (build-free)

**Date**: 2026-06-14
**Agent**: researcher-2
**Phase**: ACT (documentation; S9 axiom-elimination remains Docker-blocked)
**Type**: comment-only Lean edit (build-safe; Docker daemon down all session)

## What

The top-level module docstring of `proofs/Proofs/GeneralQuartic.lean`
(the "Mathematical Background" section) described Ferrari's completion in
the textbook `(y² + p/2 + m)²` convention, but every proved declaration in
the file — `resolventCubic`, `ferrari_factorization_id`, the
`ferrari_factorization_*_ne` theorems, `ferrari_roots_verify_ne` — uses the
file's **non-standard `(y² + p + m)²` convention** (constant `p + m`, not
`p/2 + m`). The inner docstrings (around `ferrari_factorization_id` and
`ferrari_biquad_limit`) already flag this convention explicitly; only the
top-level block was stale.

The stale block was also **internally inconsistent**: its line
`(y² + p/2 + m)² = (2m + p)y² − qy + (m² + pm + p²/4 − r)` pairs a
textbook LHS (`p/2 + m`) with a file-convention RHS coefficient (`(2m+p)y²`),
which do not match. In the textbook `p/2+m` convention the y²-coefficient is
`2m`, not `2m+p`.

## Fix

Rewrote the Mathematical Background derivation entirely in the file's
`(y² + p + m)²` convention, with an explicit NOTE that this is non-standard
and that the file's `m` differs from the textbook parameter by a p/2 shift.
The rewritten derivation is mathematically verified to match the code:

- Completion: `(y² + p + m)² = (2m+p)y² − qy + (m² + 2pm + p² − r)`
  (substitute `y⁴ = −py² − qy − r` into `y⁴ + 2(p+m)y² + (p+m)²`).
- Perfect-square / discriminant-vanishing condition:
  `q² − 4(2m+p)((p+m)² − r) = 0`.
- Expanding that condition yields exactly the file's `resolventCubic`:
  `8m³ + 20pm² + (16p² − 8r)m + (4p³ − 4pr − q²) = 0`
  (expansion checked by hand: `4(2m+p)[(p+m)²−r] − q²`).
- Factor relations: `α² = 2m+p`, `2αβ = q`, `β² = (p+m)² − r`, matching the
  `hα / hβ1 / hβ2` hypotheses of `ferrari_factorization_id`; and the sign is
  `(αy − β)` (the factors are `y² + p + m ∓ αy ± β`), corrected from the stale
  `(αy + β)`.

## Scope / safety

- Comment-only: no declaration, statement, tactic, axiom, or import changed.
- No effect on axiom count (still 3), sorry count (0), or line count semantics.
- Gallery `general-quartic/meta.json` left untouched (it is a shared parent
  entry and has concurrent audit branches; this fix is docstring-only and does
  not change any meta-tracked count).

## Still blocked

S9 axiom-elimination (`biquadratic_forward/backward`, `quartic_has_four_roots`)
remains Docker-gated; `docker info` still times out this session. Unblock
condition unchanged: re-verify the S8 merge state builds, then resume Action 1.
