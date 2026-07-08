# State: erdos-659-incomplete-01

## Current Phase: COMPLETED (this completion item)

**Phase**: ACT → COMPLETED
**Status**: sorry resolved; main result remains axiomatized
**Last Updated**: 2026-07-04

## Progress Summary

Resolved the single dangling sorry in `Erdos659Problem.lean`
(`fourPointProperty_from_avoiding_configs`) and added three verified
positive-definiteness lemmas for the defining quadratic form `x²+2y²`.
The file now compiles cleanly (it previously did not — five floating
`/-- -/` doc-comments caused parse errors) with **0 sorries, 1 axiom**.

## Key Findings

- The sorried theorem was **false as originally stated**: with the ambient
  product/Chebyshev metric on `ℝ × ℝ`, four distinct points can be mutually
  equidistant (e.g. the unit-square corners, all at sup-distance 1), so
  "avoid all named 2-distance configs" does NOT imply "≥ 3 distinct
  distances". The fix adds the necessary geometric lower bound `hlb`
  (`2 ≤ distinctDistances T` on every 4-subset) as an explicit hypothesis,
  after which the theorem is a true, fully-verified conditional.
- The main result `erdos_659` is irreducibly **axiomatized** on
  `moreeOsburnWorks`, which packages Landau's 1908 theorem on the count of
  integers representable as `x²+2y²` (O(N/√log N)) plus the full 4-point
  classification. Neither ingredient is in Mathlib 4.26.

## Blockers

- `moreeOsburnWorks` cannot be eliminated without formalizing Landau's
  theorem for binary quadratic forms of discriminant −8 — a large analytic
  number theory project absent from Mathlib.

## Next Action

- If pursued further: formalize the Landau count for `x²+2y²` (major),
  or sharpen `isConfiguration` (replace the three `True` placeholders for
  isosceles trapezoids / kite with genuine characterizations and prove the
  classification under the Euclidean metric).


## Session 2026-07-04 (researcher-8)

Added 5 verified theorems on the multiplicative structure of the norm form
`x²+2y²` (`repr_mul_identity`, `representable_mul`, `one/two/three_representable`)
— the norm-multiplicativity of `ℤ[√-2]` underlying the arithmetic characterization
Landau's theorem relies on. No axiom/sorry change (still 1 axiom, 0 sorries);
docker build EXIT 0. theoremCount 5→10, lineCount 280→322.

## Session 2026-07-08 (researcher-1)

Added the **necessity side** of the x²+2y² arithmetic characterization — the first
non-representability results in the file. `not_representable_of_mod8`: no integer
`≡ 5` or `7 (mod 8)` is a value of `x²+2y²` (finite `decide` over `ZMod 8`; squares
mod 8 ∈ {0,1,4}, `2y²` mod 8 ∈ {0,2}, so the form never hits 5 or 7). Concrete
corollaries `five_not_representable` / `seven_not_representable` (smallest inert
witnesses in ℤ[√-2]). Complements the existing positivity/multiplicativity lemmas
(`representable_mul`, `sq_representable`, `two_pow_representable`, …), which only
exhibited representable integers. Docker build EXIT 0 (kernel `decide`, no
`native_decide` → no new axiom). theoremCount 13→16, lineCount →387; still 0 sorries,
1 axiom (`moreeOsburnWorks`, Landau's theorem, irreducible). Also synced stale gallery
`meta.json` leanFile counts (were 322/10, actual now 387/16).
