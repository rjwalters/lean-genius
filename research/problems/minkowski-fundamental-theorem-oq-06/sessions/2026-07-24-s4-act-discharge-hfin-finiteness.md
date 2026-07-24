# S4 ACT — Discharge the `hFin` staging hypothesis (2026-07-24, researcher-1)

## Goal

Rung 1 of the post-#43192 plan: prove that the finiteness hypothesis `hFin` of
the staged `hlawka_*` theorems is a *theorem*, not an assumption, for bounded
sets and uniformly discrete lattices — shrinking the staged surface to exactly
the analytic inputs (`hMV` Siegel–Rogers primitive mean-value, `hInt`
integrability).

## What was proved (all unconditional, Mathlib-only)

- `subsingleton_ball_inter_of_uniform_discrete` — a ball of radius `r₀/3`
  contains at most one point of a uniformly discrete subgroup (two points
  would differ by a nonzero subgroup element of norm `< 2r₀/3 < r₀`).
- `finite_inter_of_isBounded_of_uniform_discrete` — **[ProperSpace E]**: a
  bounded set meets a uniformly discrete subgroup finitely often. Route:
  `IsBounded.isCompact_closure` → `IsCompact.totallyBounded` →
  `Metric.totallyBounded_iff` with `ε = r₀/3` → finite `biUnion` of
  subsingletons. The properness hypothesis is essential (documented
  counterexample in the file: ℤ-span of the orthonormal basis in ℓ² is
  uniformly discrete but meets the 3/2-ball infinitely often).
- `finite_primitive_inter_of_isBounded` — specialization to the primitive-
  vector set (primitives are subgroup elements).
- `hlawka_avoidance_of_isBounded` / `hlawka_ball_of_discrete` — the staged
  Minkowski–Hlawka theorems with `hFin` **discharged**: avoidance now assumes
  bounded `S` + per-ω uniform discreteness; the ball form needs no new
  hypothesis at all beyond what it already carried (balls are bounded).

## Verification

`./proofs/scripts/docker-build.sh Proofs.MinkowskiFundamentalTheoremOQ06` —
first attempt failed at the final `linarith` of the subsingleton lemma
(`r₀ ≤ ‖a-b‖ < 2r₀/3` only forces `r₀ < 0`; needs `0 ≤ ‖a-b‖` via
`norm_nonneg` to close). One-line fix; second build GREEN (see PR).

## Lean notes

- `Bornology.IsBounded.isCompact_closure` (ProperSpace) + `TotallyBounded.subset
  subset_closure` is the clean route to total boundedness of a bounded set.
- `Metric.totallyBounded_iff` (namespace `Metric`, `Pseudo/Basic.lean`) gives
  the finite `Set` cover form directly; destructure membership with
  `Set.mem_iUnion₂.mp`.
- Avoid a choice-function pigeonhole: `Set.Finite.biUnion` over ball-centers
  with per-ball `Set.Subsingleton.finite` needs no `choose` at all.

## Next

- ±-pairing rung: symmetric `S` ⟹ even primitive count, threshold `2ζ(n)`
  (classical `ζ(n)/2^(n-1)` constant).
- Density-form assessment (packing balls of radius `r/2`).
- DEEP (blocked route): the Siegel–Rogers identity itself (Haar measure on
  `SLₙ(ℤ)\SLₙ(ℝ)` absent from Mathlib).
