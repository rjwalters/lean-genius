# Research State: fourth-root-2-irrational-oq-01

## Current State
**Phase**: ACT
**Path**: full
**Since**: 2026-06-27T11:32:59-07:00
**Iteration**: 2
**Last Updated**: 2026-07-01 (researcher-6)

## Current Focus
Structural splitting-field content added on top of the existing degree-8 result in
`Proofs/FourthRoot2SplittingFieldOQ01.lean` (PR #30937 proved `[ℚ(⁴√2,i):ℚ]=8` and the
realness obstruction `i ∉ ℚ(⁴√2)`, but not the splitting/generation structure).

## Progress (researcher-6, 2026-07-01, VERIFIED 0-axiom)
Added Parts V–VI to `FourthRoot2SplittingFieldOQ01.lean` (168 → 323 lines, +~15 thm/defs):
- Explicit roots in `K = ℚ⟮frc, Complex.I⟯`: `rt = ⁴√2`, `im_i = i`, with `rt^4 = 2`,
  `im_i^2 = -1` (`rt_pow_four`, `im_i_sq`).
- **`X4_sub_2_factor`**: `X⁴ − 2 = (X−α)(X+α)(X−iα)(X+iα)` over `K` (α = ⁴√2).
- **`X4_sub_2_splits`** / `X4_sub_2_splits_map`: `X⁴ − 2` splits over `K`.
- **`two_roots_nonreal`**: `±i·⁴√2` are the two non-real roots (im = ±⁴√2 ≠ 0).
- **`X4_sub_2_isSplittingField`**: `Polynomial.IsSplittingField ℚ K (X⁴ − 2)` — the full
  structural statement (splits + roots generate `K`, via `i = (i·⁴√2)·(⁴√2)⁻¹` and
  `lift`-injectivity `adjoin_gens_eq_top`).
- `#print axioms` on all new results: only `propext / Classical.choice / Quot.sound`.

### Still open
The named group isomorphism `Gal(K/ℚ) ≃* DihedralGroup 4` (the last remaining part of
the OQ). `X4_sub_2_isSplittingField` supplies the `IsSplittingField`/`IsGalois` footing
that a `MulEquiv`-to-`DihedralGroup 4` construction can now build on.

## Prior Focus
Initial problem understanding. Read problem.md and gather context.

## Active Approach
None yet.

## Attempt Count
- Total attempts: 0
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
None.

## Next Action
Read problem.md thoroughly and acquire full context.
Then move to ORIENT phase to explore literature and related proofs.
