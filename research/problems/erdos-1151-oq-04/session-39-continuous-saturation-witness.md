# Session 39 (researcher-3, 2026-07-24) — Continuous saturation witness via clamped Lagrange polynomial

## Summary

**Sorry 2 ingredient (a) CLOSED.** The file header has documented Sorry 2
(`divergence_from_lebesgue_growth`) as needing (a) a *continuous* optimizing
function with ‖f‖_∞ ≤ 1 and Lₙf(x) = Λₙ(x), and (b) the lacunary series
assembly. S31/S33 proved the *discrete* saturation witness
(`chebyshev_lebesgue_saturated`, 0 off the node set) and deferred the
continuous lift to "Tietze extension" (S32+ plan, S38 roadmap). This session
delivers the continuous lift — with **no Tietze extension and no
piecewise-linear construction**:

> Clamp the Lagrange interpolation polynomial. g = Σₖ wₖ·ℓₖ is continuous and
> passes through the target values wₖ = sign(ℓₖ(x)) by the delta property
> ℓₖ(xⱼ) = δₖⱼ; then f = max(−1, min(1, g)) is continuous, globally bounded by
> 1, and still passes through the values (they lie in [−1, 1]). Since Lₙ only
> reads f at the nodes, Lₙf(x) = Σₖ wₖ ℓₖ(x) = Σₖ |ℓₖ(x)| = Λₙ(x).

## New declarations (Erdos1151OQ04.lean, +135/−7 lines → 2842 lines, 36 top-level theorems)

| Declaration | Content |
|---|---|
| `lagrangeBasis_apply_self` (public) | ℓₖ(xₖ) = 1 for injective nodes (`Finset.prod_eq_one` + `div_self`) |
| `lagrangeBasis_apply_ne` (public) | ℓₖ(xⱼ) = 0 for j ≠ k (`Finset.prod_eq_zero` at the i = j factor); no injectivity needed |
| `lagrangeBasis_continuous` (public) | t ↦ ℓₖ(t) continuous (`continuous_finsetProd` of affine factors) |
| `exists_continuous_bounded_through_nodes` (public) | for injective nodes and \|wₖ\| ≤ 1: ∃ continuous f, ‖f‖_∞ ≤ 1, f(xₖ) = wₖ — **no `0 < n` hypothesis** (vacuous at n = 0) |
| `chebyshev_lebesgue_saturated_continuous` (private) | ∃ continuous f, \|f\| ≤ 1, `chebyshevInterp n f x = chebyshevLebesgue n x` for ALL n, x |

Also: `chebyshev_lebesgue_saturated` docstring updated to point at the
continuous upgrade; file-header architecture list and Sorry 2 description
updated ((a) marked DONE).

## Build

`./proofs/scripts/docker-build.sh Proofs.Erdos1151OQ04` — **clean on first
attempt** (3355 jobs, exit 0), exactly 1 sorry warning (line 2820 =
`divergence_from_lebesgue_growth`, the intended survivor). Follow-up commit
swapped `continuous_finset_prod`/`continuous_finset_sum` for the
non-deprecated `continuous_finsetProd`/`continuous_finsetSum` (v4.31
deprecation warnings) and was re-verified.

## Why this unblocks both endgames

- **UBP route** (S32+ plan): the operator-norm identity ‖Λₙ_x‖ =
  chebyshevLebesgue n x on C(ℝ) needed the saturating f to be continuous;
  the discrete witness could not feed `ContinuousLinearMap` packaging.
- **Strong-form route** (what the sorry actually states): the gliding-hump /
  lacunary construction needs, for each n, a continuous near-saturating
  block. This is that block, with exact (not ε-approximate) saturation.

## Correction to the S34/S38 roadmap — UBP alone CANNOT close Sorry 2

The S34 §6 roadmap (CLM packaging → operator-norm identity → Banach–Steinhaus
contrapositive → "Sorry 2 discharge") silently assumed the S30 statement
refactor (PR #17593, weakening the conclusion to unboundedness
`∀ M, ∃ n, M < |Lₙf(x)|`). **That PR was closed unmerged** (administratively,
as branch-rot supersession, not on the merits), so `origin/main` still states
the STRONG full-limit form:

```
∃ f, Continuous f ∧ ∀ M, ∃ N, ∀ n ≥ N, M < chebyshevInterp n f x
```

Banach–Steinhaus delivers only `limsup |Lₙf(x)| = ∞`. Closing the strong form
needs the lacunary construction:

1. **Polynomial reproduction** (next missing piece, S40 candidate):
   `chebyshevInterp n p x = p x` for polynomials p with degree < n
   (Lagrange interpolation is a projection onto degree-< n polynomials).
   With it, earlier gliding-hump blocks become *transparent* at later levels:
   approximate each continuous saturating block fⱼ by a polynomial pⱼ
   (interpolation only reads node values, so Weierstrass approximation
   transfers with error Λₙ·ε), and for n > deg pⱼ, Lₙpⱼ(x) = pⱼ(x) ∈ [−1−ε, 1+ε].
2. **Block assembly**: f = Σⱼ aⱼpⱼ with aⱼ chosen inductively
   (aⱼ ≤ 2^{−j}/max(1, Λ_{n₁}(x), …, Λ_{n_{j−1}}(x)) kills cross terms from
   the tail; nⱼ chosen after aⱼ using Λₙ(x) → ∞ so aⱼΛ_{nⱼ}(x) ≥ j + 3).
   NOTE: this yields divergence along the subsequence nⱼ; upgrading to the
   stated full-limit `∀ n ≥ N` needs blocks that stay uniformly large on
   whole ranges nⱼ ≤ n ≤ deg pⱼ — genuinely harder, needs the sign structure
   of ℓₖⁿ(x) across n. Whether the strong form should instead be weakened to
   the ground-truth-faithful `limsup` form (reviving S30's refactor on its
   merits) is a decision for the next PLAN step.

## Files touched

`proofs/Proofs/Erdos1151OQ04.lean` (+135/−7 then deprecation swap),
`src/data/research/problems/erdos-1151-oq-04.json` (lineCount 2714→2842,
theoremCount 32→36 per S38 conventions), `state.md`, this session file.
0 axiom / 0 sorry change (1 sorry preserved at `divergence_from_lebesgue_growth`).
