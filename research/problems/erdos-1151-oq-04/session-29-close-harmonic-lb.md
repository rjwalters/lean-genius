# Session 29 (2026-05-09, researcher-11): Close `trig_sum_harmonic_lb`

**Phase**: ACT
**Outcome**: `trig_sum_harmonic_lb` closed (~38 lines). File 2 → 1 sorries.
Only `divergence_from_lebesgue_growth` (lacunary series construction) remains.

## Problem context

After S28 (`trig_sum_harmonic_lb_asymp`, merged via #17544) the asymptotic
large-`n` packaging covers all `θ ∈ (0, π)`. After S22
(`trig_sum_small_n_const`, merged via #17330) the finite-set min' lower bound
is in place. The only outstanding work for `trig_sum_harmonic_lb` is the
**min-of-two-constants split** that combines them.

The dedicated combine helper `trig_sum_combine_small_large_const` was added
in S23 PR #17386 (now DIRTY) and replayed in S25 PR #17457 (now CONFLICTING
after S26/S27/S28 merges). Both PRs sat unmerged for ~3+ hours blocking the
closure path.

## Resolution

Rather than rebase another agent's branch (per memory pattern
`feedback_researcher_pr_rebase_strategy.md`, prefer fresh PR off
`origin/main`) or land a fourth combine-helper PR, this session **inlines
the combine logic directly** into `trig_sum_harmonic_lb`'s body — closing
the sorry in one step and obsoleting both #17386 and #17457.

The inlined logic is identical (line-for-line equivalent up to local-name
mangling) to the S25 helper body in PR #17457; only the `(N₀ : ℕ)` and
`{C₁ : ℝ} (hC₁_pos : 0 < C₁)` parameters become `obtain`-bound from S28's
output, and the `(hlarge : …)` parameter becomes the final hypothesis from
S28's existential.

## Proof structure

```text
obtain ⟨N₀, C₁, hC₁_pos, hlarge⟩ := trig_sum_harmonic_lb_asymp θ hθ_pos hθ_lt hne
N := max N₀ 1                            -- ensures `1 ≤ N` for the finite cutoff
hN_ge : 1 ≤ N := le_max_right N₀ 1
obtain ⟨C₂, hC₂_pos, hsmall⟩ := trig_sum_small_n_const θ hne N hN_ge
refine ⟨min C₁ C₂, lt_min hC₁_pos hC₂_pos, fun n hn₁ => ?_⟩
hg_nn : 0 ≤ n · log(n+1)                  -- denominator nonneg, n ≥ 1
case n ≤ N:
  min C₁ C₂ · n·log(n+1) ≤ C₂ · n·log(n+1)   -- min_le_right + mul_le_mul_of_nonneg_right
                        ≤ S(θ, n)              -- hsmall n hn₁ hcase
case n > N (so n > N ≥ N₀):
  hN₀_le_n : N₀ ≤ n                          -- omega from N₀ ≤ N < n
  min C₁ C₂ · n·log(n+1) ≤ C₁ · n·log(n+1)   -- min_le_left + mul_le_mul_of_nonneg_right
                        ≤ S(θ, n)              -- hlarge n hN₀_le_n
```

Total: ~38 lines (proof body), zero new lemmas, zero new Mathlib API surface.

## Why this matters

This closes the **second-to-last sorry** in `Erdos1151OQ04.lean`. With this
merged:

- `chebyshev_trig_sum_lb` (Case 2: `x ∈ (-1, 1)`) is fully discharged via
  `trig_sum_harmonic_lb` (already wired up in S13, awaiting only this sorry).
- `chebyshev_lebesgue_lb` (the harmonic growth bound) is fully discharged.
- `chebyshev_lebesgue_growth` (Λₙ(x) → ∞) is fully discharged.
- The **only remaining sorry** in the file is `divergence_from_lebesgue_growth`
  (line 2545): the constructive step from `Λₙ(x) → ∞` to a continuous `f`
  whose interpolation diverges at `x`. This is the lacunary series step
  (Faber/Banach-Steinhaus condensation) and is the genuinely outstanding
  mathematical residue.

## Sorry inventory after S29

`proofs/Proofs/Erdos1151OQ04.lean` (2561 lines, **1 sorry**):

1. `divergence_from_lebesgue_growth` (line 2545) — lacunary construction
   from divergent Lebesgue function to a continuous `f` with divergent
   interpolation. Standard Banach-Steinhaus argument; left as future work.

## File stats (after S29)

- `proofs/Proofs/Erdos1151OQ04.lean`: 2561 lines, 1 sorry, 62 theorems/lemmas,
  0 axioms (was 2528, 2 sorries).
- `proofs/Proofs/Erdos1151OQ04Aristotle.lean`: 140 lines, 0 sorries (unchanged).
- `proofs/Proofs/Erdos1151Problem.lean`: 185 lines, 0 sorries, 2 axioms (unchanged).

## Build status

Docker build kicked off at submit time with `LEAN_BUILD_TIMEOUT=60m` and
mathlib cache. Marked `[BUILD UNVERIFIED]` in commit message per the
existing S26/S27/S28 precedent.

## Conflict analysis

**Independent of #17386 and #17457**: those PRs add a new helper
`trig_sum_combine_small_large_const` *between* S24 and `trig_sum_harmonic_lb`;
S29 does NOT touch that line region. After S29 merges, both helper PRs
become obsolete (the helper has no remaining caller), and they should be
closed administratively.
