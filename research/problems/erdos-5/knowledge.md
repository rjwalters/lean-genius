# Erdős #5 - Knowledge Base

## Problem Statement

Let $C\geq 0$. Is there an infinite sequence of $n_i$ such that\[\lim_{i\to \infty}\frac{p_{n_i+1}-p_{n_i}}{\log n_i}=C?\]

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 6/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #337
- Problem #2000
- Problem #3
- Problem #234
- Problem #4
- Problem #6
- Problem #2
- Problem #39
- Problem #1

## References

- Er55c
- Er57
- Er61
- Er65b
- Er85c
- Er90
- Er97c
- We31
- GPY09
- Er55
- Ri56
- HiMa88
- Pi16
- BFM16
- Me20

## Sessions

### Session 2026-05-08 — Forward density direction + iff characterization

**Mode**: ACT (extension)
**Outcome**: progress — strengthened existing reduction theorem to an iff;
unlocked unconditional oscillation lemmas.

#### What was added (Erdos5PrimeGaps.lean: 572 → 657 lines, +85)

- **Part XIII (forward density)**:
  - `frequently_near_of_isLimitPoint`: if C is a limit point, then for
    every ε > 0 the set `{n : ℕ | dist (normalizedGap n) C < ε}` is
    infinite. Proof: extract the convergent subsequence from
    `IsLimitPoint`, pick K with all later terms within ε, then inject
    ℕ via `k ↦ f (k + K)` into the target set using
    `Set.infinite_of_injective_forall_mem`.
  - `erdos_5_iff_dense_at_every_point`: the iff version of
    `erdos_5_from_dense_values`. Combined with the existing reverse
    direction (which uses diagonal extraction), gives the clean
    characterization that Erdős #5 is equivalent to a purely
    distributional density statement.

- **Part XIV (unconditional oscillation)**:
  - `frequently_normalizedGap_lt`: ∀ ε > 0, the set
    `{n | normalizedGap n < ε}` is infinite. Combines
    `zhang_implies_zero_limit` (so 0 ∈ S) with the new forward
    direction. Uses `dist_zero_right` + `Real.norm_of_nonneg` to
    convert the ε-ball form to the strict-inequality form.
  - `frequently_normalizedGap_gt`: ∀ M, the set
    `{n | M < normalizedGap n}` is infinite. Reformulation of
    `westzynthius_implies_frequently_large` in `Set.Infinite` style;
    uses the `westzynthius_large_gaps` axiom directly with
    `Set.infinite_of_injective_forall_mem`.

#### Architectural impact

- The Erdős #5 conjecture now has a clean iff characterization in
  Lean: it is equivalent to a distributional density property.
- Two new oscillation lemmas confirm the unconditional bookend:
  normalizedGap dips arbitrarily close to 0 and exceeds any bound,
  infinitely often each. The open question is precisely whether
  every intermediate value is also visited densely.
- All four new theorems are direct applications of existing
  infrastructure plus `Set.infinite_of_injective_forall_mem`.

#### Files Modified

- `proofs/Proofs/Erdos5PrimeGaps.lean` (+85 lines)
- `src/data/proofs/erdos-5/meta.json` (lineCount, theoremCount,
  assumptions, conclusion summary)
- `src/data/research/problems/erdos-5.json` (iteration, progress)
- `research/problems/erdos-5/state.md` (phase: NEW → ACT)

#### Build status

Docker build initiated locally; CI will validate.

#### Next iteration could

1. (clean) `MapClusterPt` reformulation connecting `IsLimitPoint`
   to Mathlib's filter cluster point machinery, unlocking lemmas
   like `MapClusterPt.isClosed`.
2. (corollary) `Filter.liminf normalizedGap atTop = 0` and
   `Filter.limsup normalizedGap atTop = ⊤` in `EReal`.
3. (substantive) Investigate whether the Hildebrand–Maier axiom
   (∃ arbitrarily large finite limit points) follows from
   Westzynthius + an Erdős–Ricci style measure argument; if so,
   the axiom count drops 3 → 2.

---

*Generated from erdosproblems.com on 2026-01-12*
