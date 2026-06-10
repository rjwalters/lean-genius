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

### Session 2026-06-09 — Eventually-form liminf/limsup corollaries (S3)

**Mode**: ACT (extension)
**Outcome**: progress — packaged S2's `Set.Infinite` oscillation lemmas
into a `Filter.Eventually` form witnessing `liminf = 0` / `limsup = ⊤`
along `atTop`. Verified Docker build clean (3061 jobs).

#### What was added (Erdos5PrimeGaps.lean: 657 → 707 lines, +50)

- **Part XV (liminf / limsup corollaries)**:
  - `normalizedGap_oscillates`: trivial packaging of
    `frequently_normalizedGap_lt` and `frequently_normalizedGap_gt`.
  - `not_eventually_normalizedGap_le`: for every `M : ℝ`,
    `¬ ∀ᶠ n in atTop, normalizedGap n ≤ M`. Proof: convert the
    eventual upper bound to `∃ N, ∀ n ≥ N, …`, then exhibit the set
    `{n | M < normalizedGap n}` as a finite subset of `Set.Iio N`,
    contradicting `frequently_normalizedGap_gt M`.
  - `not_eventually_le_normalizedGap`: dual statement —
    `¬ ∀ᶠ n in atTop, ε ≤ normalizedGap n` for every `ε > 0`.

#### Architectural impact

- The two `not_eventually_*` lemmas together with the existing
  `normalizedGap_nonneg` are *exactly* the data needed to derive
  `Filter.limsup = ⊤` and `Filter.liminf = 0` in any complete
  extension of `ℝ` (e.g. `EReal`). Future iterations can take the
  explicit `EReal` step without redoing the `Set.Infinite` ↔
  `Filter.Eventually` bridge.
- The S2 dichotomy "either the conjecture holds, or some
  intermediate value is eventually avoided" is now spelled in a
  filter-native idiom alongside the `Set.Infinite` form.

#### Meta fixes piggybacked

- Outer `axiomCount` corrected: 4 → 3 (the file has only three
  `axiom` declarations: `westzynthius_large_gaps`,
  `zhang_bounded_gaps`, `hildebrand_maier_large_limit_points`; no
  structure-encoded assumptions). Both inner and outer counts now
  agree at 3.
- `theoremCount`: 33 → 36 (added three new theorems).
- `lineCount`: 657 → 707 (wc -l canonical).
- `assumptions` text bumped from `26 theorems` to `36 theorems`
  and references the new corollaries by name.
- `conclusion.summary` extended to mention the `Filter.limsup` /
  `Filter.liminf` reading made unconditional by S3.

#### Files Modified

- `proofs/Proofs/Erdos5PrimeGaps.lean` (+50 lines, +3 theorems)
- `src/data/proofs/erdos-5/meta.json` (lineCount, theoremCount,
  axiomCount fix, assumptions, conclusion summary, inner
  leanFile mirrors)
- `research/problems/erdos-5/state.md` (iteration 2 → 3, refreshed
  next-action list)
- `research/problems/erdos-5/knowledge.md` (this session entry)

#### Build status

Docker build clean: `Build completed successfully (3061 jobs)`
(log: `.loom/logs/researcher-9-erdos5-s3-build.log`).

#### Next iteration could

1. (S4 clean) Explicit `EReal` coercion: state and prove
   `Filter.limsup (fun n => (normalizedGap n : EReal)) atTop = ⊤`
   using `not_eventually_normalizedGap_le` and an `EReal`
   characterization (`EReal.limsup_eq_top_iff_frequently_gt` or
   similar).
2. (S4 clean) `MapClusterPt` reformulation linking `IsLimitPoint`
   to Mathlib's filter cluster point machinery.
3. (S5 substantive) Reduce the axiom budget by attempting
   Hildebrand–Maier ← Westzynthius + Erdős–Ricci measure argument.

---

*Generated from erdosproblems.com on 2026-01-12*
