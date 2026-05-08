# Session 25 (2026-05-08, researcher-1): Step 7c combine helper replay

**Phase**: ACT
**Outcome**: trig_sum_combine_small_large_const helper added (replay of stale PR #17386). Step 7 helpers fully populated.

## Problem context

PR #17386 (S23, researcher-N, 2026-05-08T19:37Z) added a `trig_sum_combine_small_large_const`
helper — the min-of-two-constants closure for the Step 7 unified-constant arithmetic in
`trig_sum_harmonic_lb`. The PR was technically sound but went CONFLICTING after several
subsequent merges:

- **S22 PR #17324** (h_interior verifier, merged ~19:10Z)
- **S22 PR #17330** (trig_sum_small_n_const, merged ~18:43Z — actually before #17386)
- **S24 PR #17438** (chebyshev_quarter_floor_log_asymp_lb, merged 21:14Z)

#17386 was never rebased — sat stale for ~3 hours, blocking the Step 7 closure path.

## Resolution: PR-rebase-via-new-branch

Per memory pattern `feedback_researcher_pr_rebase_strategy.md`, this session opens a fresh
branch off current `origin/main` and inserts the helper at the now-correct position
(between S24's `chebyshev_quarter_floor_log_asymp_lb` and `trig_sum_harmonic_lb`).

The helper proof body transfers verbatim; only the docstring is augmented to mention
S24's now-available companion. The original PR insertion point (after `trig_sum_small_n_const`,
before `trig_sum_harmonic_lb`) has been displaced by S24's helper, so the new insertion
is one section later.

## Helper added

**Location**: §X of `proofs/Proofs/Erdos1151OQ04.lean`, lines 2087–2147 (after S24's
helper which spans 2009–2086, before `trig_sum_harmonic_lb` at line 2149).

**Signature**:

```lean
private lemma trig_sum_combine_small_large_const
    (θ : ℝ)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k)
    (N₀ : ℕ)
    {C₁ : ℝ} (hC₁_pos : 0 < C₁)
    (hlarge : ∀ n : ℕ, N₀ ≤ n →
      C₁ * ((n : ℝ) * log ((n : ℝ) + 1)) ≤ S(θ, n)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      C * ((n : ℝ) * log ((n : ℝ) + 1)) ≤ S(θ, n)
```

**Proof structure**:

1. Set `N := max N₀ 1`. Apply `trig_sum_small_n_const θ hne N (by le_max_right)` to get C₂.
2. Set `C := min C₁ C₂`. The witness is `⟨C, lt_min hC₁_pos hC₂_pos, ...⟩`.
3. Case-split on `n ≤ N`:
   - **Small-n branch** (n ≤ N): apply `hsmall n hn₁ hcase`. Use `min_le_right` to drop `C` to `C₂`.
   - **Large-n branch** (n > N ≥ N₀): apply user's `hlarge n (by omega)`. Use `min_le_left` to drop `C` to `C₁`.
4. Both branches use `mul_le_mul_of_nonneg_right` with `0 ≤ n·log(n+1)` (proved via
   `Real.log_nonneg` + `mul_nonneg`).

## Step 7 closure picture (after this PR)

| Step | Helper | Status |
|------|--------|--------|
| 6c   | `trig_sum_subsum_log_lb`         | merged (S21, PR #17046) |
| 7a   | `chebyshev_quarter_floor_log_asymp_lb` | merged (S24, PR #17438) |
| 7b   | `trig_sum_small_n_const`         | merged (S22, PR #17330) |
| 7b   | `chebyshev_h_interior_of_close_and_max_index_cap` | merged (S22, PR #17324) |
| 7c   | `trig_sum_combine_small_large_const` | **this PR** (S25 replay) |

## What's left for trig_sum_harmonic_lb

**Caller-side glue** (S26+):

1. WLOG `θ ∈ (0, π/2]` via `trig_sum_reindex_symmetry` (S18, merged).
2. Pick `m := ⌊n·θ/(4π)⌋ : ℕ` — satisfies `(m : ℝ) ≥ n·θ/(4π) − 1` via `Nat.lt_floor_add_one`.
3. Apply S22 `h_interior` verifier + S21 `trig_sum_subsum_log_lb` to get
   `(sin(θ/2)/(2π)) · ((1/2)·log(m+2) − 1) ≤ S(θ, n)`.
4. Apply S24 `chebyshev_quarter_floor_log_asymp_lb` to convert
   `(1/2)·log(m+2) − 1 ≥ (1/4)·log(n+1)` for `n ≥ N₀(θ)`.
5. Combine into `hlarge : ∀ n ≥ N₀, (sin(θ/2)/(2π)) · (1/4) · n · log(n+1) ≤ S(θ, n)`.
6. Pass C₁ := sin(θ/2)/(8π), N₀, hlarge to `trig_sum_combine_small_large_const`.

This caller-glue is itself ~50–80 lines. Estimated S26 size.

## Counts delta

|              | Before (S24)     | After (S25)       | Δ    |
|--------------|-----------------:|------------------:|-----:|
| Lines        | 2288             | 2349              | +61  |
| Theorems     | 59               | 60                | +1   |
| Axioms       | 1                | 1                 | 0    |
| Sorries      | 2                | 2                 | 0    |

The +61 vs PR #17386's +58 reflects 3 additional docstring lines added to mention
S24's `chebyshev_quarter_floor_log_asymp_lb` (which didn't exist when #17386 was authored).

## Mathlib API surface

Zero new lemmas. Composes from existing helpers:
- `trig_sum_small_n_const` (file-local, S22)
- `lt_min`, `min_le_left`, `min_le_right`, `mul_le_mul_of_nonneg_right`,
  `mul_nonneg`, `Real.log_nonneg`, `le_max_right`, `le_max_left`,
  `omega`, `linarith`, `by_cases`, `push_neg`, `exact_mod_cast`.

No new imports.

## Build status

**[BUILD UNVERIFIED]** — Docker build queued. Proof body is verbatim from
PR #17386's working theorem (which was build-pending in #17386 too;
neither has Docker-verified). Per memory `feedback_researcher_lake_symlink_broken.md`,
local builds re-clone Mathlib (~30–45 min); risk profile is identical to other
build-pending Step 7 PRs.

## Stale PR #17386

Should be closed (the helper has been rebased here).

## References

- Stale PR #17386 (origin/research/...-s23-step-7c-combine, researcher-N)
- Memory: `feedback_researcher_pr_rebase_strategy.md`
- `proofs/Proofs/Erdos1151OQ04.lean` lines 2087–2147 (this PR)
- S24 PR #17438 (asymptotic log lb), S22 PRs #17324/#17330 (h_interior, small-n const),
  S21 PR #17046 (subsum log lb), S18 PR #17050 (reindex symmetry).
