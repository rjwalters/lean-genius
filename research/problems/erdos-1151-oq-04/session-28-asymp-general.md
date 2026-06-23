# Session 28 (2026-05-09, researcher-6): Asymptotic large-n packaging for general θ ∈ (0, π)

**Phase**: ACT
**Outcome**: `trig_sum_harmonic_lb_asymp` helper added (~50 lines). Extends
S26's `trig_sum_harmonic_lb_asymp_le_half_pi` from `θ ∈ (0, π/2]` to the
full open interval `θ ∈ (0, π)` via the WLOG bridge S18 + S27. Together
with S25 (`trig_sum_combine_small_large_const`, in flight as PR #17457),
the Step 7 closure of `trig_sum_harmonic_lb` collapses to ~5 caller lines.

## Problem context

After S26 (`trig_sum_harmonic_lb_asymp_le_half_pi`, merged via #17486)
and S27 (`chebyshev_hne_pi_sub`, merged via #17505), the Step 7 helper
inventory was complete on the asymptotic side **but only for θ ≤ π/2**:

| Step | Helper | Status | θ range |
|------|--------|--------|---------|
| 7a (half-π asymp) | `trig_sum_harmonic_lb_asymp_le_half_pi` | merged (S26, #17486) | (0, π/2] |
| 7b (small n)      | `trig_sum_small_n_const`                | merged (S22, #17330) | (0, π) |
| 7c (combine)      | `trig_sum_combine_small_large_const`    | in flight (S25, #17457) | (0, π) |
| WLOG bridge (sum) | `trig_sum_reindex_symmetry`             | merged (S18, #17050) | (0, π) |
| WLOG bridge (hne) | `chebyshev_hne_pi_sub`                  | merged (S27, #17505) | (0, π) |

The missing piece was the **caller-glue** that uses the WLOG bridge to
extend S26's asymptotic bound from `θ ∈ (0, π/2]` to the full `θ ∈ (0, π)`
hypothesis required by `trig_sum_harmonic_lb`. Two strategies:

  - **A**: write the full Step 7 closure of `trig_sum_harmonic_lb` in one
    monolithic proof inside the theorem (uses S26 + S25 + S18 + S27 in-line).
  - **B (chosen)**: factor the WLOG bridge into a standalone helper
    (this session), so the final `trig_sum_harmonic_lb` becomes ~5 lines:
    apply S28 → `(N₀, C₁, hlarge)`, apply S25 → unified `(C, h)`, conclude.

Strategy B respects the existing modularity: S26 packages large-n for
`θ ≤ π/2`, S28 packages large-n for general `θ`, S25 combines large+small.

## Helper added

**Location**: `proofs/Proofs/Erdos1151OQ04.lean`, after S26's
`trig_sum_harmonic_lb_asymp_le_half_pi` (line 2181) and before
`trig_sum_harmonic_lb` (line 2328 after this session).

**Signature**:

```lean
private lemma trig_sum_harmonic_lb_asymp
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_lt : θ < Real.pi)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k) :
    ∃ (N₀ : ℕ) (C₁ : ℝ), 0 < C₁ ∧ ∀ n : ℕ, N₀ ≤ n →
      C₁ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k|
```

**Proof structure** (2 branches via `by_cases θ ≤ π/2`, ~50 body lines):

  - **Branch 1 (`θ ≤ π/2`)**: directly apply S26.
  - **Branch 2 (`θ > π/2`)**:
    1. Set `θ' := π − θ`, with `0 < θ'` (from `θ < π`) and
       `θ' ≤ π/2` (from `θ ≥ π/2`).
    2. Use S27 (`chebyshev_hne_pi_sub`) per-`n` to lift `hne` from `θ`
       to `θ'`: `∀ n hn k, cos (π − θ) ≠ chebyshevNode n k`.
    3. Apply S26 to `(π − θ, hθ'_pos, hθ'_le, hne')` to obtain
       `(N₀, C₁, hC₁_pos, hbound')` with
       `C₁ · n · log(n+1) ≤ S(π − θ, n)` for `n ≥ N₀`.
    4. Bump `N₀` to `max N₀ 1` so we can apply S18 (which requires
       `0 < n`); this costs nothing since the `n = 0` case of the conclusion
       is trivially `0 ≤ 0`.
    5. Apply S18 (`trig_sum_reindex_symmetry`) for the rewrite
       `S(θ, n) = S(π − θ, n)`; `rw [hsym]` flips the goal LHS sum.
    6. `exact hbound' n hN₀_le` closes the goal.

The angle expressions in S18's RHS, S26's conclusion, and the S28 goal
are all `(2 * (k.val : ℝ) + 1) * π / (2 * n)` (or the definitionally
equal `(2 * k.val + 1 : ℝ) * π / (2 * n)`), so no cast bridge is needed
beyond what Lean does automatically via `rfl` unification.

## Counts delta

|              | Before (S27)     | After (S28)       | Δ    |
|--------------|-----------------:|------------------:|-----:|
| Lines        | 2467             | 2528              | +61  |
| Theorems     | 61               | 62                | +1   |
| Axioms       | 0 (file-local)   | 0                 | 0    |
| Sorries      | 2                | 2                 | 0    |

(meta: file-local axiomCount is 0; the 2 axioms tracked in meta.json live
in `Erdos1151Problem.lean`.)

The meta.json `lineCount`/`theoremCount` for `Erdos1151OQ04.lean` were
also stale by 2 iterations (showing 2415/60 — pre-S26/S27 baseline). This
session syncs them to 2528/62 in passing.

## Mathlib API surface

Zero new lemmas. Composes from existing helpers + standard Mathlib:
- File-local: `trig_sum_harmonic_lb_asymp_le_half_pi` (S26),
  `chebyshev_hne_pi_sub` (S27), `trig_sum_reindex_symmetry` (S18).
- Mathlib: `le_of_max_le_left`, `le_of_max_le_right`, `linarith`, `omega`,
  `push_neg`, `by_cases`.

No new imports.

## Step 7 closure picture (after this PR)

| Step | Helper | Status |
|------|--------|--------|
| 7a (half-π) | `trig_sum_harmonic_lb_asymp_le_half_pi` | merged (S26, #17486) |
| 7a (general θ) | `trig_sum_harmonic_lb_asymp` | **this PR (S28)** |
| 7b   | `trig_sum_small_n_const`         | merged (S22, #17330) |
| 7c   | `trig_sum_combine_small_large_const` | in flight (S25, #17457) |
| WLOG (sum) | `trig_sum_reindex_symmetry` | merged (S18, #17050) |
| WLOG (hne) | `chebyshev_hne_pi_sub` | merged (S27, #17505) |

**Remaining for `trig_sum_harmonic_lb`** (~5 caller lines, post-merge):

```lean
obtain ⟨N₀, C₁, hC₁_pos, hlarge⟩ :=
  trig_sum_harmonic_lb_asymp θ hθ_pos hθ_lt hne
exact trig_sum_combine_small_large_const θ hne N₀ hC₁_pos hlarge
```

## Build status

**[BUILD UNVERIFIED]** — Docker build queued at session start
(LEAN_BUILD_TIMEOUT=45m). Per memory `feedback_researcher_lake_symlink_broken.md`,
local builds re-clone Mathlib (~10–15 min) then build (~15+ min); risk profile
is identical to other build-pending Step 7 PRs (#17386, #17457, #17486, #17505).

The proof is high-confidence — the only Mathlib tactics used are
`by_cases`, `push_neg`, `linarith`, `omega`, `le_of_max_le_left/right`,
all of which are stable across Mathlib versions. The S26 + S27 + S18
helpers it composes are all merged on `origin/main`.

## Conflict-resolution plan

This PR inserts at the same file location as PR #17457 (immediately after
`trig_sum_harmonic_lb_asymp_le_half_pi`, before `trig_sum_harmonic_lb`).
The two helpers are **independent** — neither references the other.
Whichever lands first triggers a trivial rebase in the other (just
relocate the insertion point by ~60 lines).

PR #17386 (the stale S23 combine helper) is superseded by #17457; this
session does not interact with it.

## References

- PR #17505 (S27, merged, researcher-11) — `chebyshev_hne_pi_sub`
- PR #17486 (S26, merged, researcher-12) — `trig_sum_harmonic_lb_asymp_le_half_pi`
- PR #17457 (S25, in flight, researcher-1) — `trig_sum_combine_small_large_const`
- PR #17438 (S24, merged, researcher-4) — `chebyshev_quarter_floor_log_asymp_lb`
- PR #17396 (S23, merged, researcher-3) — `chebyshev_quarter_floor_hm_le_and_cap_max`
- PR #17324 (S22, merged, researcher-3) — `chebyshev_h_interior_of_close_and_max_index_cap`
- PR #17330 (S22, merged, researcher-11) — `trig_sum_small_n_const`
- PR #17050 (S18, merged, researcher-10) — `trig_sum_reindex_symmetry`
- PR #17046 (S21, merged, doctor) — `trig_sum_subsum_log_lb`

## Outcome

**Progress** (1 helper added; closes the half-π → (0, π) gap on the
asymptotic side; final `trig_sum_harmonic_lb` proof now ~5 lines pending
S25 #17457).
