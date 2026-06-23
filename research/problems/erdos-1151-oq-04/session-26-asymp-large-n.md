# Session 26 (2026-05-09, researcher-12): Asymptotic large-n packaging for θ ∈ (0, π/2]

**Phase**: ACT
**Outcome**: `trig_sum_harmonic_lb_asymp_le_half_pi` helper added (~140 lines).
This is the **`hlarge` hypothesis** consumed by S25's combine helper
(`trig_sum_combine_small_large_const`, in flight as PR #17457). Once both
land, the `θ ∈ (0, π/2]` branch of `trig_sum_harmonic_lb` closes in ~10
caller lines.

## Problem context

After S24 (`chebyshev_quarter_floor_log_asymp_lb`, merged via #17438) closed
the genuinely-asymptotic log step, the Step 7 helper inventory was complete
on the building-block side:

| Step | Helper | Status |
|------|--------|--------|
| 4    | `sin_lb_of_in_interior` / `sin_chebyshev_midpoint_lb` | merged (S16) |
| 5    | `chebyshev_term_lb_at_node`     | merged (S16) |
| 6a   | `odd_harmonic_sum_shifted_lb`   | merged (S17b) |
| 6b   | `trig_sum_subsum_lb`            | merged (S17b) |
| 6c   | `trig_sum_subsum_log_lb`        | merged (S21, PR #17046) |
| 7a (m-choice) | `chebyshev_quarter_floor_hm_le_and_cap_max` | merged (S23, #17396) |
| 7a (h_interior) | `chebyshev_h_interior_of_close_and_max_index_cap` | merged (S22, #17324) |
| 7a (log) | `chebyshev_quarter_floor_log_asymp_lb` | merged (S24, #17438) |
| 7b (small n)  | `trig_sum_small_n_const`           | merged (S22, #17330) |
| 7c (combine)  | `trig_sum_combine_small_large_const` | in flight (S25, #17457) |

What was missing was the **caller-glue** that composes these helpers into
a single `hlarge`-shaped statement. Two strategies:

  - **A**: write the full Step 7 closure of `trig_sum_harmonic_lb` in one
    monolithic 200+ line proof inside the theorem.
  - **B (chosen)**: factor the asymptotic side into a standalone helper
    (this session), so the final `trig_sum_harmonic_lb` becomes ~30 lines:
    reindex-symmetry reduction (~15) + S26 + S25 (~15).

Strategy B respects the existing modularity of the file.

## Helper added

**Location**: `proofs/Proofs/Erdos1151OQ04.lean`, after S24's
`chebyshev_quarter_floor_log_asymp_lb` (line 2086) and before
`trig_sum_harmonic_lb` (line 2225 after this session).

**Signature**:

```lean
private lemma trig_sum_harmonic_lb_asymp_le_half_pi
    (θ : ℝ) (hθ_pos : 0 < θ) (hθ_le : θ ≤ Real.pi / 2)
    (hne : ∀ (n : ℕ) (_ : 0 < n) (k : Fin n), Real.cos θ ≠ chebyshevNode n k) :
    ∃ (N₀ : ℕ) (C₁ : ℝ), 0 < C₁ ∧ ∀ n : ℕ, N₀ ≤ n →
      C₁ * ((↑n : ℝ) * Real.log ((↑n : ℝ) + 1)) ≤
        ∑ k : Fin n, Real.sin ((2 * k.val + 1 : ℝ) * Real.pi / (2 * n)) /
                     |Real.cos θ - chebyshevNode n k|
```

**Witness**: `C₁ := sin(θ/2) / (2π)`, `N₀ := max N₀_log 4` where
`N₀_log` comes from S24 (depending on `θ`) and `4` is the lower bound
required by S23 (`chebyshev_quarter_floor_hm_le_and_cap_max`).

**Proof structure** (9 steps, ~120 body lines):

1. Positivity: `sin(θ/2) > 0` since `θ/2 ∈ (0, π/4] ⊂ (0, π)`.
2. C₁ positivity from numerator + denominator.
3. Get `N₀_log` from S24 application.
4. Take `N₀ := max N₀_log 4`.
5. For each `n ≥ N₀`:
   - `exists_nearest_chebyshev_angle` → `k₀` with closeness.
   - `m := ⌊n·θ/(4π)⌋ : ℕ` — bracketed by `(m : ℝ) ≤ n·θ/(4π)` (S23 hyp,
     `Nat.floor_le`) and `n·θ/(4π) − 1 ≤ (m : ℝ)` (S24 hyp,
     `Nat.lt_floor_add_one`).
6. S23 → both `hm_le` and `hcap_max`.
7. S22 → `h_interior` (with `d := θ`).
8. S21 → mixed-cast log lower bound.
9. S24 + nonneg-prefactor multiplication + algebraic identity →
   final outer-cast bound via cast bridge.

Algebra: `sin(θ/2) · (2n/π) · (1/4)·log(n+1) = (sin(θ/2)/(2π)) · n · log(n+1) = C₁ · n · log(n+1)`.

Cast bridge from `(2 * (k.val : ℝ) + 1)` to `(2 * k.val + 1 : ℝ)` via
`Finset.sum_congr` + `congr 2` + `push_cast` + `ring` (matches the bridge
in S22's `trig_sum_small_n_const`).

## Counts delta

|              | Before (S24)     | After (S26)       | Δ    |
|--------------|-----------------:|------------------:|-----:|
| Lines        | 2288             | 2425              | +137 |
| Theorems     | 59               | 60                | +1   |
| Axioms       | 0 (file-local)   | 0                 | 0    |
| Sorries      | 2                | 2                 | 0    |

(meta: file-local axiomCount is 0; the 2 axioms tracked in meta.json live
in `Erdos1151Problem.lean`.)

## Mathlib API surface

Zero new lemmas. Composes from existing helpers + standard Mathlib:
- File-local: `exists_nearest_chebyshev_angle` (S14),
  `chebyshev_quarter_floor_hm_le_and_cap_max` (S23),
  `chebyshev_h_interior_of_close_and_max_index_cap` (S22),
  `trig_sum_subsum_log_lb` (S21),
  `chebyshev_quarter_floor_log_asymp_lb` (S24).
- Mathlib: `Real.sin_pos_of_pos_of_lt_pi`, `Real.pi_pos`, `Nat.floor_le`,
  `Nat.lt_floor_add_one`, `mul_le_mul_of_nonneg_left`, `mul_nonneg`,
  `div_nonneg`, `div_pos`, `Finset.sum_congr`, `le_of_max_le_left`,
  `le_of_max_le_right`, `field_simp`, `ring`, `linarith`, `omega`,
  `push_cast`, `congr`, `exact_mod_cast`.

No new imports.

## Step 7 closure picture (after this PR)

| Step | Helper | Status |
|------|--------|--------|
| 7a   | `trig_sum_harmonic_lb_asymp_le_half_pi` | **this PR (S26)** |
| 7c   | `trig_sum_combine_small_large_const` | in flight (S25, #17457) |

**Remaining for `trig_sum_harmonic_lb`** (~30 caller lines):

1. Reindex-symmetry reduction `θ ∈ (0, π) → θ ∈ (0, π/2]` via
   `trig_sum_reindex_symmetry` (S18, merged): `S(θ, n) = S(π−θ, n)`.
   For `θ > π/2`, set `θ' := π − θ ∈ (0, π/2)` and use the rewrite.
2. Apply S26 to get `(N₀, C₁, hlarge)` for the θ' ≤ π/2 branch.
3. Apply S25 (#17457) to combine with small-n bound; get `(C, _, h_unified)`.
4. Discharge `1 ≤ n → C · n · log(n+1) ≤ S(θ, n)`.

## Build status

**[BUILD UNVERIFIED]** — Docker build queued at session start
(LEAN_BUILD_TIMEOUT=45m). Per memory `feedback_researcher_lake_symlink_broken.md`,
local builds re-clone Mathlib (~10–15 min) then build (~15+ min); risk profile
is identical to other build-pending Step 7 PRs.

The proof is high-confidence — every step uses an existing merged helper or
trivial Mathlib lemma. The only risky bit is the algebraic identity in
Step 8 (`hC₁_eq`), which uses `field_simp; ring`; matches the pattern
used elsewhere in this file.

## Conflict-resolution plan

This PR inserts at the same file location as PR #17457 (between
`chebyshev_quarter_floor_log_asymp_lb` and `trig_sum_harmonic_lb`).
The two helpers are **independent** — neither references the other.
Whichever lands first triggers a trivial rebase in the other (just
relocate the insertion point by ~60 lines).

## References

- PR #17457 (S25, in flight, researcher-1) — `trig_sum_combine_small_large_const`
- PR #17438 (S24, merged, researcher-4) — `chebyshev_quarter_floor_log_asymp_lb`
- PR #17396 (S23, merged, researcher-3) — `chebyshev_quarter_floor_hm_le_and_cap_max`
- PR #17324 (S22, merged, researcher-3) — `chebyshev_h_interior_of_close_and_max_index_cap`
- PR #17330 (S22, merged, researcher-11) — `trig_sum_small_n_const`
- PR #17046 (S21, merged, doctor) — `trig_sum_subsum_log_lb`
- PR #17050 (S18, merged, researcher-10) — `trig_sum_reindex_symmetry`
- PR #16765 (S16, merged) — `chebyshev_term_lb_at_node`
- PR #16745 (S15, merged) — `chebyshev_angle_dist_triangle/from_nearest`
- PR #16593 (S14, merged) — `exists_nearest_chebyshev_angle`
