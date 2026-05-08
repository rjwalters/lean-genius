# Session 8 (2026-05-08, researcher-1): dE_dk theorem replay

**Phase**: ACT
**Outcome**: dE_dk theorem assembled and committed (build pending).
**PR base**: fresh `origin/main` (HEAD: 1d5abc3ce24, post #17431/#17430/#17429).

## Context: stale PR #17371

PR #17371 (created 2026-05-08T19:18Z by another researcher) had the
`dE_dk : HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k` theorem
ready, claiming to close §8 + §9 with `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.

Between 19:18 and now (~21:30Z), two K-side PRs landed on top of #17371's
base:

- **#17373** (S6, K-side chain rule for `dK_dk`, merged 2026-05-08T~)
  added new §10 with `dIntegrandK`, `dIntegrandK_continuous`,
  `dIntegrandK_integrable`, `integrandK_hasDerivAt_in_k`.
- **#17431** (S7, K-side uniform bound, merged 2026-05-08T21:14Z) added
  new §11 with `boundDIntegrandK`, `boundDIntegrandK_continuous`,
  `boundDIntegrandK_integrable`, `dIntegrandK_abs_le_bound`.

Both are independent of the E-side work in #17371 (no overlap with §1, §8,
or §9), but the file's append point (originally line 562 in #17371's base)
moved to line 829 in current main, and the section numbering used by
#17371 ("§10 dE/dk") collides with the K-side §10 in main. Result:
`gh pr view 17371` reports `mergeable: CONFLICTING`. The PR was never
rebased.

## Resolution: PR-rebase-via-new-branch

Per memory pattern `feedback_researcher_pr_rebase_strategy.md` ("when
claimed slug has CONFLICTING PR by another researcher, open a new PR off
`origin/main` rather than force-pushing their branch"), this session opens
a fresh branch off current `origin/main` with the dE_dk theorem from
#17371 renumbered to **§12** (since K-side §10/§11 are now in main).

**The Lean theorem itself transferred verbatim** — no change to the proof
body, just the section header comment. All conflicts in #17371 were
metadata-level (state.md, meta.json line/theorem counts, problem JSON).

## What's in §12

```lean
-- ============================================================================
-- § 12. dE/dk = (E − K) / k for 0 < k < 1
-- ============================================================================

theorem dE_dk (hk_pos : 0 < k) (hk_lt : k < 1) :
    HasDerivAt ellipticE ((ellipticE k - ellipticK k) / k) k := by
  set M : ℝ := (k + 1) / 2 with hM_def
  -- ... 7 hypotheses ...
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hs_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_diff
  have h_deriv :
      HasDerivAt (fun κ => ∫ θ in (0 : ℝ)..π / 2, ellipticIntegrandE κ θ)
        (∫ θ in (0 : ℝ)..π / 2, dIntegrandE k θ) k := h.2
  rw [integral_dIntegrandE_eq hk_pos hk_lt] at h_deriv
  exact h_deriv
```

The seven hypotheses (`hs_nhds`, `hF_meas`, `hF_int`, `hF'_meas`,
`h_bound`, `h_bound_int`, `h_diff`) are discharged via:

| Hypothesis      | From                                                                              |
|-----------------|-----------------------------------------------------------------------------------|
| `hs_nhds`       | `isOpen_Ioo.mem_nhds ⟨-M < k, k < M⟩` with `M := (k+1)/2`                         |
| `hF_meas`       | `Filter.eventually_of_forall` + `(integrandE_continuous _).aestronglyMeasurable`  |
| `hF_int`        | `ellipticE_integrable k` (from §1)                                                |
| `hF'_meas`      | `(dIntegrandE_continuous hk_sq_lt_one).aestronglyMeasurable` (§8)                 |
| `h_bound`       | `MeasureTheory.ae_of_all` + `dIntegrandE_abs_le_bound` (§9)                        |
| `h_bound_int`   | `boundDIntegrandE_integrable hM_sq_lt_one` (§9)                                    |
| `h_diff`        | `MeasureTheory.ae_of_all` + `integrandE_hasDerivAt_in_k` (§8)                      |

Final integral rewrite uses §8's `integral_dIntegrandE_eq` to convert
`∫ dIntegrandE k θ dθ` to `(E(k) − K(k))/k`. The function
`fun κ ↦ ∫ ellipticIntegrandE κ θ dθ` is definitionally `ellipticE`.

## Counts delta

|              | Before (S7) | After (S8) | Δ    |
|--------------|-------------|------------|------|
| Lines        | 829         | 928        | +99  |
| Definitions  | 9 (incl. §10–11) | 9    | 0    |
| Theorems     | 36          | 37         | +1   |
| Axioms       | 1           | 1          | 0    |
| Sorries      | 0           | 0          | 0    |

Note: meta.json `theoremCount` was 36 before; only `dE_dk` was added in §12.

## Mathlib API surface

Zero new lemmas. Composes from:

- `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
  (Mathlib/Analysis/Calculus/ParametricIntervalIntegral)
- `Filter.eventually_of_forall`, `MeasureTheory.ae_of_all`
- `Set.Ioo`, `isOpen_Ioo`, `IsOpen.mem_nhds`
- `Real.norm_eq_abs`
- §1 (`ellipticE_integrable`), §8 (`integrandE_continuous`,
  `dIntegrandE_continuous`, `integrandE_hasDerivAt_in_k`,
  `integral_dIntegrandE_eq`), §9 (`dIntegrandE_abs_le_bound`,
  `boundDIntegrandE_integrable`)

## Build status

[BUILD UNVERIFIED — Docker build queued]

The proof is a **verbatim copy** of #17371's working theorem (which was
build-verified per its commit message). No changes to the proof body, so
the only correctness risk is interaction with the K-side §10/§11
machinery — and §12 imports nothing from §10/§11, so this should be
clean.

## Next session (S9)

Mirror §12 for the K-side: assemble `dK_dk` using §10 (K chain rule) and
§11 (K uniform bound). Same band M := (k+1)/2 strategy. The K-side
integral identity (`∫ dIntegrandK k θ dθ = (E - (k')²K) / (k (k')²)`)
may need to be proved separately first (~80–120 lines IBP) — that's the
§8-analog gap on the K-side.

## References

- Stale PR #17371 (origin/research/amgm-oq-04-oq-02-s6-dE-dk-1778267827)
- Memory: `feedback_researcher_pr_rebase_strategy.md`
- `proofs/Proofs/AmgmInequalityOQ04OQ02.lean` §12 (this PR)
- `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean`
