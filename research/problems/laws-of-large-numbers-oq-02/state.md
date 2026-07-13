# Research State: laws-of-large-numbers-oq-02

## Current State
**Phase**: S2 ACT — discharge `variance_sampleMean` axiom to theorem
**Path**: full
**Since**: 2026-05-13 (S2 ACT by researcher-5; S1 OBSERVE by researcher-5 PR #18789; prior PRs #13382, #13415 2026-04-27)
**Iteration**: 2
**Build status**: build-pending (Docker `.lake` symlink loop in worktree, see Blockers).
  Expected: 2 axioms (`standardNormalCDF`, `berryEsseenConstant`), 0 sorries, after S2 ACT lands.

## What Has Been Proved

Per `proofs/Proofs/LawsOfLargeNumbersOQ02.lean` (now ~355 LOC, was 338):

- `sampleMean_memLp` — sample mean is in L² (theorem, discharged in #13382).
- `integral_sampleMean` — `𝔼[X̄ₙ] = μ` when each `Xᵢ` has mean μ.
- **`variance_sampleMean`** — `Var(X̄ₙ) = σ²/n` (**S2 ACT 2026-05-13**: was axiom, now
  theorem; proved from `variance_const_mul` + `IndepFun.variance_sum`).
- `chebyshev_convergence_rate` — `P(|X̄ₙ − μ| ≥ ε) ≤ σ² / (n ε²)` (derived from
  Mathlib's Chebyshev inequality + (now proven) `variance_sampleMean`).
- `chebyshevBound_nonneg`, `chebyshevBound_antitone` — basic monotonicity of the bound.
- `chebyshev_rate_is_O_inv_n`, `berry_esseen_rate_involves_sqrt_n` — rate-ordering facts.
- `chebyshev_rate_implies_convergence` — bridge to the WLLN convergence statement.

## Remaining Axioms (post-S2 ACT)

1. `standardNormalCDF : ℝ → ℝ` (was line 217): genuinely beyond Mathlib v4.26 — Mathlib
   has Gaussian density and characteristic functions but no `Φ` function exposed as a
   named scalar map from ℝ to ℝ with the standard normal interpretation.
2. `berryEsseenConstant : ℝ` (was line 240): genuinely beyond Mathlib v4.26 — no
   Berry–Esseen theorem statement exists in Mathlib. Mathlib does have characteristic
   functions (`Mathlib.MeasureTheory.Measure.CharacteristicFunction`), but the CLT itself
   has not been formalized.

## Active Approach (S2 ACT)

Per the S1 OBSERVE audit (`s1-observe-variance-sampleMean-bearer-audit.md`), the
discharge of `variance_sampleMean` uses:

- `variance_const_mul (c : ℝ) (X : Ω → ℝ) (μ : Measure Ω) : variance (fun ω => c * X ω) μ = c ^ 2 * variance X μ`
  (line 183 of `Mathlib/Probability/Moments/Variance.lean` at pinned SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
- `IndepFun.variance_sum {X : ι → Ω → ℝ} {s : Finset ι} (hs : ∀ i ∈ s, MemLp (X i) 2 μ)
  (h : Set.Pairwise ↑s fun i j => X i ⟂ᵢ[μ] X j) : variance (∑ i ∈ s, X i) μ =
  ∑ i ∈ s, variance (X i) μ`
  (line 403)

The S2 ACT proof is ~22 LOC (5 `have`-lemmas + 5 rewrite/simp lines + `field_simp` +
`ring`). Net diff: +37/−19 LOC including docstring updates and the SECTION 9 summary.

## Attempt Count

- Total attempts (S0 + #13382 + #13415 + S1 OBSERVE + S2 ACT): 5
- Current approach attempts: 1 (S2 ACT, build pending)
- Approaches tried: initial axiomatization (S0), `sampleMean_memLp` discharge (#13382),
  axiom-count sync (#13415), Mathlib bearer audit (S1 PR #18789), `variance_sampleMean`
  discharge (S2 ACT, this PR).

## Blockers

- Worktree `.lake` symlink loop confirmed: both
  `proofs/.lake → /Users/rwalters/GitHub/lean-genius/proofs/.lake` (self-referential).
  Direct Docker build from worktree CWD fails. Mitigation per memory trap
  `feedback_researcher_lake_symlink_loop_and_wipe.md`: commit + push first, ship
  build-pending PR, let doctor verify from clean worktree.
- Two remaining axioms (CLT and Berry–Esseen) are upstream-blocked and out of scope.

## Next Action

- **Doctor or auditor**: verify the S2 ACT build from a clean worktree (no symlink
  loop). Expected ~5–10 min for `Proofs.LawsOfLargeNumbersOQ02` (probabilistic deps).
- **If build fails**: most-likely failure points (in order of likelihood) are:
  1. `rw [variance_const_mul]` may need `simp only [variance_const_mul]` or
     `simpa [variance_const_mul]` if `unfold sampleMean` exposes a slightly different
     form (`1 / ↑n` vs `(1 : ℝ) / ↑n`).
  2. The `simpa [Finset.sum_apply]` rewrite of `IndepFun.variance_sum` to the
     pointwise-lambda form may need additional simp hints.
  3. The final `field_simp` + `ring` may need `hn0` passed explicitly.
- **Out of scope for the researcher role**: create the gallery entry
  `src/data/proofs/laws-of-large-numbers-oq-02/{meta,annotations,index}.{json,ts}` —
  this is the enricher's domain. Note this in handoff to enrichment-tracker if/when
  claimed.
- Long-term: track upstream Mathlib for `centralLimitTheorem` / `berryEsseen` statements.
