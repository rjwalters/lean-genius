# Research State: binomial-theorem-oq-02-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (Phase-4 axiom elimination — opaque marker removed)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Session 6, researcher-1)
**Iteration**: 6

## Current Focus
Phase-4 axiom elimination — Session 5's "Stretch (independent)" goal.
Replaced `opaque standardNormalCDF : ℝ → ℝ` with a concrete
`noncomputable def standardNormalCDF (x : ℝ) : ℝ :=
∫ t in Set.Iic x, ProbabilityTheory.gaussianPDFReal 0 1 t`. Added three
elementary structural lemmas — `standardNormalCDF_nonneg`,
`standardNormalCDF_le_one`, `standardNormalCDF_mono` — that sit on the
critical path for the Phase-4 Portmanteau bridge. Imported
`Mathlib.Probability.Distributions.Gaussian.Real` to access the
Gaussian PDF API.

**Axiom count: 2 → 1.** The file is now 0 sorries / 1 axiom
(`binomial_clt_pointwise` only). Next session is the de Moivre-Laplace
discharge itself.

## Active Approach
**CDF-based** rather than the measure-theoretic Bernoulli-sum approach
sketched in iteration 1. Justification:

- Avoids the heavy `MeasureTheory` + `IsProbabilityMeasure` + Mathlib-CLT
  setup needed to use `ProbabilityTheory.iid_central_limit_theorem`.
- Matches the classical de Moivre–Laplace presentation.
- Keeps the reduction step transparent: the marginal CDF *equals* the
  binomial CDF (not just converges to it), so `Filter.Tendsto.congr` does
  the job.
- Cost (since Session 2 — RESOLVED Session 6): the original scaffold
  introduced `standardNormalCDF` as `opaque` (counted as +1 axiom);
  Session 6 replaced it with a concrete `noncomputable def`
  integrating Mathlib's `gaussianPDFReal 0 1` over `Set.Iic x`,
  removing that assumption.

## Attempt Count
- Total attempts: 6 (Sessions 1–6)
- Approaches tried:
  - **Iteration 1** (researcher-8, OBSERVE→ORIENT): planned i.i.d.-CLT
    decomposition (Sublemmas A, B, C, D). No Lean code.
  - **Iteration 2** (researcher-9, ACT): CDF-based scaffold.
    `BinomialTheoremOQ02OQ01OQ01OQ03.lean` (178 lines, 2 axioms incl.
    opaque, 1 sorry, 2 theorems). Merged in #16866.
  - **Iteration 3** (researcher-3, ACT): discharged the reduction-lemma
    sorry via `Finset.sum_fiberwise_of_maps_to`. File grew to 239 lines,
    2 axioms, **0 sorries**, 3 theorems (added `piAntidiag_apply_le`
    private lemma).
  - **Iteration 4** (researcher-10, ACT): Phase-4 prep.
    Added `binomialCDF_neg` (CDF = 0 below support) and
    `binomialCDF_mono` (monotone in `x` when `0 ≤ p ≤ 1`). File grew to
    275 lines, 2 axioms (unchanged), **0 sorries**, 5 theorems
    (substantive count: 4). Merged in #16951.
  - **Iteration 5** (researcher-1, ACT): Phase-4 prep continued.
    Added `binomialCDF_zero_le` (CDF ≥ 0) and `binomialCDF_le_one`
    (CDF ≤ 1) using `add_pow` for the binomial expansion. File grew to
    330 lines, 2 axioms (unchanged), **0 sorries**, 7 theorems
    (substantive count: 6). Merged in #16992.
  - **Iteration 6** (researcher-1, ACT — THIS SESSION): Phase-4 axiom
    elimination. Replaced `opaque standardNormalCDF` with a concrete
    `noncomputable def` integrating `ProbabilityTheory.gaussianPDFReal 0 1`
    over `Set.Iic x`; added three structural lemmas
    (`standardNormalCDF_nonneg`, `_le_one`, `_mono`). File now 369 lines,
    **1 axiom** (was 2), 0 sorries, 10 theorems
    (substantive count: 9).

## Blockers
- **Build verification**: this session could not run the Docker build
  for direct compile-check (long iteration time + worktree symlink trap).
  The scaffold uses well-tested Mathlib idioms (`Filter.Tendsto.congr`,
  `Real.sqrt`, `Finset.range`); confidence is high but not verified.
  CI is the ground truth.
- **Reduction lemma sorry**: the proof of
  `multinomialMarginalCDF_eq_binomialCDF` is a routine fiber-regrouping
  + application of the parent's `multinomial_marginal_pmf`. Phase-3 target.
- **`standardNormalCDF` opaque** (RESOLVED in Session 6): replaced
  with a concrete `noncomputable def` integrating Mathlib's
  `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`; axiom
  count dropped 2 → 1.
- **`binomial_clt_pointwise` axiom** (the only remaining axiom):
  next-session target. The cleanest path is to derive from
  `ProbabilityTheory.iid_central_limit_theorem` via the Portmanteau
  theorem at continuity points of the standard normal CDF (every
  point — Φ is continuous).

## Next Action

**Session 7 (Phase-4 axiom attack — sole remaining axiom)**: discharge
`binomial_clt_pointwise`. The cleanest path is to bridge from Mathlib's
`ProbabilityTheory.iid_central_limit_theorem` applied to a Bernoulli($p$)
i.i.d. sequence; this requires a Portmanteau-style CDF-from-measure-
weak-convergence step. The structural lemmas added in Sessions 4–6
(`binomialCDF_neg`, `binomialCDF_mono`, `binomialCDF_le_one`,
`binomialCDF_zero_le`, `standardNormalCDF_nonneg`,
`standardNormalCDF_le_one`, `standardNormalCDF_mono`) are now in place
for the bridge. Alternative path: Stirling's formula for a direct
asymptotic-analysis proof.

The Portmanteau bridge requires showing that for the standardized
Bernoulli-sum law $\mu_n$ on $\mathbb{R}$, $\mu_n \to \mathcal{N}(0,1)$
weakly implies pointwise CDF convergence at all continuity points of the
limit CDF. Since $\Phi$ is continuous everywhere, every point is a
continuity point, so the convergence is universal. Mathlib's
`ProbabilityTheory.tendsto_measure_Iic_of_tendsto_in_distribution` (or
its Mathlib equivalent — name TBD) is the direct hook.

---

**Phase-3 (Session 3)**: discharged the reduction-lemma sorry. Proof
sketch (follows the actual file):

```lean
theorem multinomialMarginalCDF_eq_binomialCDF ... := by
  unfold multinomialMarginalCDF binomialCDF
  -- Step 1: build the fibre map.
  have hmaps : ∀ k ∈ s.piAntidiag n, k i₀ ∈ Finset.range (n + 1) :=
    fun k hk => by
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact piAntidiag_apply_le s n i₀ k hk
  -- Step 2: split the multinomial sum by `j := k i₀`.
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
        (g := fun k => if ((k i₀ : ℕ) : ℝ) ≤ x
                       then multinomialProb s p n k else 0)]
  -- Step 3: term-by-term comparison.
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mem_range, Nat.lt_succ_iff] at hj
  by_cases hcond : (j : ℝ) ≤ x
  · rw [if_pos hcond]
    -- inside the fibre, k i₀ = j, so the if-condition reduces to hcond.
    -- factor it out, then apply Sublemma A.
    have h_inner : ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
        (if ((k i₀ : ℕ) : ℝ) ≤ x then multinomialProb s p n k else 0) =
        ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
          multinomialProb s p n k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      rw [hk.2, if_pos hcond]
    rw [h_inner]
    exact multinomial_marginal_pmf s p n hp i₀ hi₀ j hj
  · rw [if_neg hcond]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [hk.2, if_neg hcond]
```

Plus a short auxiliary `piAntidiag_apply_le` (private lemma): every
coordinate of a composition `k ∈ s.piAntidiag n` is at most `n`.

**Phase-4 stretch**: discharge `binomial_clt_pointwise` by bridging from
Mathlib's i.i.d. CLT. This requires the Portmanteau theorem at continuity
points of the standard normal CDF.

## References
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean:167` —
  `multinomial_marginal_pmf` (used for the reduction lemma).
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` —
  this session's scaffold (178 lines).
- `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/` — gallery
  entry (created this session).
- `proofs/Proofs/CentralLimitTheorem.lean:375` — local general CLT
  (axiomatized at the standardisation step, characteristic-function form).
- Classical: Feller, *Introduction to Probability Theory*, Vol. I (1968),
  Ch. VII §3 (de Moivre–Laplace).
