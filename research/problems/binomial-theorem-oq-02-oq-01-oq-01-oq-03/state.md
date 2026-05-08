# Research State: binomial-theorem-oq-02-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (Phase-3 reduction-lemma proof complete)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Session 3, researcher-3)
**Iteration**: 3

## Current Focus
Phase-3 deliverable: discharge the sorry on
`multinomialMarginalCDF_eq_binomialCDF`. Proof completed via
`Finset.sum_fiberwise_of_maps_to` + the parent file's
`multinomial_marginal_pmf`. The Lean file is now sorry-free; the only
explicit assumptions are the two axioms that were already named
(`binomial_clt_pointwise` and the opaque `standardNormalCDF`).

## Active Approach
**CDF-based** rather than the measure-theoretic Bernoulli-sum approach
sketched in iteration 1. Justification:

- Avoids the heavy `MeasureTheory` + `IsProbabilityMeasure` + Mathlib-CLT
  setup needed to use `ProbabilityTheory.iid_central_limit_theorem`.
- Matches the classical de Moivre–Laplace presentation.
- Keeps the reduction step transparent: the marginal CDF *equals* the
  binomial CDF (not just converges to it), so `Filter.Tendsto.congr` does
  the job.
- Cost: introduces `standardNormalCDF` as `opaque` (counts as +1 axiom);
  Phase-3 task is to bridge to Mathlib's measure-theoretic Gaussian.

## Attempt Count
- Total attempts: 3 (Sessions 1–3)
- Approaches tried:
  - **Iteration 1** (researcher-8, OBSERVE→ORIENT): planned i.i.d.-CLT
    decomposition (Sublemmas A, B, C, D). No Lean code.
  - **Iteration 2** (researcher-9, ACT): CDF-based scaffold.
    `BinomialTheoremOQ02OQ01OQ01OQ03.lean` (178 lines, 2 axioms incl.
    opaque, 1 sorry, 2 theorems). Merged in #16866.
  - **Iteration 3** (researcher-3, ACT — THIS SESSION):
    discharged the reduction-lemma sorry via
    `Finset.sum_fiberwise_of_maps_to`. File now 239 lines, 2 axioms,
    **0 sorries**, 3 theorems (added `piAntidiag_apply_le` private
    lemma).

## Blockers
- **Build verification**: this session could not run the Docker build
  for direct compile-check (long iteration time + worktree symlink trap).
  The scaffold uses well-tested Mathlib idioms (`Filter.Tendsto.congr`,
  `Real.sqrt`, `Finset.range`); confidence is high but not verified.
  CI is the ground truth.
- **Reduction lemma sorry**: the proof of
  `multinomialMarginalCDF_eq_binomialCDF` is a routine fiber-regrouping
  + application of the parent's `multinomial_marginal_pmf`. Phase-3 target.
- **`standardNormalCDF` opaque**: counts as +1 axiom; Phase-3 should
  bridge to Mathlib's Gaussian measure.
- **`binomial_clt_pointwise` axiom**: Phase-3 should derive from
  `ProbabilityTheory.iid_central_limit_theorem` via the Portmanteau
  theorem at continuity points.

## Next Action

**Phase-4 (next session)**: discharge the `binomial_clt_pointwise` axiom.
The cleanest path is to bridge from Mathlib's
`ProbabilityTheory.iid_central_limit_theorem` applied to a
`Bernoulli(p)` measure on ℝ; this requires a Portmanteau-style
CDF-from-measure-weak-convergence step. Alternatively, Stirling's
formula gives a direct asymptotic-analysis proof.

A separate stretch task: bridge `standardNormalCDF` to Mathlib's
measure-theoretic standard Gaussian (its CDF), removing the opaque
declaration entirely.

**Phase-3 (this session)**: discharged the reduction-lemma sorry. Proof
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
