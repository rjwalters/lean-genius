# Research State: binomial-theorem-oq-02-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (Phase-2 scaffold complete)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Session 2, researcher-9)
**Iteration**: 2

## Current Focus
Phase-2 STATEMENT scaffold landed. The Lean file
`proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` exists; the multinomial
marginal CLT is *stated* in CDF form and *derived* (not axiomatized
separately) from two axioms: the classical de Moivre–Laplace theorem
(in CDF form) and an opaque `standardNormalCDF` marker. One sorry remains
in the reduction lemma `multinomialMarginalCDF_eq_binomialCDF` (provable from
the parent file's `multinomial_marginal_pmf` by fiber regrouping).

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
- Total attempts: 2 (Sessions 1–2)
- Approaches tried:
  - **Iteration 1** (researcher-8, OBSERVE→ORIENT): planned i.i.d.-CLT
    decomposition (Sublemmas A, B, C, D). No Lean code.
  - **Iteration 2** (researcher-9, ACT): CDF-based scaffold.
    `BinomialTheoremOQ02OQ01OQ01OQ03.lean` (178 lines, 2 axioms incl.
    opaque, 1 sorry, 2 theorems).

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

**Phase-3 (next session)**: discharge the reduction-lemma sorry. The proof
should follow this skeleton:

```lean
theorem multinomialMarginalCDF_eq_binomialCDF ... := by
  -- Regroup the sum over k into fibers over j = k(i₀):
  rw [show multinomialMarginalCDF s p n i₀ x =
        ∑ j ∈ Finset.range (n + 1),
          if (j : ℝ) ≤ x then
            ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
              BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k
          else 0
      from ?_]
  · -- Apply multinomial_marginal_pmf to each fiber:
    apply Finset.sum_congr rfl
    intro j hj
    split_ifs with hjx
    · rw [BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf s p n hp i₀ hi₀ j
            (by simp [Finset.mem_range] at hj; omega)]
    · rfl
  · -- Reverse the regrouping (sum-over-piAntidiag = sum-over-fibers):
    sorry  -- standard Finset partition identity
```

Two subgoals: (1) the fiber-regrouping identity (provable via
`Finset.sum_partition` or directly), (2) the per-fiber application of
`multinomial_marginal_pmf`. The second is one rewrite.

**Phase-3 stretch**: discharge `binomial_clt_pointwise` by bridging from
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
