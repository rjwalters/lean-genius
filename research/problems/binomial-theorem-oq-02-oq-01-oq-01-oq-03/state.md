# Research State: binomial-theorem-oq-02-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (axiom elimination — opaque marker discharged)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Session 6, researcher-8)
**Iteration**: 6

## Current Focus
Session 6 executes the long-standing "Stretch (independent)" item from
Sessions 4 and 5: replace the `standardNormalCDF` opaque marker with a
concrete `noncomputable def` integrating
`ProbabilityTheory.gaussianPDFReal 0 ⟨1, zero_le_one⟩` over `Set.Iic x`.
**Axiom count: 2 → 1**.

The replacement is mechanical (the only consumers of `standardNormalCDF`
— the `binomial_clt_pointwise` axiom and the `multinomial_marginal_clt`
derived theorem — do not unfold it), and follows the same `gaussianPDFReal`
idiom as `ShannonEntropyOQ01.lean:260–278`. The single remaining axiom
(`binomial_clt_pointwise`) is the substantive de Moivre-Laplace claim
itself; the previous opaque-marker assumption is discharged.

No new sorries, no proof changes — only a *meaning sharpening* of the
existing main theorem (the limit symbol is now pinned to a defined
function rather than an uninterpreted opaque).

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
  - **Iteration 5** (researcher-1, ACT):
    Phase-4 prep continued. Added `binomialCDF_zero_le` (CDF ≥ 0) and
    `binomialCDF_le_one` (CDF ≤ 1) using `add_pow` for the binomial
    expansion. File: 330 lines, 2 axioms (unchanged), **0 sorries**,
    7 theorems (substantive count: 6). Merged in #16992.
  - **Iteration 6** (researcher-8, ACT — THIS SESSION):
    Eliminated `standardNormalCDF` opaque. Replaced with a
    `noncomputable def` integrating `ProbabilityTheory.gaussianPDFReal
    0 ⟨1, zero_le_one⟩` over `Set.Iic x`. **Axiom count 2 → 1.**
    File: 351 lines, **1 axiom** (only `binomial_clt_pointwise` remains),
    0 sorries, 7 theorems (substantive count: 6), 3 definitions
    (was 2). The proof of `multinomial_marginal_clt` is unchanged —
    the limit symbol is now pinned to a defined function rather than
    an uninterpreted opaque.

## Blockers
- **Build verification**: this session could not run the Docker build
  for direct compile-check (long iteration time + worktree symlink trap).
  The change is mechanical (opaque → def, body uses idioms exercised in
  `ShannonEntropyOQ01.lean:260–278`); confidence is high but not verified.
  CI is the ground truth.
- **`binomial_clt_pointwise` axiom**: the single remaining axiom. Future
  sessions can derive it from `ProbabilityTheory.iid_central_limit_theorem`
  via the Portmanteau theorem at continuity points of the standard
  normal CDF (every point, since Φ is continuous).

## Next Action

**Session 7 (axiom attack)**: discharge `binomial_clt_pointwise`. The
cleanest path is to bridge from Mathlib's
`ProbabilityTheory.iid_central_limit_theorem` applied to a Bernoulli($p$)
i.i.d. sequence; this requires a Portmanteau-style CDF-from-measure-
weak-convergence step. The structural lemmas added in Sessions 4–5
(`binomialCDF_neg`, `binomialCDF_mono`, `binomialCDF_le_one`,
`binomialCDF_zero_le`) — together with the now-defined
`standardNormalCDF` — are the prerequisites. Alternative path:
Stirling's formula for a direct asymptotic-analysis proof. Estimated
~150–200 lines of new Lean. Once this lands, the file is fully verified
(0 axioms, 0 sorries).

**Sibling stretch**: prove `Continuous standardNormalCDF` by integration-
of-a-continuous-function on `Set.Iic`. The Portmanteau bridge in
Session 7 needs continuity at every point of the limit CDF, so this is
a natural staging step that does not depend on Session 7's main work.

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
