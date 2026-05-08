# Research State: binomial-theorem-oq-02-oq-01-oq-01-oq-03

## Current State
**Phase**: ACT (Phase-4 prep — tendsto-saturation lemmas added on right tail)
**Path**: full
**Since**: 2026-05-07
**Last Updated**: 2026-05-08 (Session 8, researcher-6)
**Iteration**: 8

## Current Focus
Phase-4 prep continued — Session 8 adds three asymptotic-saturation
(`Filter.Tendsto`-form) lemmas covering the right-tail of both Φ and the
binomial CDF, plus the left-tail of the binomial CDF:

- `standardNormalCDF_tendsto_one_atTop`: `Tendsto Φ atTop (𝓝 1)`. Proof
  uses `MeasureTheory.aecover_Iic Filter.tendsto_id` to get the AECover
  for `volume` along `atTop`, then
  `AECover.integral_tendsto_of_countably_generated` on the integrable
  `gaussianPDFReal 0 1`, with the total integral identified as 1 by
  `ProbabilityTheory.integral_gaussianPDFReal_eq_one 0 one_ne_zero`.
- `binomialCDF_tendsto_one_atTop` (under `0 ≤ p ≤ 1`): eventually
  constant via `binomialCDF_eq_one`, packaged with `Tendsto.congr'` and
  `Filter.eventually_ge_atTop (n : ℝ)`.
- `binomialCDF_tendsto_zero_atBot`: eventually constant via
  `binomialCDF_neg`, packaged with `Tendsto.congr'` and
  `Filter.eventually_lt_atBot (0 : ℝ)`. No `p` constraint required.

These three lemmas convert the boundary-value information from
Sessions 4–7 into the `Filter.Tendsto` form Mathlib's Portmanteau
direction at `±∞` consumes. Together with `standardNormalCDF_continuous`
(Session 7) and the four-corner `binomialCDF_*` lemmas (Sessions 4–7),
all the right-tail prerequisites are in place. The matching
`standardNormalCDF_tendsto_zero_atBot` (Φ left tail) is the remaining
structural-CDF prerequisite: the proof needs the `Antitone` direction
(`Antitone.tendsto_setIntegral` on `(fun y => Iic (-y))` composed with
`Filter.tendsto_neg_atBot_atTop`) since `aecover_Iic` only cares about
covers expanding to the whole space, not contracting to `∅`.

**Axiom count: 1 (unchanged).** The file is now 0 sorries / 1 axiom
(`binomial_clt_pointwise` only), 17 theorems (substantive count: 13),
582 lines.

**Build verification.** Session 8 was conducted under the broken
`/Users/rwalters/GitHub/lean-genius/proofs/.lake` self-symlink trap
(see memory feedback `feedback_researcher_lake_symlink_broken.md`),
so a Docker build was not run. Each lemma uses well-tested Mathlib
idioms (`AECover` API, `Filter.Tendsto.congr'`, `filter_upwards` over
`eventually_ge_atTop` / `eventually_lt_atBot`), so confidence is high
but not verified locally. CI is the ground truth for this PR.

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
- Total attempts: 7 (Sessions 1–7)
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
  - **Iteration 6** (researcher-1, ACT): Phase-4 axiom elimination.
    Replaced `opaque standardNormalCDF` with a concrete `noncomputable def`
    integrating `ProbabilityTheory.gaussianPDFReal 0 1` over `Set.Iic x`;
    added three structural lemmas (`standardNormalCDF_nonneg`, `_le_one`,
    `_mono`). File grew to 369 lines, **1 axiom** (was 2), 0 sorries,
    10 theorems (substantive count: 9). Merged in #17014.
  - **Iteration 7** (researcher-11, ACT — THIS SESSION): Phase-4 prep —
    completed the standard-normal CDF structural library. Added
    `standardNormalCDF_continuous` (Φ is continuous on ℝ) plus a private
    bridge lemma `standardNormalCDF_eq_zero_plus_intervalIntegral`
    (`Φ x = Φ 0 + ∫_{0..x} gaussianPDFReal 0 1 t`). The continuity
    proof reduces to `MeasureTheory.Integrable.continuous_primitive`
    after the bridge lemma, which in turn uses
    `MeasureTheory.intervalIntegral_tendsto_integral_Iic`,
    `intervalIntegral.integral_add_adjacent_intervals`, and
    `tendsto_nhds_unique`. Two new imports
    (`Mathlib.MeasureTheory.Integral.IntegralEqImproper`,
    `Mathlib.MeasureTheory.Integral.DominatedConvergence`). File now
    445 lines, **1 axiom** (unchanged), 0 sorries, 12 theorems
    (substantive count: 10).

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
  Session 8 target. The cleanest path is to derive from
  `ProbabilityTheory.iid_central_limit_theorem` via the Portmanteau
  theorem at continuity points of the standard normal CDF (every
  point — Φ is continuous, now machine-verified by Session 7's
  `standardNormalCDF_continuous`).
- **Mathlib survey result** (Session 7): Mathlib does NOT contain a
  single `iid_central_limit_theorem` lemma. Instead it has
  `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` (random-
  variable convergence-in-distribution form, requires centered + unit-
  variance + i.i.d. + identically-distributed). There is also no
  Mathlib lemma stating "the law of (X₁ + ... + Xₙ) for i.i.d.
  Bernoulli(p) X₁,...,Xₙ equals Binomial(n,p)" — that bridge needs to
  be constructed manually from `PMF.binomial` and pushforward measures.
  Realistic estimate: discharge of `binomial_clt_pointwise` is ~300–500
  lines across **2+ sessions**, not feasible in one session.

## Next Action

**Session 8 — Phase-4 axiom attack (Lemma A: Bernoulli→Binomial measure
bridge)**. With the CDF-structure library complete on both sides
(Sessions 4–7), the next bottleneck is the measure-theoretic side:
prove that for n i.i.d. Bernoulli(p) random variables `X₁, ..., Xₙ` on
a finite product probability space, the pushforward of the product
measure under `(ω ↦ Σ Xᵢ(ω))` has law equal to `Binomial(n, p)` (with
PMF matching `binomialCDF`'s summand). This is the foundational bridge
that lets Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum` apply.

Subsequent sessions:
- **Session 9 (Lemma C — Portmanteau bridge)**: prove the abstract
  bridge "convergence in distribution + continuous limit CDF ⟹
  pointwise CDF convergence". Combines Mathlib's Portmanteau lemmas
  (`Mathlib/MeasureTheory/Measure/Portmanteau.lean`) with our new
  `standardNormalCDF_continuous`.
- **Session 10 (axiom discharge)**: assemble Lemmas A + C + Mathlib's
  CLT into the proof of `binomial_clt_pointwise`. Convert axiom →
  theorem; status promotes to `verified` (axiomCount 1 → 0).

Alternative single-session path that was considered but rejected:
direct Stirling's-formula asymptotic analysis of `C(n,j) p^j (1-p)^(n-j)`
near the mean. Self-contained but tedious; competing with the
Portmanteau path's reuse of Mathlib infrastructure.

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
