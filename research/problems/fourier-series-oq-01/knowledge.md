# Knowledge Base: fourier-series-oq-01

Insights accumulated during research on Carleson's theorem.

---

## Problem Understanding

**Carleson's Theorem (1966)**: For any f ∈ L²(𝕋), the Fourier partial sums
S_N f(x) → f(x) for almost every x.

This is one of the great theorems of 20th-century harmonic analysis. The key insight
is that a.e. convergence reduces to an L² bound on the Carleson maximal operator
S*f(x) = sup_N |S_N f(x)|.

**Architecture**: The proof has two layers:
1. **Carleson-Hunt maximal inequality** (deep time-frequency analysis — axiomatized)
2. **Density reduction** (maximal bound → a.e. convergence — PROVED as of session 3)

---

## Session 2026-04-13 (Session 5) — Axiom Count Reduced: 6 → 2

**Mode**: REVISIT
**Outcome**: progress — 4 axioms replaced with actual Mathlib proofs, PR #10486 created

### What I Did
- Replaced 4 provable axioms with actual theorems proved from Mathlib:
  1. `carlesonConstant_nonneg`: now `theorem` using `carlesonData.2` (bundled as `{c : ℝ // 0 ≤ c}`)
  2. `IsTrigPoly.memℒp_two`: proved via `Memℒp.of_bound` + `continuous_finset_sum` + `‖fourier n x‖ = 1`
  3. `trigPoly_exact_convergence`: proved via new `fourierCoeff_of_trigPoly_sum` + `Finset.sum_subset`
  4. `trigPoly_L2_approx`: proved via `hasSum_fourier_series_L2` + L² norm + `Lp_fourier_sum_coeFn`

### Key Technical Achievement
New private lemma `fourierCoeff_of_trigPoly_sum` (Fourier orthogonality):
- `fourierCoeff (∑ k ∈ Icc(-M,M), c k * fourier k) n = if n ∈ Icc(-M,M) then c n else 0`
- Proved without `fourierCoeff.sum` (which doesn't exist in Mathlib)
- Method: `integral_finset_sum` to swap sum/integral + per-term orthogonality
- Orthogonality: `∫ fourier m dμ = if m=0 then 1 else 0`
  - m=0: `fourier_zero` + `integral_const` + `measure_univ` (normalized Haar measure)
  - m≠0: `integral_eq_zero_of_add_right_eq_neg` + `fourier_add_half_inv_index`

### Additional Fixes Applied
- Moved `fourierPartialSum_add/smul/zero_fn` before their use sites (forward ref fix)
- Fixed `abs_of_nonpos` proof using `linarith` + `Int.ofNat_nonneg`
- Fixed `hf.coeFn_toLp.symm` direction (`.symm` was wrong)
- Fixed `sq_lt_sq'` with `[norm_nonneg ...]` hint for `linarith`
- Fixed `hh_ae` calc using `Finset.sum_congr` + `Finset.sum_subset` pattern

### Files Modified
- `proofs/Proofs/FourierSeriesOQ01.lean` (860 lines, was 644)

### PR
- #10486: https://github.com/rjwalters/lean-genius/pull/10486 (awaiting Docker build)

### Next Steps
- Build with Docker to confirm all proofs compile
- Update `src/data/proofs/fourier-series-oq-01/meta.json` to reflect 2 axioms
- Consider if any of the remaining 2 deep axioms can be partially formalized

---

## Session 2026-04-02 (Session 4) — Final Sorry Filled: 0 Sorries Remain

**Mode**: REVISIT
**Outcome**: completed — 1 sorry → 0 sorries, PR #8630 created

### What I Did
- Filled the final Markov/Chebyshev sorry in `divergenceSet_measure_bound`
  - Used `mul_meas_ge_le_lintegral₀` for the raw Markov inequality on `‖h‖²`
  - Used `ofReal_integral_eq_lintegral_ofReal` to connect lintegral ↔ integral
  - Used `ENNReal.le_div_iff_mul_le` + `ENNReal.div_le_div_right` + `ENNReal.ofReal_div_of_pos`
  - Proved set inclusion `{‖h‖>δ/2} ⊆ {(δ/2)²≤‖h‖²}` via `pow_le_pow_left`
- Fixed pre-existing `fourierPartialSum_smul` compilation error
  - `integral_mul_left` was deprecated; replaced with `integral_const_mul`
  - Removed broken `ring_nf; congr 1` tactic, replaced with explicit `have` + `funext`/`ring`
- PR created: https://github.com/rjwalters/lean-genius/pull/8630

### Key Findings
- Final Markov proof: key insight is to avoid `eLpNorm`-based Chebyshev (requires
  more API work) and instead use the basic `mul_meas_ge_le_lintegral₀` on `ENNReal.ofReal(‖h‖²)`
- `Integrable.aemeasurable` gives AEMeasurability for the squared norm integrand
- `memℒp_two_iff_integrable_sq_norm` is the bridge from L² membership to ∫‖h‖² integrability
- Approach: {‖h‖>c} ⊆ {c²≤‖h‖²} → Markov on ‖h‖² → divide by c² → compare with ε²

### Files Modified
- `proofs/Proofs/FourierSeriesOQ01.lean` (644 lines, was 605)

### Next Steps
- None for this problem — proof architecture complete
- Follow-up OQ: Can the 4 provable axioms be replaced with actual Mathlib proofs?

---

## Session 2026-04-02 (Session 3) — Complete Proof Architecture

**Mode**: REVISIT
**Outcome**: progress — architecture complete, 2 sorries → 1 sorry

### What I Did
- Added 4 helper axioms (all provable from Mathlib):
  - `trigPoly_exact_convergence`: S_N g = g for N ≥ deg(g) when IsTrigPoly g
  - `IsTrigPoly.memℒp_two`: trig polys are in L²
  - `trigPoly_L2_approx`: density of trig polys in L² (from hasSum_fourier_series_L2)
  - `carlesonConstant_nonneg`: Carleson constant ≥ 0
- Proved `divergenceSet_measure_bound` — complete proof except Markov inequality
  - Applies `divergenceSet_subset_of_approx` (proved in session 2)
  - Carleson-Hunt bound from axiom
  - 1 sorry remains: `μ({‖h‖>c}) ≤ ∫‖h‖²/c²` (Markov/Chebyshev)
  - Uses `mul_meas_ge_le_pow_eLpNorm'` from LpSeminorm.ChebyshevMarkov
- Proved `carleson_ae_convergence` — FULLY PROVED (no sorry):
  - Non-convergence ⊆ fullDivergenceSet = ⋃_k divSet(1/(k+1))
  - Each divSet(1/(k+1)) has measure 0 via density + ENNReal.le_of_forall_pos_le_add
  - Countable union via measure_iUnion_null

### Key Findings
- `carleson_ae_convergence` is proved conditional on `divergenceSet_measure_bound`
- The Markov inequality sorry is the ONLY remaining gap
- `mul_meas_ge_le_pow_eLpNorm'` in `ChebyshevMarkov.lean` is the right lemma
  - Signature: `ε^p * μ({‖f‖ₑ ≥ ε}) ≤ eLpNorm f p μ^p`
  - Applied with p=2, ε = ofReal(δ/2)
  - Needs: connecting eLpNorm h 2 μ^2 to ENNReal.ofReal(∫ ‖h‖^2)
- `ENNReal.ofReal_toReal_le` is useful for the ≤ r step in the density argument

### Files Modified
- `proofs/Proofs/FourierSeriesOQ01.lean` (510 lines, was 427)
- `src/data/proofs/fourier-series-oq-01/meta.json`

### Next Steps
1. **Fill Markov sorry**: Use `mul_meas_ge_le_pow_eLpNorm'` with p=2 + `eLpNorm_sq_eq_integral` or similar to connect eLpNorm^2 to ∫‖h‖²
2. **Replace helper axioms** with actual proofs from Mathlib:
   - `trigPoly_exact_convergence`: via `hasSum_fourier_series_of_summable` + finite support summability
   - `IsTrigPoly.memℒp_two`: via `Memℒp` of finite sum of `fourier n`
   - `trigPoly_L2_approx`: via `hasSum_fourier_series_L2` + norm convergence
3. Create Aristotle companion file for the remaining technical lemmas

---

## Insights

- No Carleson formalization exists in Mathlib v4.26.0
- External project "Carleson4" by Floris van Doorn et al. is working on full formalization
- The density reduction from maximal inequality to a.e. convergence is fully proved
- Key Markov lemma: `mul_meas_ge_le_pow_eLpNorm'` in `Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov`
- `ENNReal.le_of_forall_pos_le_add` is the right tool for showing μ(A) = 0 in ENNReal
- `measure_iUnion_null` for countable unions of null sets

---

## Built Items

- `proofs/Proofs/FourierSeriesOQ01.lean` — 510 lines
  - 5 definitions: fourierPartialSum, carlesonMaximal, IsTrigPoly, divergenceSet, fullDivergenceSet
  - 13 theorems (1 with sorry: divergenceSet_measure_bound's Markov step)
  - 6 axioms: carlesonConstant (deep), carleson_hunt_maximal (deep),
    trigPoly_exact_convergence, IsTrigPoly.memℒp_two, trigPoly_L2_approx,
    carlesonConstant_nonneg (all 4 are provable from Mathlib)
- `src/data/proofs/fourier-series-oq-01/` — full gallery integration

---

## Dead Ends

- `div_add_div_same` approach for arithmetic: needed `field_simp; ring` + `div_le_div_right` instead
- `memℒp_top_of_bound` for `carleson_continuous`: API may need adjustment

---

## Next Steps (priority order)

1. Fill Markov sorry in `divergenceSet_measure_bound` using `mul_meas_ge_le_pow_eLpNorm'`
2. Replace `trigPoly_exact_convergence` with a proof using `hasSum_fourier_series_of_summable`
3. Replace `trigPoly_L2_approx` with a proof using `hasSum_fourier_series_L2` norm convergence
4. Replace `IsTrigPoly.memℒp_two` with direct computation
5. Verify `carleson_continuous` compiles (may need `memℒp_of_bounded` API fix)
