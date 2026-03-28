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
2. **Density reduction** (maximal bound → a.e. convergence — provable from Mathlib)

---

## Insights

- No Carleson formalization exists in Mathlib v4.26.0
- External project "Carleson4" by Floris van Doorn et al. is working on full formalization
- The density reduction from maximal inequality to a.e. convergence is a standard
  technique that generalizes beyond Fourier series (Banach principle / Cotlar's lemma)
- Key Mathlib infrastructure available: fourierCoeff, fourier, haarAddCircle,
  hasSum_fourier_series_L2, span_fourier_closure_eq_top, Memℒp
- Two axioms (trigPoly_dense_L2, trigPoly_partialSum_eq) are actually provable from
  existing Mathlib — next session should eliminate these

---

## Built Items

- `proofs/Proofs/FourierSeriesOQ01.lean` — 440 lines
  - 5 definitions: fourierPartialSum, carlesonMaximal, IsTrigPoly, divergenceSet, fullDivergenceSet
  - 13 theorems (4 with sorries)
  - 5 axioms (Carleson constant, positivity, Hunt weak-type, trig poly convergence, density)
- `src/data/proofs/fourier-series-oq-01/` — full gallery integration

---

## Dead Ends

(None yet — first session)

---

## Next Steps

1. Prove `carleson_ae_convergence` by filling in the density argument
2. Prove `divergenceSet_measure_bound` using Carleson-Hunt + Chebyshev
3. Eliminate `trigPoly_dense_L2` axiom using Mathlib's `span_fourier_closure_eq_top`
4. Eliminate `trigPoly_partialSum_eq` axiom from Fourier coefficient vanishing
5. Create Aristotle companion file for routine lemmas
