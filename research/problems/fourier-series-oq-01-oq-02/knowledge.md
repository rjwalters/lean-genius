# Knowledge Base: fourier-series-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Replace the `trigPoly_L2_approx` axiom in `proofs/Proofs/FourierSeriesOQ01.lean` (line 233)
with a proved theorem using Mathlib's existing density results.

The axiom states that for any L² function f and ε > 0, there exists a trigonometric
polynomial g such that ‖f - g‖_L² < ε. This is exactly the density of trigonometric
polynomials in L²(T) — a classical result.

**Key observation**: `proofs/Proofs/FourierSeries.lean` already uses `span_fourier_closure_eq_top`
from Mathlib (line 258) to prove `span_fourier_dense`. This is the same density result.
The bridge from `span_fourier_closure_eq_top` to the approximation form in FourierSeriesOQ01
is the main task.

---

## Insights

- `Mathlib.Analysis.Fourier.AddCircle` contains `span_fourier_closure_eq_top` which asserts
  that the span of Fourier monomials is dense in Lp(AddCircle T μ) for 1 ≤ p < ∞.
- The main FourierSeries.lean (line 76) documents: `span_fourier_closure_eq_top` : density of
  trigonometric polynomials.
- FourierSeriesOQ01.lean also uses `trigPoly_L2_approx` (line 495) in the proof of Carleson's
  theorem to approximate arbitrary L² functions by trig polynomials.
- The strategy: use `dense_iff_closure_eq_top.mpr` + `span_fourier_closure_eq_top` to extract
  an approximating sequence, then use L² norm bounds.

---

## Dead Ends

[Approaches known not to work will be documented here]
