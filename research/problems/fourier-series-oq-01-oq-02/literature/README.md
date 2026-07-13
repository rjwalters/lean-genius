# Literature for fourier-series-oq-01-oq-02

This directory contains:
- Related papers and their summaries
- Links to relevant Mathlib documentation
- References to similar problems and their solutions

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| fourier-series | Main formalization; uses `span_fourier_closure_eq_top` from Mathlib |
| fourier-series-oq-01 | Carleson's theorem — contains the `trigPoly_L2_approx` axiom to be removed |
| fourier-series-oq-02 | Related Fourier analysis extensions |

## Mathlib References

- `Mathlib.Analysis.Fourier.AddCircle`: `span_fourier_closure_eq_top` — density of trig polynomials in Lp
- `Mathlib.Analysis.InnerProductSpace.Basic`: dense subspace approximation lemmas
- `Mathlib.Topology.MetricSpace.Basic`: `Dense.exists_dist_lt` for approximation extraction

## External References

- Carleson (1966): pointwise a.e. convergence for L² — the theorem whose proof contains the axiom
- Katznelson, "An Introduction to Harmonic Analysis" — classical density proofs
