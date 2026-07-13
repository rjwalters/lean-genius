# Problem: Replace trigPoly_L2_approx axiom with Mathlib proof

## Statement

### Plain Language
The Lean formalization of Carleson's theorem (`FourierSeriesOQ01.lean`) contains an axiom
`trigPoly_L2_approx` that asserts trigonometric polynomials are dense in L²(T). Replace
this axiom with a proof using Mathlib's existing `span_fourier_closure_eq_top`.

### Formal Statement
```lean
-- Current axiom to eliminate (FourierSeriesOQ01.lean line 233):
axiom trigPoly_L2_approx :
  ∀ (f : Lp ℝ 2 (AddCircle T)) (ε : ℝ), 0 < ε →
    ∃ g : trigPoly T, ‖(f : Lp ℝ 2 (AddCircle T)) - (g : Lp ℝ 2 (AddCircle T))‖ < ε

-- Mathlib resource:
-- span_fourier_closure_eq_top : closedSpan (fourier '') = ⊤  (in Lp sense)
```

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - fourier-analysis
  - mathlib
  - density
  - L2-space
  - axiom-elimination
```

**Significance**: 6/10 — removes a stated axiom, strengthening the verification status
**Tractability**: 6/10 — Mathlib has the result; bridging the formulation is the challenge

## Why This Matters

1. **Axiom integrity** — `trigPoly_L2_approx` is an unproved assumption in Carleson's theorem
   formalization; removing it moves the proof closer to `verified` status
2. **Mathlib already has the result** — `span_fourier_closure_eq_top` in `Mathlib.Analysis.Fourier.AddCircle`
   is exactly the density theorem needed; this is a formulation bridging task
3. **Reusable technique** — the pattern of extracting approximations from `closedSpan` = ⊤
   applies to other Fourier and harmonic analysis proofs in the gallery

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| fourier-series | Already uses `span_fourier_closure_eq_top`; extract the technique |
| fourier-series-oq-01 | The file containing the axiom to be eliminated |
