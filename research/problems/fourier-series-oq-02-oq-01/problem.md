# Problem: Alternative Mathlib proof of riemannLebesgue_of_holder

**Slug**: fourier-series-oq-02-oq-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Given the existing `riemannLebesgue_of_holder` theorem in `FourierHolderDecay`:

```lean
theorem riemannLebesgue_of_holder (C : ℝ≥0) (α : ℝ≥0)
    (f : AddCircle T → ℂ) (hf : IsHolderOnCircle C α f) (hα : 0 < α) :
    Tendsto (fun n : ℤ => fourierCoeff f n) cofinite (𝓝 0)
```

Can this be proved more cleanly via the Mathlib chain:

$$\text{Hölder} \Rightarrow \text{Continuous} \Rightarrow L^1 \Rightarrow \text{Riemann-Lebesgue (Mathlib)}$$

rather than via the current quantitative decay bound?

### Plain Language

The current proof of `riemannLebesgue_of_holder` goes through a quantitative Fourier
coefficient decay estimate (`fourierCoeff_holder_decay`): it shows |ĉₙ| ≤ C/|n|^α, then
derives that the set of frequencies where |ĉₙ| ≥ ε is finite.

Mathlib has `Mathlib.Analysis.Fourier.RiemannLebesgueLemma` which provides the
Riemann-Lebesgue theorem for L¹ functions. The question is whether we can give a
*shorter*, more principled proof by:

1. Showing every α-Hölder function (α > 0) is continuous
2. Continuous functions on a compact space (AddCircle T) are bounded, hence integrable (L¹)
3. Applying Mathlib's R-L lemma directly

This would produce a cleaner derivation that doesn't depend on the intermediate
quantitative bounds.

### Why This Matters

- Demonstrates how to connect the gallery's custom Hölder API to Mathlib's mainstream analysis
- Would reduce the complexity of `FourierSeriesOQ02.lean` (currently 486 lines with 1 axiom)
- Shows the gallery's quantitative estimates can be complemented by qualitative Mathlib paths
- Models good Lean formalization practice: reuse Mathlib rather than reproving

## Known Results

### What's Already Proven

- `riemannLebesgue_of_holder` — proved in `FourierSeriesOQ02.lean` via quantitative decay
- `fourierCoeff_holder_decay` — decay estimate: |ĉₙ| ≤ (C/2)·(T/(2|n|))^α for n≠0
- `IsHolderOnCircle` → continuous is standard (Hölder with α > 0 implies uniform continuity)
- Mathlib: `Mathlib.Analysis.Fourier.RiemannLebesgueLemma` exists
- Mathlib: `Mathlib.Topology.MetricSpace.Holder` has `HolderWith.uniformContinuous`

### What's Still Open

- Whether Mathlib's R-L for AddCircle gives exactly `Tendsto ... cofinite (𝓝 0)`
- The exact Mathlib theorem name needed (may use `VanishingAtInfinity` vs `cofinite` filter)
- Whether gallery `fourierCoeff` matches Mathlib's `AddCircle.fourierCoeff` or needs bridging

### Our Goal

Provide an alternative proof of `riemannLebesgue_of_holder` using:
```lean
theorem riemannLebesgue_of_holder_v2 ...  := by
  have hcont : Continuous f := holder_continuous ...
  have hL1 : Integrable f := hcont.integrable_of_compact_closure ...
  exact mathlib_RL_for_L1 hL1
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fourier-series-oq-02` | Parent proof; contains existing Lean proof | Quantitative decay, cofinite filter |
| `fourier-series-oq-04` | Fourier series, Dirichlet kernel | AddCircle Fourier theory |
| `fourier-series-oq-03` | Dirichlet conditions (BV functions) | R-L for BV, integration by parts |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib Bridge** (preferred):
   - Look up Mathlib's AddCircle Fourier coefficient R-L theorem name
   - Show `IsHolderOnCircle → ContinuousOn` via `HolderWith.continuous`
   - Show compact + continuous → L¹
   - Apply Mathlib R-L
   - Risk: Mathlib R-L may use a different filter or different normalization

2. **Upgrade existing proof**:
   - Keep current proof structure but replace explicit decay computation
     with `tendsto_of_tendsto_of_tendsto` applied to the bound tending to 0
   - Less clean but likely to compile quickly

### Key Difficulties

- Matching the `cofinite` filter to whatever filter Mathlib's R-L uses
  (may be `atTop` on `ℕ` vs cofinite on `ℤ`)
- The gallery uses custom `fourierCoeff` — need to check it matches Mathlib's API
- `IsHolderOnCircle` is gallery-local; need to extract `ContinuousOn` via `HolderWith`

### What Would a Proof Need?

- Key lemma 1: `IsHolderOnCircle C α f → Continuous f` (from `HolderWith.uniformContinuous`)
- Key lemma 2: Mathlib R-L: `Integrable f → Tendsto (fourierCoeff f) cofinite (𝓝 0)` on AddCircle
- Key lemma 3: `Continuous f → Integrable f` on compact `AddCircle T`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathematical path is completely clear (Hölder → continuous → integrable → R-L)
- The challenge is finding right Mathlib lemma names and handling API mismatches
- `Mathlib.Analysis.Fourier.RiemannLebesgueLemma` exists and covers this case
- Similar Mathlib bridging work has succeeded in other gallery proofs

**Estimated Effort**:
- Exploration (finding Mathlib lemma names): 1-2 hours
- Proof assembly: 2-4 hours

## References

### Papers
- Zygmund, *Trigonometric Series*, Chapter 2 — standard reference for Fourier decay

### Mathlib
- `Mathlib.Analysis.Fourier.RiemannLebesgueLemma` — R-L for L¹ (the main tool needed)
- `Mathlib.Topology.MetricSpace.Holder` — HolderWith, continuity implications
- `Mathlib.Analysis.Fourier.AddCircle` — AddCircle Fourier coefficients
- `Mathlib.MeasureTheory.Function.L2Space` — integrability on compact spaces

## Metadata

```yaml
tags:
  - harmonic-analysis
  - fourier-series
  - mathlib
  - riemann-lebesgue
  - holder-continuity
  - integrability
related_proofs:
  - fourier-series-oq-02
  - fourier-series-oq-03
difficulty: medium
source: gallery-gap
created: 2026-04-21
```

**Significance**: 7/10
**Tractability**: 7/10
