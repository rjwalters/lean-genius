# Problem: erdos-1126-oq-01

## Title
Extending de Bruijn-Jurkat to Other Functional Equations

## Statement

Can the de Bruijn-Jurkat theorem (almost additive → additive a.e.) be extended to
multiplicative, Jensen, and derivation functional equations?

**de Bruijn-Jurkat theorem**: If f: ℝ → ℝ satisfies f(x+y) = f(x) + f(y) for
almost all pairs (x,y), then there exists an additive function g: ℝ → ℝ with f = g a.e.

**Extension questions**:
1. **Almost multiplicative** → multiplicative a.e.?
2. **Almost Jensen** → Jensen a.e.?
3. **Almost derivation** → derivation a.e.?
4. **Measurable regularity**: Are measurable multiplicative functions exactly x^c?
   Are measurable derivations exactly zero?

## Classification

```yaml
tier: B
significance: 6
tractability: 6
tags:
  - erdos
  - functional-equations
  - stability
  - functional-analysis
  - measure-theory
```

## Gallery Status

**File**: `proofs/Proofs/Erdos1126OQ01Problem.lean` (472 lines, 5 axioms, 0 sorries)

### Current Axioms (5)

1. `almost_multiplicative_stability` (line 344):
   Almost multiplicative → ∃ multiplicative g with f = g a.e.
   **Approach**: Reduce via log/exp conjugation to almost additive case

2. `almost_jensen_stability` (line 354):
   Almost Jensen → ∃ Jensen g with f = g a.e.
   **Approach**: Shift f by constant to get almost additive, apply de Bruijn-Jurkat

3. `almost_derivation_stability` (line 419):
   Almost derivation → ∃ true derivation δ with d = δ a.e.
   **Reference**: Ger (1979)

4. `measurable_multiplicative_is_power` (line 454):
   Multiplicative + measurable → f(x) = x^c for x > 0
   **Approach**: Log-linearize, apply measurable additive → linear

5. `measurable_derivation_is_zero` (line 462):
   Derivation + measurable → d = 0
   **Approach**: Measurable additive functions are linear; derivations on ℝ are 0

## Research Goal

**Primary**: Prove `measurable_multiplicative_is_power` and `measurable_derivation_is_zero`
using Mathlib's MeasureTheory infrastructure.

**Secondary**: Establish the reduction chain:
- Almost multiplicative → (via log) almost additive → additive a.e. → multiplicative
- Almost Jensen → (via substitution) almost additive → additive a.e. → Jensen

## Related Results in Mathlib

- `MeasureTheory.AEMeasurable` — almost everywhere measurability
- Cauchy's functional equation: measurable additive → linear is classical
- `ContinuousLinearMap` — continuous linear maps (covers continuous derivations)
- Real.log, Real.exp — for log/exp conjugation

## Key References

- de Bruijn (1948), Jurkat (1965) — original stability theorem
- Ger (1979) — derivation stability
- Járai (2005) — extensions to locally compact groups
