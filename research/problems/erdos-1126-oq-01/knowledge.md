# Knowledge Base: erdos-1126-oq-01

Extending de Bruijn-Jurkat Stability to Multiplicative, Jensen, and Derivation Equations.

---

## Problem Understanding

**Core question**: The de Bruijn-Jurkat theorem says almost-additive ⟹ additive a.e.
Can this be extended to:
1. Almost-multiplicative ⟹ multiplicative a.e. (reduce via log/exp)
2. Almost-Jensen ⟹ Jensen a.e. (reduce via linear substitution)
3. Almost-derivation ⟹ derivation a.e. (Ger 1979)
4. Measurable multiplicative ⟹ x^c (regularity)
5. Measurable derivation ⟹ 0 (regularity)

**Gallery proof** at `proofs/Proofs/Erdos1126OQ01Problem.lean` (472 lines, 5 axioms, 0 sorries).

---

## Current Axiom Status

### Axiom 1: `almost_multiplicative_stability` (line 344)
- **Claim**: IsAlmostMultiplicative f → ∃ multiplicative g, ae_eq f g
- **Strategy**: For f > 0 a.e., take log to get almost additive h = log ∘ f, apply de Bruijn-Jurkat to get additive g₀, set g = exp ∘ g₀. Sign changes require additional case analysis.
- **Tractability**: MEDIUM — the positive case is clean, sign changes complex

### Axiom 2: `almost_jensen_stability` (line 354)
- **Claim**: IsAlmostJensen f → ∃ Jensen g, ae_eq f g
- **Strategy**: Jensen condition f((x+y)/2) = (f(x)+f(y))/2 is equivalent to h(x+y) = h(x)+h(y) where h(x) = f(2x). So almost-Jensen → almost-additive via substitution x ↦ 2x.
- **Tractability**: HIGH — reduction to additive case is elementary

### Axiom 3: `almost_derivation_stability` (line 419)
- **Claim**: IsAlmostDerivation d → ∃ derivation δ, ae_eq d δ
- **Reference**: Ger (1979) — based on groupoid extension methods
- **Tractability**: LOW — requires non-trivial extension theory

### Axiom 4: `measurable_multiplicative_is_power` (line 454)
- **Claim**: IsMultiplicative f → Measurable f → ∃ c, ∀ x > 0, f(x) = x^c
- **Strategy**: On (0,∞), log∘f∘exp is a measurable additive function ℝ→ℝ, hence f∘exp = exp(c·id) = id^c
- **Tractability**: MEDIUM — log/exp conjugation + measurable additive ⟹ linear

### Axiom 5: `measurable_derivation_is_zero` (line 462)
- **Claim**: IsDerivation d → Measurable d → d = 0
- **Strategy**: d(1) = 0 (proved in file). d(x) = x·d(1) for rationals (Leibniz rule iteration). Extension to ℝ by measurability ⟹ Cauchy equation ⟹ linear ⟹ d(x) = cx, but then Leibniz forces c=0.
- **Tractability**: MEDIUM — requires measurable additive functions are linear

---

## Best Research Targets

**Priority 1**: `almost_jensen_stability` — highest tractability, elementary reduction
**Priority 2**: `measurable_derivation_is_zero` — clean argument via Leibniz + Cauchy
**Priority 3**: `measurable_multiplicative_is_power` — log conjugation to linear case

---

## Key Mathlib APIs

- `MeasureTheory.AEMeasurable` — measure theory infrastructure
- `Real.log_mul`, `Real.exp_add` — for log/exp conjugation
- Cauchy equation on ℝ: measurable additive ⟹ ∃ c, f = c * id (may need manual proof)
- `MeasureTheory.Measure.ae` — almost everywhere filter

---

## Insights

- The file uses `ae_pairs` for "almost everywhere on pairs" — custom definition in the file
- `IsAlmostAdditive`, `IsAlmostMultiplicative` etc. use this `ae_pairs` wrapper
- The reduction structure is clean: each "almost" equation reduces via substitution to almost-additive

---

## Dead Ends

[None yet — initialized by Seeker 2026-04-05]

