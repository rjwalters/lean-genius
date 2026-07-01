# Problem: Bolzano — Every Odd-Degree Real Polynomial Has a Real Root

**Slug**: intermediate-value-theorem-oq-04
**Created**: 2026-07-01
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: intermediate-value-theorem

## Problem Statement

### Formal Statement

$$
p \in \mathbb{R}[X],\ \deg p \text{ odd} \implies \exists x \in \mathbb{R},\ p(x) = 0.
$$

### Plain Language

The parent `intermediate-value-theorem` proves the IVT for continuous real functions. Its
most famous corollary is **Bolzano's theorem**: every real polynomial of *odd* degree has a
real root. The reason is that an odd-degree polynomial takes arbitrarily large positive and
arbitrarily large negative values (its two "ends" point opposite ways), so it must cross
zero. This child formalizes that corollary end-to-end.

### Why This Matters

This is the canonical application of the IVT to algebra and the elementary reason `ℝ` is not
algebraically closed only "by one dimension" (odd-degree polynomials always factor off a real
root). Mathlib has the IVT (`intermediate_value_Icc`), polynomial continuity, and the precise
end-behavior lemmas (`tendsto_atTop_of_leadingCoeff_nonneg`,
`tendsto_atBot_of_leadingCoeff_nonpos`), but there is **no named lemma** assembling them into
"odd degree ⟹ real root." The proof is a clean, instructive assembly.

## Known Results

### What's Already Proven

- Parent `intermediate-value-theorem` is verified (0-axiom).
- Mathlib: `intermediate_value_Icc (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b)) :
  Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b`;
  `Polynomial.continuous`;
  `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg (hdeg : 0 < P.degree) (0 ≤ leadingCoeff)`;
  `Polynomial.tendsto_atBot_of_leadingCoeff_nonpos (hdeg : 0 < P.degree) (leadingCoeff ≤ 0)`.

### What's Still Open

- The target theorem below (currently `sorry`). No Mathlib lemma states "odd real degree ⟹
  a real root exists."

### Our Goal

Prove the sketch below as a self-contained verified (0-axiom) child. Category:
**application / corollary of IVT**.

## Target Lean Sketch

```lean
open Polynomial Filter Topology

/-- Bolzano: an odd-degree real polynomial has a real root. -/
theorem exists_root_of_odd_natDegree (p : ℝ[X]) (hodd : Odd p.natDegree) :
    ∃ x : ℝ, p.eval x = 0 := by
  sorry
  -- WLOG `0 < p.leadingCoeff` (else replace p by -p; roots are the same).
  -- `0 < p.degree` since odd natDegree ⟹ natDegree ≥ 1.
  -- As x → +∞, `eval x p → +∞` (tendsto_atTop_of_leadingCoeff_nonneg) ⟹ pick b with p b > 0.
  -- As x → -∞, `eval x p → -∞` (odd degree flips the sign; tendsto_atBot_of_leadingCoeff_nonpos
  --   applied to `p.comp (-X)`, whose leadingCoeff is `-p.leadingCoeff`) ⟹ pick a < b with p a < 0.
  -- `Polynomial.continuous p` is continuous on [a,b]; `intermediate_value_Icc` puts 0 ∈ image,
  --   giving `∃ x ∈ Icc a b, p.eval x = 0`.
```

Add worked `example`s: `p = X^3 - X` (roots `-1,0,1`); `p = X^3 + X + 1` (one real root, no
rational one); confirm an *even*-degree counterexample to the hypothesis (`X^2 + 1` has no
real root) to motivate the odd-degree condition.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `intermediate-value-theorem` | Parent: IVT | continuity, connectedness |
| `fundamental-theorem-algebra` | Complex roots exist for all degrees | complex analysis |
| `solution-of-cubic` | Real cubics always have a real root | Cardano, algebra |

## Tractability Assessment

**Difficulty**: Medium

**Significance**: 7/10  |  **Tractability**: 7/10  |  **Tier**: B

**Justification**: All ingredients are in Mathlib; the work is the bookkeeping of (i) the
sign-normalization WLOG, (ii) extracting a positive and a negative value from the two
end-behavior `Tendsto` facts (`Filter.eventually` + `Filter.Eventually.exists`), and (iii)
one `intermediate_value_Icc` application. The `p.comp (-X)` leading-coefficient computation
for the `atBot` end is the main fiddly step.

### Suggested First Steps

1. Reduce to `0 < p.leadingCoeff` and note `0 < p.degree` from `Odd p.natDegree`.
2. From `tendsto_atTop_of_leadingCoeff_nonneg`, extract `b` with `0 < p.eval b`; from the
   `atBot` end (odd-degree sign flip), extract `a < b` with `p.eval a < 0`.
3. Apply `intermediate_value_Icc` (with `Polynomial.continuous`) to land `0` in the image.

## References

### Mathlib

- `intermediate_value_Icc` — Topology/Order/IntermediateValue.lean
- `Polynomial.continuous` — Topology/Algebra/Polynomial.lean
- `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`,
  `Polynomial.tendsto_atBot_of_leadingCoeff_nonpos` — Analysis/Polynomial/Basic.lean

### Literature

- Bolzano (1817); the odd-degree real-root theorem is the standard first corollary of the
  intermediate value theorem in every analysis text.

## Metadata

```yaml
tags:
  - real-analysis
  - intermediate-value-theorem
  - polynomials
  - bolzano
related_proofs:
  - intermediate-value-theorem
  - fundamental-theorem-algebra
  - solution-of-cubic
difficulty: medium
source: proof-suggestion
created: 2026-07-01
```
