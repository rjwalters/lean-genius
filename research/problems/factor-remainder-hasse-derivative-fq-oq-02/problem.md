# Problem: The Global Kernel of the Ordinary-Derivative Test: derivative f = 0 ⇔ Frobenius expansion ⇔ p-th power over 𝔽_q

**Slug**: factor-remainder-hasse-derivative-fq-oq-02
**Created**: 2026-06-30
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: factor-remainder-hasse-derivative-fq

## Problem Statement

### Formal Statement

$$
\text{over }F,\ \mathrm{char}\,F=p:\quad D f = 0 \iff \exists g,\, f = \mathrm{expand}_p g;\qquad \text{over perfect }F:\quad D f = 0 \iff \exists h,\, f = h^p
$$

### Plain Language

The parent shows the ordinary iterated-derivative test goes blind at order p; the sibling oq-01 quantifies the pointwise multiplicity gap. Which polynomials are globally invisible — killed by the first ordinary derivative? Over a characteristic-p field these are exactly the Frobenius expansions f = g(X^p), and over any perfect field (every 𝔽_q) exactly the p-th powers f = h^p. This pins down the ordinary derivative's kernel structurally, tying the parent's blindness to inseparability.

### Why This Matters

The classical inseparability ⇔ p-th-power criterion, freshly framed as the exact global kernel of the parent's ordinary-derivative test — blind at all orders ≥1 simultaneously — complementing the parent (pointwise multiplicity threshold) and oq-01 (overcounting gap).

## Known Results

### What's Already Proven

- Parent entry `factor-remainder-hasse-derivative-fq` is verified (0-axiom) in the gallery and supplies the base result this question extends.
- All Mathlib lemmas listed under References below were grep-confirmed to exist in the pinned Mathlib.

### What's Still Open

- The specific target theorems sketched below (currently `sorry`).

### Our Goal

Prove the target sketch below as a self-contained, verified (0-axiom) child of `factor-remainder-hasse-derivative-fq`. Category: **extension**.

## Target Lean Sketch

```lean
variable {F : Type*} [Field F] {p : ℕ} [Fact p.Prime] [CharP F p]

theorem derivative_eq_zero_iff_expand (f : F[X]) :
    Polynomial.derivative f = 0 ↔ ∃ g : F[X], f = Polynomial.expand F p g := by sorry

theorem derivative_eq_zero_iff_pow (f : F[X]) [PerfectRing F p] :
    Polynomial.derivative f = 0 ↔ ∃ h : F[X], f = h ^ p := by sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `factor-remainder-hasse-derivative-fq` | Parent: Hasse derivative factor/remainder over 𝔽_q | Hasse derivative, Taylor expansion |
| `factor-remainder-hasse-derivative-fq-oq-01` | Sibling: pointwise multiplicity overcounting gap | rootMultiplicity |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 7/10  |  **Tractability**: 8/10  |  **Tier**: B

**Justification**: The required Mathlib primitives exist and the proof mirrors the parent's style; the sketch reduces to assembling named lemmas.

### Suggested First Steps

1. derivative_eq_zero_iff_expand ⇐: rw derivative_expand, then (p:F)=0 via CharP.cast_eq_zero → mul_zero. ⇒: exact ⟨contract p f, (expand_contract p hf ‹p≠0›).symm⟩.
2. Corollary ⇒: from f = expand p g, use surjective_frobenius + Polynomial.map_surjective to get h with map (frobenius F p) h = g; then f = expand p (map frob h) = map frob (expand p h) = h^p via map_expand + expand_char.
3. Add concrete witnesses: X^p (blind, = expand p X) and a separable X − C a (not blind).

## References

### Mathlib

- `Polynomial.derivative_expand` — Algebra/Polynomial/Expand.lean (derivative (expand R p f) = expand R p (derivative f) * (p * X^(p-1)); the (p:F)=0 factor kills the ⇐ direction)
- `Polynomial.expand_contract` + `Polynomial.contract` — Expand.lean ([CharP R p][NoZeroDivisors R]) give ⇒ with g := contract p f
- `Polynomial.map_expand`, `Polynomial.expand_char` — Expand.lean (map (frobenius R p)(expand R p f) = f^p) assemble the p-th-power corollary
- `surjective_frobenius`; `PerfectRing.ofFiniteOfIsReduced` / `PerfectField.ofFinite` — FieldTheory/Perfect.lean (perfect-field instances for 𝔽_q)

## Metadata

```yaml
tags:
  - algebra
  - polynomials
  - hasse-derivative
  - positive-characteristic
  - finite-fields
  - frobenius
  - separability
related_proofs:
  - factor-remainder-hasse-derivative-fq
  - factor-remainder-hasse-derivative-fq-oq-01
difficulty: low
source: proof-suggestion
created: 2026-06-30
```
