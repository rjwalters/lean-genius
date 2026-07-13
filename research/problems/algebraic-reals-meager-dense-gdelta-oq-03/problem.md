# Problem: Generically Liouville: A Comeagre Refinement Inside the Transcendental Gδ

**Slug**: algebraic-reals-meager-dense-gdelta-oq-03
**Created**: 2026-06-30
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: algebraic-reals-meager-dense-gdelta

## Problem Statement

### Formal Statement

$$
\{x:\mathrm{Liouville}\,x\}\ \text{is a dense }G_\delta \subseteq \{x:\neg\mathrm{IsAlgebraic}_\mathbb{Q}\,x\},\quad \{x:\neg\mathrm{IsAlgebraic}_\mathbb{Q} x \wedge \neg\mathrm{Liouville}\,x\}\ \text{is meagre}
$$

### Plain Language

The parent shows the transcendentals are a dense Gδ (comeagre) in ℝ. Is this the sharpest such witness? No: the Liouville numbers form a strictly smaller dense Gδ contained in the transcendentals. Exhibit {x | Liouville x} as a comeagre subset of {x | ¬IsAlgebraic ℚ x}, and conclude the transcendental-but-not-Liouville reals are meagre — residually every real is not merely transcendental but Liouville.

### Why This Matters

Shows the transcendental dense-Gδ is NOT minimal: a strictly smaller natural comeagre set sits inside. Introduces Liouville numbers / Diophantine approximation and the non-minimality of the comeagre witness — untouched by oq-01 (Fσ dual) and oq-02 (constructive decreasing sequence).

## Known Results

### What's Already Proven

- Parent entry `algebraic-reals-meager-dense-gdelta` is verified (0-axiom) in the gallery and supplies the base result this question extends.
- All Mathlib lemmas listed under References below were grep-confirmed to exist in the pinned Mathlib.

### What's Still Open

- The specific target theorems sketched below (currently `sorry`).

### Our Goal

Prove the target sketch below as a self-contained, verified (0-axiom) child of `algebraic-reals-meager-dense-gdelta`. Category: **extension**.

## Target Lean Sketch

```lean
theorem liouville_comeagre_refines_transcendentals :
    (IsGδ {x : ℝ | Liouville x} ∧ Dense {x : ℝ | Liouville x}) ∧
    {x : ℝ | Liouville x} ⊆ {x : ℝ | ¬ IsAlgebraic ℚ x} ∧
    IsMeagre {x : ℝ | ¬ IsAlgebraic ℚ x ∧ ¬ Liouville x} := by sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `algebraic-reals-meager-dense-gdelta` | Parent: transcendentals are a dense Gδ / algebraics meagre | Baire category, residual sets |
| `algebraic-reals-meager-dense-gdelta-oq-02` | Sibling: constructive decreasing sequence | explicit Gδ construction |

## Tractability Assessment

**Difficulty**: Low

**Significance**: 7/10  |  **Tractability**: 9/10  |  **Tier**: B

**Justification**: The required Mathlib primitives exist and the proof mirrors the parent's style; the sketch reduces to assembling named lemmas.

### Suggested First Steps

1. Gδ+dense clause: exact ⟨IsGδ.setOf_liouville, dense_liouville⟩.
2. Inclusion: intro x hx; Liouville.transcendental gives Transcendental ℤ x; transport to ¬IsAlgebraic ℚ x via IsAlgebraic.transcendental_iff.
3. Meagre clause: {¬alg ∧ ¬Liouville} ⊆ {¬Liouville} = {Liouville}ᶜ, meagre since {Liouville} ∈ residual (eventually_residual_liouville); close with IsMeagre.mono.

## References

### Mathlib

- `IsGδ.setOf_liouville`, `dense_liouville`, `eventually_residual_liouville` — NumberTheory/Transcendental/Liouville/Residual.lean
- `Liouville.transcendental : Transcendental ℤ x` — Liouville/Basic.lean
- `IsAlgebraic.transcendental_iff` — RingTheory/Algebraic/Integral.lean (transfer ℤ ↔ ℚ)
- `IsMeagre`, `IsMeagre.mono` — Topology/GDelta/Basic.lean
- reuse parent `transcendentalReals_dense_isGδ` (import Proofs.AlgebraicRealsMeagerDenseGDelta)

## Metadata

```yaml
tags:
  - topology
  - baire-category
  - real-analysis
  - descriptive-set-theory
  - liouville-numbers
  - transcendental-numbers
  - comeagre-set
  - diophantine-approximation
related_proofs:
  - algebraic-reals-meager-dense-gdelta
  - algebraic-reals-meager-dense-gdelta-oq-02
difficulty: low
source: proof-suggestion
created: 2026-06-30
```
