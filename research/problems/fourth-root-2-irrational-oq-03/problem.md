# Problem: The Galois Closure of ℚ(⁴√2): [ℚ(⁴√2, i) : ℚ] = 8 via the Quadratic Step i ∉ ℝ ⊇ ℚ(⁴√2)

**Slug**: fourth-root-2-irrational-oq-03
**Created**: 2026-06-30
**Status**: Active
**Source**: proof-suggestion <!-- gallery open-question spawned from verified parent -->
**Parent**: fourth-root-2-irrational

## Problem Statement

### Formal Statement

$$
[\mathbb{Q}(\sqrt[4]{2},\, i) : \mathbb{Q}] = 8,\qquad \text{via }\ \mathbb{Q}\subset\mathbb{Q}(\sqrt[4]{2})\subset\mathbb{Q}(\sqrt[4]{2},i),\ 4\cdot 2=8
$$

### Plain Language

The parent's OQ-01 asserts the splitting field of X⁴−2 is ℚ(⁴√2, i), of degree 8 with Galois group D₄. Formalize the degree half: model α = (⁴√2 : ℂ) via Complex.ofReal and prove [ℚ(α, i) : ℚ] = 8 by the tower ℚ ⊂ ℚ(α) ⊂ ℚ(α, i), where [ℚ(α):ℚ]=4 (reusing X⁴−2 irreducible) and [ℚ(α,i):ℚ(α)]=2 because i satisfies X²+1 but i ∉ ℚ(α) (that field is real).

### Why This Matters

Directly answers parent OQ-01's concrete degree claim [ℚ(⁴√2,i):ℚ]=8 and is distinct from oq-02, which stays inside ℝ with real radicals. The full D₄ Galois-group identification is left as the new downstream open question.

## Known Results

### What's Already Proven

- Parent entry `fourth-root-2-irrational` is verified (0-axiom) in the gallery and supplies the base result this question extends.
- All Mathlib lemmas listed under References below were grep-confirmed to exist in the pinned Mathlib.

### What's Still Open

- The specific target theorems sketched below (currently `sorry`).

### Our Goal

Prove the target sketch below as a self-contained, verified (0-axiom) child of `fourth-root-2-irrational`. Category: **extension**.

## Target Lean Sketch

```lean
-- α : ℂ := ((2:ℝ) ^ ((1:ℝ)/4) : ℝ)  -- real fourth root, coerced to ℂ
theorem i_notin_adjoin_fr2 : Complex.I ∉ ℚ⟮α⟯ := by sorry
theorem finrank_adjoin_i_over_fr2 :
    Module.finrank ℚ⟮α⟯ (ℚ⟮α⟯⟮Complex.I⟯) = 2 := by sorry
theorem finrank_galois_closure :
    Module.finrank ℚ ℚ⟮α, Complex.I⟯ = 8 := by sorry
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fourth-root-2-irrational` | Parent: ⁴√2 irrational, X⁴−2 irreducible over ℚ | minimal polynomial, Eisenstein |
| `fourth-root-2-irrational-oq-02` | Sibling: stays inside ℝ with real radicals | real subfield degrees |

## Tractability Assessment

**Difficulty**: Medium

**Significance**: 7/10  |  **Tractability**: 6/10  |  **Tier**: B

**Justification**: The required Mathlib primitives exist and the proof mirrors the parent's style; the sketch reduces to assembling named lemmas.

### Suggested First Steps

1. Show ℚ⟮α⟯ ≤ (real subfield: Complex.ofReal's fieldRange as an IntermediateField ℚ ℂ) via adjoin_le_iff; conclude every z ∈ ℚ⟮α⟯ has z.im = 0, excluding i (I_im = 1).
2. From i ∉ ℚ⟮α⟯ and i²+1=0, get X²+1 irreducible/monic over ℚ⟮α⟯ ⇒ minpoly = X²+1 ⇒ relative finrank 2.
3. Combine [ℚ(α):ℚ]=4 (parent) with Module.finrank_mul_finrank; rewrite via adjoin_adjoin_left to reach 8.

## References

### Mathlib

- `Module.finrank_mul_finrank` — LinearAlgebra/Dimension/Free.lean (tower 4·2=8)
- `IntermediateField.adjoin.finrank` — FieldTheory/IntermediateField/Adjoin/Basic.lean
- `IntermediateField.adjoin_adjoin_left` — Adjoin/Defs.lean (ℚ⟮α⟯⟮i⟯ = ℚ⟮{α,i}⟯)
- `minpoly.eq_of_irreducible_of_monic` — FieldTheory/Minpoly/Field.lean (X²+1 = minpoly i)
- `Complex.I_sq`, `Complex.ofReal_im`, `Complex.I_im` — Data/Complex/Basic.lean; `Subfield.fieldRange`
- Reuse parent `irreducible_X4_sub_2_rat` via import Proofs.FourthRoot2Degree4

## Metadata

```yaml
tags:
  - irrationality
  - field-theory
  - galois-theory
  - splitting-field
  - minimal-polynomial
  - number-theory
  - nth-roots
related_proofs:
  - fourth-root-2-irrational
  - fourth-root-2-irrational-oq-02
difficulty: medium
source: proof-suggestion
created: 2026-06-30
```
