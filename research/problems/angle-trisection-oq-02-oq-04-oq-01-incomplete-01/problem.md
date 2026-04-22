# Problem: Complete Tower-Galois Equivalence via Mathlib Correspondence

**Slug**: angle-trisection-oq-02-oq-04-oq-01-incomplete-01
**Created**: 2026-04-22
**Status**: Available
**Source**: incomplete-lean (3 sorries in AngleTrisectionOQ02OQ04OQ01.lean)

## Problem Statement

### Plain Language

The file `proofs/Proofs/AngleTrisectionOQ02OQ04OQ01.lean` formalizes the Tower-Galois
equivalence for constructible real numbers:

> For an algebraic real α: α lies in a quadratic tower ⟺ Gal(minpoly ℚ α) is a 2-group

Three `sorry`s remain. The task is to prove them using Mathlib's existing infrastructure.

### The Three Remaining Sorries

**Sorry 1 (line 193)** — `galois_two_group_implies_tower` (hardest):
```lean
theorem galois_two_group_implies_tower (α : ℝ) (hα : IsIntegral ℚ α)
    (hG : IsPGroup 2 (minpoly ℚ α).Gal) :
    ConstructibleViaTower α := by
  sorry -- Requires: splitting field construction, Galois correspondence,
        -- iterative index-2 subgroup extraction, embedding α into tower
```
Proof sketch: G = Gal(E/ℚ) is a 2-group → has index-2 subgroup H → Galois correspondence
gives K₁ with [K₁:ℚ] = 2 → repeat inductively on |H|.

**Sorry 2 (line 216)** — `tower_implies_galois_two_group` (medium):
```lean
theorem tower_implies_galois_two_group (α : ℝ) (hα : IsIntegral ℚ α)
    (ht : ConstructibleViaTower α) :
    IsPGroup 2 (minpoly ℚ α).Gal := by
  sorry -- Requires: degree of splitting field divides tower degree power
```
Proof sketch: α ∈ quadratic tower K with [K:ℚ] = 2^n → deg(minpoly α) | 2^n →
[E:ℚ] is a power of 2 → |Gal(E/ℚ)| is a power of 2.

**Sorry 3 (line 291)** — `sqrt2_constructible_tower` (easiest):
```lean
theorem sqrt2_constructible_tower :
    ∃ (K : IntermediateField ℚ ℝ),
      QuadraticTower ℚ ℝ K 1 ∧ (Real.sqrt 2 : ℝ) ∈ K := by
  sorry -- Needs: construction of ℚ(√2) as IntermediateField with degree 2
```

## Classification

```yaml
tier: B
significance: 7
tractability: 5
tags:
  - seeker-selected
  - algebra
  - galois-theory
  - tower-law
  - angle-trisection
  - incomplete
```

**Significance**: 7/10 — Completes the central theorem in the angle trisection proof chain
**Tractability**: 5/10 — API glue work, ~500-800 lines estimated; no missing theorems

## Mathlib Gap Analysis (from Lean file)

### Available
- `IsPGroup.isSolvable` — 2-groups are solvable
- `IsPGroup.to_subgroup` — subgroups of 2-groups are 2-groups
- `IsPGroup.iff_card` — card of p-group is p^n
- `IntermediateField`, `Polynomial.Gal`, `IsGalois`
- `IntermediateField.fixedField` / `fixingSubgroup` (Galois correspondence)
- `exists_index_two_subgroup` for 2-groups — PROVED in the file

### Missing / Needs Glue
- Connecting `Polynomial.Gal` to `IntermediateField.fixingSubgroup`
- Index-degree relation: `[G : H] = [Fix(H) : K]` (API connection to `Module.finrank`)
- Iterative tower construction from repeated index-2 extraction (induction on |G|)

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| angle-trisection | Parent proof using QuadraticTower constructibility |
| angle-trisection-oq-02-oq-04 | Defines DegreeCriterion, GaloisCriterion, TowerCriterion |
| angle-trisection-oq-02-oq-04-oq-01 | Direct parent — partial formalization |
| angle-trisection-oq-02 | Constructible algebraic numbers via Galois groups |
