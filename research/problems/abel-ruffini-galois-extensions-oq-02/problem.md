# Problem: Galois Correspondence Theorem (Subfields ↔ Subgroups)

**Slug**: abel-ruffini-galois-extensions-oq-02
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

For a finite Galois extension $L/K$, the fundamental theorem of Galois theory states there is a bijection:

$$
\{\text{intermediate fields } K \subseteq E \subseteq L\} \longleftrightarrow \{\text{subgroups } H \leq \text{Gal}(L/K)\}
$$

given by $E \mapsto \text{Gal}(L/E)$ and $H \mapsto L^H$ (fixed field). Moreover:
- $[L:E] = |H|$ and $[E:K] = [\text{Gal}(L/K) : H]$
- $E/K$ is Galois iff $H \trianglelefteq \text{Gal}(L/K)$, in which case $\text{Gal}(E/K) \cong \text{Gal}(L/K)/H$

**Goal**: Formalize this correspondence in Lean 4 in the context of the `abel-ruffini-galois-extensions` gallery proof, using Mathlib's existing `IsGalois` and `IntermediateField` infrastructure.

### Plain Language

The fundamental theorem of Galois theory gives a complete "dictionary" between subfields of a Galois extension and subgroups of its Galois group. Subfields and subgroups are in perfect bijection, with order reversing the degree of extension. This is the core structural result that powers the Abel-Ruffini proof of quintic unsolvability.

### Why This Matters

1. **Foundation for Abel-Ruffini**: The unsolvability of the quintic rests on this bijection — showing the Galois group is S₅ (unsolvable) requires the full correspondence
2. **Mathlib completeness**: Mathlib has `IsGalois.galoisCorrespondence` but the gallery proof may axiomatize or weaken what's available
3. **Gallery gap**: The `abel-ruffini-galois-extensions` gallery entry explicitly lists this as an open question
4. **Pedagogical value**: A clean formalization would demonstrate the correspondence concisely for education

## Known Results

### What's Already Proven

- `IsGalois` class in Mathlib with `IsGalois.galoisCorrespondence` — the correspondence exists in Mathlib
- `IntermediateField.fixingSubgroup` and `IntermediateField.fixedField` — the two maps are defined
- Gallery proof `abel-ruffini-galois-extensions` — partial formalization of Galois theory for Abel-Ruffini

### What's Still Open

- Whether the gallery proof fully uses `IsGalois.galoisCorrespondence` or axiomatizes it
- Connecting the gallery's specific Galois group computation to the full correspondence
- Proving the normal subgroup ↔ Galois subextension correspondence explicitly

### Our Goal

Determine if the gallery proof can be strengthened to explicitly invoke `IsGalois.galoisCorrespondence`, and formalize the key properties (degree equality, normal subgroup criterion) in the Abel-Ruffini context.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| abel-ruffini-galois-extensions | Parent proof — source of this open question | Galois groups, solvability |
| abel-ruffini | Main Abel-Ruffini theorem — needs Galois correspondence | S₅ unsolvable |

## Initial Thoughts

### Potential Approaches

1. **Direct use of `IsGalois.galoisCorrespondence`**: Apply Mathlib's existing correspondence theorem to the specific extension in the gallery proof
   - Why it might work: Mathlib has this theorem, just need to connect it to the gallery context
   - Risk: Gallery proof may use different API; may need to prove the extension is Galois first

2. **Explicit bijection construction**: Define the maps E ↦ Gal(L/E) and H ↦ L^H explicitly and prove they're inverse
   - Why it might work: More transparent, pedagogically clear
   - Risk: More verbose than using Mathlib's theorem; duplication of existing work

3. **Partial formalization**: Focus only on the degree formula $[L:E] = |H|$ as the key lemma
   - Why it might work: Smaller target, likely sufficient for the Abel-Ruffini application
   - Risk: May not fully answer the open question

### Key Difficulties

- The gallery proof's specific polynomial/extension may need to be verified as Galois explicitly
- `IntermediateField` vs `Subfield` API differences in Mathlib
- Proving the full bijection (both directions of the correspondence) may require careful `simp` lemmas

### What Would a Proof Need?

- Key lemma 1: `galoisCorrespondence_apply` — composition of the two maps is identity
- Key lemma 2: `fixingSubgroup_fixedField` — $H = \text{Gal}(L/L^H)$ for closed $H$
- Technical requirements: Mathlib's `IsGalois`, `IntermediateField`, `Subgroup.index`

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib already has the fundamental theorem (`IsGalois.galoisCorrespondence`)
- Gallery context is concrete (Abel-Ruffini, specific polynomials)
- Main challenge is API navigation and connecting pieces, not mathematical novelty
- Similar: other Galois theory formalizations in gallery took 1-2 weeks

**Estimated Effort**:
- Exploration: 1 day (survey Mathlib Galois API)
- If tractable: 3-5 days (full proof connecting gallery to Mathlib theorem)
- If hard: partial formalization + documented gaps

## References

### Papers
- Emil Artin, "Galois Theory" (1942) — classic exposition
- Lang, "Algebra" Chapter V — standard reference for the correspondence

### Mathlib
- `Mathlib.FieldTheory.Galois.Basic` — `IsGalois` class
- `Mathlib.FieldTheory.IntermediateField` — `IntermediateField`, `fixingSubgroup`, `fixedField`
- `IsGalois.galoisCorrespondence` — the key theorem to leverage

## Metadata

```yaml
tags:
  - galois-theory
  - field-theory
  - group-theory
  - abel-ruffini
  - intermediate-fields
related_proofs:
  - abel-ruffini-galois-extensions
  - abel-ruffini
difficulty: medium
source: gallery-gap
created: 2026-04-05
```
