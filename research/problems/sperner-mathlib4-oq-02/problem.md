# Problem: Tucker's Lemma (and Borsuk–Ulam) from Abstract Door-Counting

**Slug**: sperner-mathlib4-oq-02
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `sperner-mathlib4`)

## Problem Statement

### Formal Statement

The parent proof formalizes Sperner's lemma via an **abstract door-counting** (a parity argument:
in a chain of cells, "doors" between full and empty faces have odd count, forcing a fully-labelled
cell). This problem asks whether the same door-counting framework extends to **Tucker's lemma**,
the antipodal analogue of Sperner:

> For any antipodally symmetric triangulation of the $n$-ball $B^n$ and any labelling
> $\lambda:\text{vertices}\to\{\pm1,\dots,\pm n\}$ that is antipodal on the boundary
> ($\lambda(-v)=-\lambda(v)$ for $v\in\partial B^n$), some edge is **complementary**:
> $\lambda(u)=-\lambda(v)$.

Tucker's lemma is the combinatorial heart of the **Borsuk–Ulam theorem**, which would then follow
from the same parity machinery.

### Plain Language

Sperner's lemma is proved by counting "doors" and using a parity (odd/even) argument to force a
rainbow cell. Tucker's lemma is the "antipodal" cousin: with a sign-symmetric labelling you are
forced to have two adjacent vertices with exactly opposite labels. The question is whether the
gallery's abstract door-counting lemma is general enough to also yield Tucker — and hence
Borsuk–Ulam — without reinventing the parity argument.

### Why This Matters

Borsuk–Ulam is a cornerstone of combinatorial topology with countless applications (ham-sandwich,
Lovász's chromatic bound, fair division). The gallery already has Borsuk–Ulam entries, but deriving
Tucker's lemma from a *shared abstract parity framework* would unify Sperner-type and antipodal
results under one combinatorial engine — a genuinely illuminating formalization, not just another
proof.

## Known Results

### What's Already Proven

- `sperner-mathlib4` — abstract door-counting proof of Sperner's lemma (parent).
- Gallery: `borsuk-ulam-*` entries (the target theorem, via other routes).
- Mathlib: `SimplicialComplex`, `Finset` parity (`Finset.card` mod 2), graph degree-parity lemmas.

### What's Still Open (in this gallery)

- Tucker's lemma derived from the abstract door-counting framework.
- The Tucker ⇒ Borsuk–Ulam reduction in Lean (continuous antipodal map ⇒ complementary edge via fine triangulations + compactness).

### Our Goal

Generalize the parent's door-counting lemma to the antipodal setting and prove Tucker's lemma; then
sketch/formalize the standard Tucker ⇒ Borsuk–Ulam limit argument. First milestone: Tucker's lemma
for a fixed antipodally symmetric triangulation.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sperner-mathlib4 | Direct parent; the abstract door-counting engine | parity, doors, chains |
| sperner-simplicial-instance | Concrete simplex triangulations and boundary parity | barycentric subdivision |
| borsuk-ulam-* | The theorem Tucker implies | antipodal maps, topology |

## Initial Thoughts

### Potential Approaches

1. **Antipodal door-counting (recommended)**: re-derive the parity lemma with a $\mathbb{Z}/2$
   antipodal symmetry acting on cells, so the boundary contributes an *even* count and an interior
   complementary edge is forced.
   - Why it might work: reuses the exact parity infrastructure of the parent; Tucker is the canonical antipodal analogue.
   - Risk: the antipodal boundary condition and the $\pm$ label set require a careful redefinition of "door".

2. **Tucker via Sperner on a quotient**: reduce Tucker to a Sperner-type statement on the antipodal quotient $\mathbb{RP}^n$ region.
   - Why it might work: leverages the parent theorem directly.
   - Risk: the quotient/orientation bookkeeping can be subtle.

### Key Difficulties

- Encoding the antipodal symmetry of the triangulation and the $\lambda(-v)=-\lambda(v)$ boundary condition combinatorially.
- The continuous Tucker ⇒ Borsuk–Ulam step (mesh → 0, compactness) is a separate analytic argument.

### What Would a Proof Need?

- Key lemma 1: an antipodal version of the door-counting parity lemma.
- Key lemma 2: complementary-edge existence (Tucker) from that parity count.
- Technical requirements: `SimplicialComplex`, `Finset.card` parity, $\mathbb{Z}/2$ group action on cells.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The combinatorial Tucker step reuses an existing parity engine — plausibly tractable.
- The Borsuk–Ulam reduction adds analysis (limits/compactness) that is a separate, heavier phase.
- Tucker's lemma alone is a clean, well-scoped first deliverable.

**Estimated Effort**:
- Exploration: days–weeks
- If tractable (Tucker only): 2–4 weeks
- If hard (through Borsuk–Ulam): 1–2 months

## References

### Papers
- Tucker (1946), "Some topological properties of disk and sphere".
- Matoušek, *Using the Borsuk–Ulam Theorem* (2003) — Tucker's lemma and combinatorial Borsuk–Ulam.

### Online Resources
- Parent gallery entry `sperner-mathlib4`.

### Mathlib
- `Mathlib.Combinatorics.SimplicialComplex` and `Finset` parity lemmas.
- `Mathlib.GroupTheory.GroupAction` — antipodal $\mathbb{Z}/2$ action.

## Metadata

```yaml
tags:
  - combinatorics
  - topology
  - tucker-lemma
  - borsuk-ulam
related_proofs:
  - sperner-mathlib4
  - sperner-simplicial-instance
difficulty: high
source: proof-suggestion
created: 2026-06-14
```
