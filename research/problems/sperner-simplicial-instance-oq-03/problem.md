# Problem: Boundary Door Parity for the Standard n-Simplex Triangulation

**Slug**: sperner-simplicial-instance-oq-03
**Created**: 2026-06-14
**Status**: Active (OBSERVE)
**Source**: gallery-gap (parent: `sperner-simplicial-instance`)

## Problem Statement

### Formal Statement

The parent proof bridges an abstract cell-complex door-counting argument to a concrete simplicial
complex, but leaves `boundary_doors_odd` — the statement that the standard $n$-simplex triangulation
has an **odd** number of fully-labelled boundary "doors" — as an assumption to be proved from first
principles. Concretely:

> For a Sperner labelling of the barycentric (or standard) triangulation of $\Delta^n$, the number
> of $(n-1)$-faces on the boundary that carry the full label set $\{0,1,\dots,n-1\}$ is **odd**.

This is the inductive engine of Sperner's lemma: boundary doors odd $\Rightarrow$ an interior fully
labelled cell exists. The goal is to prove it from the geometry/combinatorics of the standard
triangulation and its barycentric subdivision, rather than assuming it.

### Plain Language

Sperner's lemma is proved by induction on dimension: you show the *boundary* of a triangulated
simplex has an odd number of properly-labelled little faces ("doors"), and oddness propagates
inward to force a rainbow cell. The parent formalization assumed this boundary-oddness for the
standard simplex; this problem asks to actually prove it from how the standard simplex is
subdivided.

### Why This Matters

`boundary_doors_odd` is the one remaining first-principles gap in the simplicial instantiation of
Sperner's lemma. Closing it makes the gallery's concrete Sperner proof fully self-contained
(no assumed combinatorial facts) and supplies a reusable lemma about boundary face counts in
standard triangulations — useful for the Tucker/Borsuk–Ulam extensions and for KKM-type results.

## Known Results

### What's Already Proven

- `sperner-simplicial-instance` — the simplicial⇄cell-complex bridge (parent), with `boundary_doors_odd` assumed.
- `sperner-mathlib4` / `sperner-simplicial-bridge` — the abstract door-counting parity and bridging lemmas.
- Mathlib: `SimplicialComplex`, `Finset.card` parity, induction over faces, standard-simplex (`stdSimplex`) API.

### What's Still Open (in this gallery)

- A first-principles proof of `boundary_doors_odd` for the standard $n$-simplex triangulation.
- The induction tying boundary parity in dimension $n-1$ to interior cells in dimension $n$.

### Our Goal

Prove `boundary_doors_odd` by induction on $n$: the base case $n=1$ (an interval: endpoints labelled
$0$ and $1$ give exactly one door) and the inductive step relating the boundary faces of $\Delta^n$
to copies of $\Delta^{n-1}$, using `Finset.card` parity. Discharge the assumption in the parent file.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sperner-simplicial-instance | Direct parent; defines the assumed lemma | simplicial complexes, doors |
| sperner-mathlib4 | Abstract door-counting parity engine | parity, chains |
| sperner-simplicial-bridge | Simplicial ⇄ cell-complex translation | barycentric subdivision |

## Initial Thoughts

### Potential Approaches

1. **Induction on dimension (recommended)**: base case interval; inductive step counts fully-labelled
   $(n-1)$-faces on $\partial\Delta^n$, of which only the face omitting label $n-1$ contributes, and
   apply the dimension-$(n-1)$ oddness there.
   - Why it might work: this is Sperner's original induction; every step is a finite parity count.
   - Risk: correctly identifying which boundary faces can be fully labelled (only one facet) and handling the subdivision indexing.

2. **Direct parity via degree counting**: build the door-adjacency graph and use handshake/parity.
   - Why it might work: mirrors the abstract proof concretely.
   - Risk: constructing the adjacency structure for the standard triangulation is more setup.

### Key Difficulties

- Indexing the faces of the standard/barycentric triangulation and proving only the right facet hosts full-labelled doors.
- Keeping the induction hypothesis aligned across the dimension drop.

### What Would a Proof Need?

- Key lemma 1: on $\partial\Delta^n$, full-labelled $(n-1)$-faces lie only on the facet omitting the top vertex.
- Key lemma 2: parity transfer — oddness of doors in dimension $n-1$ ⇒ oddness on the boundary of $\Delta^n$.
- Technical requirements: `SimplicialComplex`, `stdSimplex`, `Finset.card` mod 2, induction.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- It is the classical Sperner induction, finite and combinatorial, with the abstract parity engine already in the gallery.
- The work is precise face-indexing and a clean induction — substantial but bounded, with no external theory.
- Closing one named assumption is a concrete, verifiable deliverable.

**Estimated Effort**:
- Exploration: days
- If tractable: 1–3 weeks
- If hard: 1 month (if triangulation indexing proves stubborn)

## References

### Papers
- Sperner (1928), "Neuer Beweis für die Invarianz der Dimensionszahl".
- Matoušek, *Using the Borsuk–Ulam Theorem* — Sperner's lemma and its induction.

### Online Resources
- Parent gallery entry `sperner-simplicial-instance`.

### Mathlib
- `Mathlib.Combinatorics.SimplicialComplex` and `Mathlib.Analysis.Convex.SimplicialComplex`.
- `Mathlib.Data.Finset.Card` — parity counting.

## Metadata

```yaml
tags:
  - combinatorics
  - topology
  - sperner-lemma
  - simplicial-complexes
related_proofs:
  - sperner-simplicial-instance
  - sperner-mathlib4
  - sperner-simplicial-bridge
difficulty: medium
source: proof-suggestion
created: 2026-06-14
```
