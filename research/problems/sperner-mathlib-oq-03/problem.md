# Problem: Tucker's Lemma via Sperner Door-Counting

**Slug**: sperner-mathlib-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Antipodally-symmetric triangulation } T \text{ of } B^n \text{ with labeling } \lambda:V(T)\to\{\pm1,\dots,\pm n\},\ \lambda(-v)=-\lambda(v) \text{ on } \partial B^n \Rightarrow \exists \text{ edge } \{u,v\}\in T,\ \lambda(u)=-\lambda(v).
$$

### Plain Language

Sperner's lemma counts panchromatic simplices by a parity (door-counting) argument. Tucker's lemma is its antipodal cousin: whenever you label the vertices of an antipodally-symmetric triangulation of a ball with signed colors that respect the antipodal symmetry on the boundary, some edge must join a color to its exact negative (a "complementary edge"). We want to derive Tucker's lemma inside this gallery entry using the *same* abstract cell-complex door-counting engine the entry already uses to prove Sperner's lemma, rather than importing a separate combinatorial framework.

### Why This Matters

Tucker's lemma is the combinatorial heart of the Borsuk–Ulam theorem, exactly as Sperner's lemma is the combinatorial heart of Brouwer's fixed-point theorem. Deriving both from one shared parity abstraction shows the `sperner-mathlib` cell-complex machinery is a genuine reusable engine, and opens a formal path to Borsuk–Ulam and its corollaries (ham-sandwich, necklace-splitting, Lusternik–Schnirelmann).

## Known Results

### What's Already Proven

- `sperner-mathlib` (VERIFIED, 0 axioms): abstract `CellComplex` door-counting — `door_count_parity`, `even_card_interior_doors`, `per_cell_door_parity`, `sperner_parity`, `exists_panchromatic`.
- Sperner's lemma via `boundary_doors_odd_of_last_face` — the template argument to mirror.
- Classical Tucker's lemma (Tucker 1945; Freund–Todd constructive proof 1981) — the target, not yet in Mathlib.

### What's Still Open

- Tucker's lemma is not formalized in Mathlib.
- No Lean derivation of Tucker from a Sperner-style door-counting abstraction exists.

### Our Goal

Prove a Tucker-style statement for the abstract `CellComplex`/door framework in `SpernerMathlib.lean`, reusing `door_count_parity` and the interior/boundary door lemmas. Target the 1-D (interval) and 2-D cases first as concrete instances, then the general antipodally-symmetric labeling. Even the low-dimensional cases, derived cleanly as corollaries of the existing engine, are a valuable self-contained result.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sperner-mathlib | Provides the door-counting parity engine to reuse | abstract CellComplex, double counting, parity |
| sperner-simplicial-instance | Concrete simplicial triangulation instances | Triangulation, barycentric subdivision |
| sperner-ndim | n-dimensional Sperner colorings | induction on dimension |

## Initial Thoughts

### Potential Approaches

1. **Reuse door-counting parity directly**: Model the signed labeling as a `CellComplex` coloring in which a "door" is a face carrying a complementary pair, then invoke `door_count_parity` so that an odd boundary count forces an interior complementary edge. Antipodal symmetry on the boundary supplies the odd boundary parity (Sperner uses the last-face count; Tucker uses the antipodal involution).
   - Why it might work: the parity skeleton is identical; only the "which faces are doors" predicate changes.
   - Risk: encoding the antipodal boundary condition abstractly may require new boundary lemmas.

2. **Low-dimensional first (interval / triangle)**: prove Tucker for n = 1 then n = 2 as concrete instances, mirroring how Sperner is instantiated, before the general statement.
   - Why it might work: keeps boundary parity concrete and finite.
   - Risk: the general antipodal induction is the genuinely new content.

### Key Difficulties

- Encoding antipodal symmetry of the boundary triangulation abstractly (the `CellComplex` has no antipodal involution yet).
- Establishing boundary door-count parity from the antipodal condition (analogue of `boundary_doors_odd_of_last_face`).

### What Would a Proof Need?

- Key lemma 1: an antipodal-boundary analogue of `boundary_doors_odd_of_last_face` giving an odd count of boundary complementary-pair faces.
- Key lemma 2: reuse of `door_count_parity` / `even_card_interior_doors` to turn odd boundary parity into an interior complementary edge.
- Technical requirements: a decidable "complementary pair" predicate on faces; an involution on boundary cells.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The reusable parity engine already exists and is verified (0 axioms); no analytic infrastructure needed.
- Novel content is confined to the boundary-parity lemma under an antipodal involution.
- Low-dimensional instances are finite and checkable — a clear incremental first target.

**Estimated Effort**:
- Exploration: 1-2 days
- If tractable: days to weeks (interval and 2-D cases, then general)
- If hard: the general antipodal induction may remain partial

## References

### Papers
- A. W. Tucker, "Some topological properties of disk and sphere," 1945 — original statement.
- R. Freund, M. Todd, "A constructive proof of Tucker's combinatorial lemma," JCTA 1981 — constructive proof.

### Online Resources
- Matoušek, *Using the Borsuk–Ulam Theorem* — Tucker's lemma and its corollaries.

### Mathlib
- No Tucker's lemma; the entry's own `CellComplex` abstraction plus `Mathlib.Combinatorics.*` provide the substrate.

## Metadata

```yaml
tags:
  - combinatorics
  - topology
  - sperner
  - tucker-lemma
  - borsuk-ulam
related_proofs:
  - sperner-mathlib
  - sperner-simplicial-instance
  - sperner-ndim
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 6/10
