# Problem: Contribute SpernerTriangulation and sperner_parity to Mathlib

**Slug**: sperner-ndim-oq-05
**Created**: 2026-04-21T07:30:34-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Contribute the `SpernerTriangulation` typeclass and `sperner_parity` theorem from
`proofs/Proofs/SpernerNDim.lean` to Mathlib (targeting mathlib4#25231) as the
foundation for a Mathlib-native Brouwer fixed point theorem via Sperner's lemma.

Concretely: the Freudenthal triangulation of the standard $n$-simplex $\Delta^n$
satisfies the `SpernerTriangulation` axioms, and the key parity result

$$
\text{sperner\_parity} : \text{FC-simplex count} \equiv 1 \pmod{2}
$$

should be provable for any `SpernerTriangulation` instance.

### Plain Language

We have a gallery proof (`sperner-ndim`) formalizing Sperner's lemma in $n$ dimensions
using an abstract `SpernerTriangulation` typeclass and a parity result `sperner_parity`.
The goal is to upstream these to Mathlib so they become the standard Lean 4 foundations
for the Brouwer fixed point theorem. This involves:

1. Constructing the concrete Freudenthal triangulation satisfying the `SpernerTriangulation` axioms.
2. Proving `sperner_parity` for concrete triangulations via face-door induction.
3. Adapting the code to Mathlib's style/API requirements (namespace, naming conventions, simp lemmas).
4. Opening or reviving the Mathlib PR (mathlib4#25231).

### Why This Matters

- Gives Mathlib its first rigorous $n$-dimensional Sperner's lemma foundation.
- Enables a Mathlib-native Brouwer fixed point theorem (one of the flagship results in topology).
- Closes the gap between the gallery formalization and Mathlib's theorem library.
- Strengthens the lean-genius → Mathlib contribution pipeline.

## Known Results

### What's Already Proven

- `sperner-ndim`: Abstract `SpernerTriangulation` typeclass + `sperner_parity` (with 1 sorry in the main inductive step as of the last audit) — `proofs/Proofs/SpernerNDim.lean`
- `sperner-ndim-oq-01`: Constructive Freudenthal triangulation instance — `proofs/Proofs/SpernerNDimOQ01.lean`
- `sperner-ndim-oq-03`: Concrete Sperner coloring and FC-simplex count — `proofs/Proofs/SpernerNDimOQ03.lean`
- `sperner-ndim-oq-03-oq-01`: Brouwer fixed point via contraction — `proofs/Proofs/SpernerNDimOQ03OQ01.lean`
- Mathlib PR #25231 opened for Sperner's lemma (status unknown — needs checking)

### What's Still Open

- The `sperner_ndim` sorry in `SpernerNDim.lean` (the main inductive parity argument)
- Mathlib-compatible packaging of `SpernerTriangulation` and `sperner_parity`
- Freudenthal instance proof that `SpernerTriangulation` axioms hold for permutation-indexed simplices
- Reviewer feedback on mathlib4#25231 (if PR exists)

### Our Goal

Produce Mathlib-ready Lean 4 code for `SpernerTriangulation` and `sperner_parity`,
resolve the remaining sorry, and advance the mathlib4#25231 PR.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sperner-ndim | Direct parent — abstract typeclass and parity theorem | Freudenthal triangulation, door parity |
| sperner-ndim-oq-01 | Concrete Freudenthal instance | Permutation-indexed simplices |
| sperner-ndim-oq-03 | FC-simplex counting for Brouwer | Constructive coloring |
| sperner-ndim-oq-03-oq-01 | Brouwer FPT via Sperner | Contraction mapping |
| brouwer-fixed-point | Parent Brouwer entry | Topological approach |

## Initial Thoughts

### Potential Approaches

1. **Resolve the sorry first, then upstream**
   - Fix the `sperner_ndim` inductive step sorry in `SpernerNDim.lean`
   - Once sorries are gone, adapt for Mathlib namespace/style
   - Why it might work: The abstract structure is sound; the sorry is a technical lemma
   - Risk: The induction on door parity may require non-trivial auxiliary lemmas

2. **Submit the axiomatized version to Mathlib and add instances separately**
   - Upstream `SpernerTriangulation` typeclass and prove `sperner_parity` conditionally
   - Submit Freudenthal instance as a follow-up PR
   - Why it might work: Splits the contribution into reviewable chunks
   - Risk: Mathlib reviewers may want the instance bundled

3. **Use Mathlib's existing `SimplicialComplex` API**
   - Check if `Mathlib.Topology.Simplicial` or `Mathlib.AlgebraicTopology` provide abstractions
   - Map `SpernerTriangulation` to existing Mathlib types
   - Why it might work: Reduces duplication and eases review
   - Risk: API mismatch may require substantial refactoring

### Key Difficulties

- The face-door induction (boundary parity argument) is combinatorially subtle
- Mathlib's style requirements (naming, docstrings, `simp` lemmas, `@[ext]`) add overhead
- The PR may have accumulated reviewer feedback that needs addressing

### What Would a Proof Need?

- Key lemma 1: Each non-FC simplex contributes exactly 0 or 2 to the door count
- Key lemma 2: The boundary contributes exactly 1 FC simplex (unique boundary door)
- Technical: Finset induction over simplices with decidable Sperner coloring

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical content is well-understood (gallery proofs exist at all levels)
- The main blocker is one sorry and Mathlib packaging
- The Freudenthal instance exists in `SpernerNDimOQ01.lean` — may need minor adaptation
- Mathlib's `SimplicialComplex` infrastructure may help or require mapping

**Estimated Effort**:
- Exploration: 1-2 days (check PR status, read existing proofs, assess sorry difficulty)
- If tractable: 1-2 weeks (close sorry, adapt to Mathlib style, submit PR)
- If hard: the sorry may require a novel auxiliary lemma library

## References

### Papers
- Sperner, E. (1928). "Neuer Beweis für die Invarianz der Dimensionszahl und des Gebietes" — Original Sperner's lemma
- Freudenthal, H. (1942). "Simplizialzerlegungen von beschränkter Flachheit" — Freudenthal triangulation
- Knaster, B., Kuratowski, C., Mazurkiewicz (1929). "KKM lemma" — Related fixed-point approach

### Mathlib
- `Mathlib.Topology.Simplicial.Simplex` — Standard simplex definitions
- `Mathlib.AlgebraicTopology.SimplicialSet` — Simplicial set infrastructure
- `Mathlib.Combinatorics.Simplicial.FaceMap` — Simplicial face maps (if exists)
- PR mathlib4#25231 — Existing Sperner submission

## Metadata

```yaml
tags:
  - topology
  - combinatorics
  - Sperner-lemma
  - triangulation
  - abstract-simplicial-complex
  - mathlib-contribution
  - Brouwer-fixed-point
related_proofs:
  - sperner-ndim
  - sperner-ndim-oq-01
  - sperner-ndim-oq-03
  - sperner-ndim-oq-03-oq-01
  - brouwer-fixed-point
difficulty: medium
source: gallery-gap
created: 2026-04-21T07:30:34-07:00
```

**Significance**: 8/10
**Tractability**: 5/10
