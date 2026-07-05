# Problem: Sperner on Infinite Complexes via Compactness

**Slug**: sperner-simplicial-bridge-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{A locally finite, properly Sperner-labeled simplicial pseudomanifold has a panchromatic cell, obtained as a } \textbf{compactness limit} \text{ of the finite door-counting existence over an exhaustion by finite subcomplexes.}
$$

### Plain Language

The parent entry proves a finite Sperner-type result by door-counting on simplicial pseudomanifolds. We want to lift it to *infinite* (locally finite) complexes: given a proper Sperner labeling of an infinite, locally finite pseudomanifold, produce a panchromatic cell as a limit of the finite result applied to an increasing exhaustion of finite subcomplexes, using a compactness argument (Tychonoff / König's lemma over the finitely-branching tree of finite panchromatic witnesses).

### Why This Matters

Compactness ("finite ⇒ infinite") is one of the most reusable moves in combinatorics and logic (de Bruijn–Erdős colorings, König's lemma, ultrafilter limits). Realizing it on top of the verified finite door-counting engine both extends the gallery's Sperner results to a genuinely new regime and demonstrates a formal compactness bridge that other finite combinatorial results in the gallery could reuse.

## Known Results

### What's Already Proven

- `sperner-simplicial-bridge` (VERIFIED, 0 axioms): pseudomanifold door-counting yielding finite panchromatic-cell existence.
- `sperner-mathlib` (VERIFIED): the abstract `CellComplex` parity engine.
- König's lemma / Tychonoff for finite discrete spaces are available in Mathlib (`Mathlib.Topology.Compactness`, `Mathlib.Combinatorics` and order-theoretic König results).

### What's Still Open

- No infinite/locally-finite Sperner statement is formalized.
- The compactness bridge from finite panchromatic existence to an infinite limit is not built.

### Our Goal

State a locally-finite pseudomanifold with a proper Sperner labeling; build an exhaustion by finite subcomplexes; apply the finite result to each; and extract a limiting panchromatic cell via König's lemma or Tychonoff on the (finitely-branching) inverse system of finite witnesses. A clean statement plus the compactness extraction — even restricted to a concrete family such as an infinite triangulated strip — is a valuable milestone.

## Known Results — Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| sperner-simplicial-bridge | Parent; finite pseudomanifold door-counting to lift | pseudomanifold, door counting |
| sperner-mathlib | Underlying abstract parity engine | CellComplex, parity |
| sperner-simplicial-instance | Concrete triangulation instances to exhaust | Triangulation |

## Initial Thoughts

### Potential Approaches

1. **König's lemma over finite witnesses**: for an exhaustion $K_1\subset K_2\subset\cdots$ with $\bigcup K_i$ the whole complex, each $K_i$ has a nonempty finite set of panchromatic cells (finite result). Restriction maps between consecutive levels give a finitely-branching, infinite, finitely-supported tree; König's lemma yields an infinite compatible branch, i.e. a cell panchromatic in the limit.
   - Why it might work: finitely-branching + infinite is exactly König's hypothesis; the finite existence is already proved.
   - Risk: defining the restriction/compatibility maps so the tree is genuinely finitely branching (local finiteness is essential).

2. **Tychonoff on the product of finite witness sets**: express "a choice of panchromatic cell at each level, compatible" as a nonempty intersection of closed sets in a compact product; nonemptiness follows from the finite-intersection property.
   - Why it might work: standard compactness packaging.
   - Risk: encoding compatibility as closed conditions in Mathlib's product topology.

### Key Difficulties

- Formalizing local finiteness and an exhaustion of the infinite complex.
- Encoding compatibility between finite panchromatic witnesses at successive levels so a compactness principle applies.

### What Would a Proof Need?

- Key lemma 1: finite panchromatic existence per subcomplex (from the parent).
- Key lemma 2: a finitely-branching inverse system of witnesses (local finiteness).
- Key lemma 3: König's lemma / Tychonoff to extract the limit cell.
- Technical requirements: `Mathlib`'s König lemma or compactness of finite-discrete products; an exhaustion API.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The finite engine is verified (0 axioms); the new content is the compactness packaging, for which Mathlib has König/Tychonoff.
- Restricting to a concrete infinite family (e.g. a triangulated half-strip) gives a checkable first target.
- Main risk is set-up bookkeeping (exhaustion, restriction maps), not deep mathematics.

**Estimated Effort**:
- Exploration: 2-3 days
- If tractable: 1-3 weeks (concrete family, then general locally-finite case)
- If hard: the general compatibility encoding may remain partial

## References

### Papers
- de Bruijn & Erdős, "A colour problem for infinite graphs...," 1951 — the finite ⇒ infinite compactness paradigm.
- Matoušek, *Using the Borsuk–Ulam Theorem* — Sperner/KKM and limiting arguments.

### Online Resources
- Standard treatments of König's lemma and compactness in infinite combinatorics.

### Mathlib
- `Mathlib.Topology.Compactness` / `Mathlib.Order.*` — König's lemma and Tychonoff.
- The parent `SpernerSimplicialBridge.lean` — finite panchromatic existence.

## Metadata

```yaml
tags:
  - combinatorics
  - topology
  - sperner
  - compactness
  - koenig-lemma
related_proofs:
  - sperner-simplicial-bridge
  - sperner-mathlib
  - sperner-simplicial-instance
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 5/10
