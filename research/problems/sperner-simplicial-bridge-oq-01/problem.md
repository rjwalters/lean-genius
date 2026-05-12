# Problem: Sperner's lemma on non-pure simplicial complexes (mixed-pseudomanifold)

**Slug**: sperner-simplicial-bridge-oq-01
**Created**: 2026-05-12
**Status**: Active (S1 OBSERVE delivered)
**Source**: gallery-gap (parent `sperner-simplicial-bridge` `openQuestions[0]`)

## Problem Statement

### Formal Statement

Let `K` be a finite simplicial complex (or finite cellular structure on
a `Finset (Finset E)`) whose facets do **not** all have the same
dimension. Define a stratified pseudomanifold condition
$$\mathrm{MixedPseudomanifold}(K) \;:\equiv\; \forall d,\;\mathrm{IsPseudomanifold}\bigl(\{\,s \in \mathrm{facets}(K) \mid \#s = d+1\,\}\bigr).$$
For each $d$ admitting a non-empty $d$-stratum with an odd boundary
door count, the parent theorem `exists_panchromatic` applied to that
stratum produces a panchromatic $d$-cell. Formalise this in Lean as a
`sperner_mixed_panchromatic` corollary of the existing pure-stratum
result.

### Plain Language

The parent gallery proof (`sperner-simplicial-bridge`, verified, 0
axioms, 22 theorems, 611 lines) formalises Sperner's lemma under a
**pure** pseudomanifold hypothesis: every top simplex has exactly
`d+1` vertices. OQ-01 asks: can the *pure* condition be weakened?

The answer is **yes, trivially via stratification**, because the
door-counting argument respects dimensions:

- A *door* at level $d$ is a codimension-1 face of a $d$-simplex, so a
  $(d-1)$-element subset.
- A codim-1 face of a $d$-simplex (cardinality $d$) and the entire
  $(d-1)$-simplex (also cardinality $d$ when read as a `Finset E`) are
  syntactically interchangeable only if the same `Finset E` appears in
  both roles — but the parent theorem's adjacency relation
  `adjFn topCells hcard p.1 p.2` is type-indexed on the *uniform*
  cardinality `d+1`. Mixing facet dimensions therefore *partitions*
  the door-count by dimension, so each dimension's stratum can run the
  parent's `exists_panchromatic` independently.

The OQ then reduces to:

1. Stating `MixedPseudomanifold` (every dimension-stratum is
   independently a pseudomanifold).
2. Stating `sperner_mixed_panchromatic` (for the chosen dimension $d$
   with odd boundary door count on its stratum, a panchromatic
   $d$-cell exists in `topCells_of_dim K d`).
3. Proving (2) by `exists_panchromatic` applied to that stratum.

The non-trivial work is *defining* the predicates and *checking*
that the door-count odd-parity hypothesis carries through stratifi-
cation. The proof itself is a one-line invocation of the parent.

### Why This Matters

- **Lifts the parent gallery proof's open-question count** from 4 to
  3, while not requiring re-architecting the parent's adjacency
  framework. Direct response to OQ-01 in
  `src/data/proofs/sperner-simplicial-bridge/meta.json`.
- **Captures the natural use-case from algebraic topology**: most
  geometrically meaningful simplicial complexes (cell complexes of
  CW-pairs, triangulated manifolds with boundary, polytopal
  decompositions of non-equidimensional spaces) are non-pure. The
  pure-pseudomanifold hypothesis is restrictive and not aesthetically
  natural for `Mathlib.AlgebraicTopology.SimplicialSet` (cf. OQ-03 and
  OQ-04 of the same parent).
- **Bridges to `Mathlib.Geometry.SimplicialComplex.facets`**: the
  Mathlib infrastructure for non-pure complexes uses
  `K.facets = {s ∈ K.faces | maximal under ⊆}`. Our `topCells_of_dim`
  is the dimension-grading of that set.
- **Direct precursor to OQ-02 and OQ-04**: the `Mathlib.Geometry.
  SimplicialComplex` bridge (OQ-02) and the `SimplicialSet adjFn`
  instance (OQ-04) both presume a stratification framework. Doing
  OQ-01 first makes those tractable.

## Parent Gallery Proof

- **Proof slug**: `sperner-simplicial-bridge`
- **Title**: Sperner's Lemma Bridge to Simplicial Complexes
- **Lean file**: `Proofs/SpernerSimplicialBridge.lean` (611 lines,
  22 theorems, 0 axioms, 0 sorries, `verified`).
- **Existing infrastructure** (verbatim signatures):
  - `noncomputable def vertexEnum (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) : E`
  - `noncomputable def faceOf (s : Finset E) (hs : s.card = d + 1) (k : Fin (d + 1)) : Finset E`
  - `noncomputable def containersOf (topCells : Finset (Finset E)) (f : Finset E) : Finset (Finset E)`
  - `noncomputable def adjFn (topCells : Finset (Finset E)) (hcard : ∀ s ∈ topCells, s.card = d + 1) : ...`
  - `theorem exists_panchromatic (topCells : Finset (Finset E)) (hcard : ...) (hpseudo : ...) (c : E → Fin (d+1)) (hbdry : Odd (...)) : ∃ s, IsPanchromatic ... s`

## Suggested First Steps (revised after S1 OBSERVE)

1. **Define `topCellsOfDim`**. The dimension-$d$ stratum of a mixed
   complex:
   ```lean
   noncomputable def topCellsOfDim
       (K : Finset (Finset E)) (d : Nat) : Finset (Finset E) :=
     K.filter (fun s => s.card = d + 1)
   ```
   Trivially `topCellsOfDim K d ⊆ K` and
   `∀ s ∈ topCellsOfDim K d, s.card = d + 1`. (S2)

2. **Define `MixedPseudomanifold`**. Each stratum independently
   satisfies the pseudomanifold property:
   ```lean
   def MixedPseudomanifold (K : Finset (Finset E)) : Prop :=
     ∀ d : Nat, ∀ f : Finset E, f.card = d →
       ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2
   ```
   Note: doors at level $d$ (cardinality-$d$ faces) are not constrained
   by cells of dimension $\ne d$, so the inner cardinality bound is per-
   stratum. (S2)

3. **State `sperner_mixed_panchromatic`**. For each dimension $d$ with
   an odd door count on the $d$-stratum, there exists a panchromatic
   $d$-cell in `topCellsOfDim K d`:
   ```lean
   theorem sperner_mixed_panchromatic
       {E : Type} [DecidableEq E] [LinearOrder E]
       (K : Finset (Finset E)) (hpseudo : MixedPseudomanifold K)
       (d : Nat) (c : E → Fin (d + 1))
       (hbdry : Odd (Finset.univ.filter (fun p => ... boundary doors ...)).card) :
       ∃ s : { s : Finset E // s ∈ topCellsOfDim K d },
         Sperner.IsPanchromatic ... c s := by
     have hcard : ∀ s ∈ topCellsOfDim K d, s.card = d + 1 := fun s hs =>
       (Finset.mem_filter.mp hs).2
     have hps : ∀ f, f.card = d → ((topCellsOfDim K d).filter (· ⊆ ·)).card ≤ 2 :=
       hpseudo d
     exact exists_panchromatic (topCellsOfDim K d) hcard hps c hbdry
   ```
   (S3)

4. **Concrete instance**. Show that any pure topCells satisfies
   `MixedPseudomanifold`, recovering the parent's `exists_panchromatic`:
   ```lean
   theorem exists_panchromatic_of_pure
       (topCells : Finset (Finset E))
       (hcard : ∀ s ∈ topCells, s.card = d + 1)
       (hpseudo : ∀ f, f.card = d → (topCells.filter (· ⊆ ·)).card ≤ 2)
       ... :
       sperner_mixed_panchromatic := ...
   ```
   demonstrating the new framework subsumes the old. (S3 or S4)

5. **Gallery integration**. Add `sperner-simplicial-bridge-oq-01` to
   the gallery as a small `formalized` entry citing the parent. (S4)

## Metadata

- **Tier**: B
- **Significance**: 6/10
- **Tractability**: 5/10 (reduced from raw 5 to "5 with caveats" — see
  S1 risk register in `knowledge.md`).
- **Tags**: combinatorics, topology, sperner, simplicial-complex,
  pseudomanifold, stratification, gallery-extension
- **Estimated effort**: 2-3 sessions for full deliverable.
  - S1 OBSERVE (this session, doc-only).
  - S2 SCAFFOLD (~80 LOC): `topCellsOfDim` + `MixedPseudomanifold`
    definitions + `exists_panchromatic_of_pure` as sanity check.
  - S3 ACT (~50-80 LOC): `sperner_mixed_panchromatic` theorem +
    boundary-door-count translation lemma.
  - S4 GALLERY (~30 LOC + meta.json): gallery entry for the OQ-01
    closure.
- **Dependencies on parent**: none; parent file is unchanged.
- **Mathlib API exercised**: `Finset.filter`, `Finset.mem_filter`,
  `Finset.card_filter`, no new imports needed beyond
  `Proofs.SpernerSimplicialBridge`.
