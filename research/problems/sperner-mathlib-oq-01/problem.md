# Problem: Weakened CellComplex Axioms — Hypergraphs and Non-Pure Complexes

## Statement

### Plain Language

The Lean file `proofs/Proofs/SpernerMathlib.lean` (897 lines, 0
sorries) proves Sperner's lemma via door-counting parity over an
**abstract cell type** `Cell` equipped with a vertex map and an
adjacency. The axioms are **hypothesis-based** (not a `structure`):
each cell has exactly `d + 1` vertices indexed by `Fin (d + 1)`,
adjacency is symmetric, face-sharing is captured by image-equality on
`Finset.univ.erase k`, and adjacent cells are distinct.

**Open question.** Identify the **minimal** axiomatic surface on
which the door-counting argument still goes through. Specifically:

- **OQ-01-A (Hypergraph).** Can `Fin (d + 1)` be replaced with a
  cell-dependent finite type `ι s` (each cell has its own arity)?
  Under what extra hypotheses does the door / parity / panchromatic
  chain still produce a panchromatic cell?
- **OQ-01-B (Non-pure).** Can the assumption that every cell has the
  *same* dimension `d` be dropped, so that cells of varying
  dimensions coexist? What does "panchromatic" / "Sperner coloring"
  even mean in this setting, and which dimension's cells receive the
  parity-driven existence conclusion?
- **OQ-01-C (Boundary-axioms minimal).** Mathematically the proof
  only uses three properties of `adj`: symmetry, vertex-image
  equality on the shared face, and `s ≠ s'`. Are any of these
  redundant for the parity conclusion alone (i.e., is the symmetry
  axiom load-bearing for `even_card_interior_doors`, or can it be
  derived from the other two plus a finiteness condition)?

### Formal Signature Targets

S1 OBSERVE locks the formal scope. The new file (or amendment to
`SpernerMathlib.lean`) targets the following signatures:

```lean
-- §A. Hypergraph generalization
def IsPanchromatic_hyper {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]
    {V : Type*} (vertex : ∀ s, ι s → V)
    (palette : V → Σ s, ι s)  -- coloring assigns each vertex an (s, index) tag
    (s : Cell) : Prop :=
  Function.Surjective (palette ∘ vertex s)

structure CellAdjacencyHypergraph
    (Cell : Type*) (V : Type*) {ι : Cell → Type*} [∀ s, Fintype (ι s)] : Prop where
  vertex : ∀ s, ι s → V
  adj    : ∀ s, ι s → Option (Σ s' : Cell, ι s')
  symm   : ∀ s i s' i', adj s i = some ⟨s', i'⟩ → adj s' i' = some ⟨s, i⟩
  ...

-- §B. Non-pure complex generalization (statement only at this stage)
theorem sperner_nonpure_failure_example : ∃ ..., ¬ ∃ panchromatic_top
```

(Full signatures are in `knowledge.md` § 4.)

### Acceptance Criteria

S1 OBSERVE (this PR) — doc-only:

1. **Axioms inventory.** Tabulate every hypothesis carried by
   `even_card_interior_doors`, `door_count_parity`, `sperner_parity`,
   `exists_panchromatic` in the current file.
2. **Weakening map.** For each hypothesis, identify which proof step
   it enters and what *minimal weakening* is consistent with that
   step.
3. **Counter-example sketch (non-pure).** A small explicit complex
   (≤ 5 cells, 2 dimensions) demonstrating that Sperner-style parity
   fails when cells have mixed dimensions, **or** identify the
   precise extra axiom that saves it.
4. **Hypergraph generalization scope.** Decide whether the
   generalization should be a *new structure* `CellAdjacencyHypergraph`
   or a *parameterized refactor* of the existing
   `even_card_interior_doors` (which already takes `vertex` /
   `adj` as hypotheses, not structure fields).
5. **Mathlib alignment.** Confirm that
   `Mathlib.Combinatorics.AbstractSimplicialComplex` and
   `Mathlib.AlgebraicTopology.SimplicialSet` do **not** subsume the
   abstraction (the file's docstring already implies this; verify
   with explicit citations).

S2 ACT (a future iteration): ship a small Lean delta that either (a)
adds the hypergraph generalization as a parameterized theorem
sitting next to `even_card_interior_doors`, or (b) ships the
non-pure counter-example as a concrete `def` + `theorem` proving the
parity argument's failure-mode.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - combinatorics
  - topology
  - sperner
  - cell-complex
  - hypergraphs
  - axioms-audit
  - mathlib
```

**Significance**: 6/10 — substantial generalization potential for
Sperner-type results across combinatorial topology, but the question
is primarily about *axiomatic taste* and Mathlib API design rather
than about new mathematical content.

**Tractability**: 5/10 — the axioms inventory is mechanical, but the
weakening map requires judgment calls, and the non-pure counter-
example needs care (Sperner's failure on non-pure complexes is folklore
but not trivially recorded in the gallery).

## Why This Matters

1. **Reusability for Tucker / Borsuk-Ulam.** The proof's helper
   `Sperner.even_card_fpf_invol` (line 59 of the file) is *already*
   abstracted out and serves Tucker's lemma and Borsuk-Ulam-style
   parity arguments. The OQ-01 generalization extends the same
   reusability to the *higher-level* door-counting pipeline.
2. **Hypergraph Sperner.** Several recent results in discrete
   geometry (e.g., colorful KKM-type theorems, Kalai's conjecture
   variants) use hypergraph generalizations of Sperner. A
   Mathlib-ready hypergraph axiomatization unblocks future
   formalizations.
3. **Sperner-mathlib roadmap.** The file's name —
   `SpernerMathlib.lean` — signals upstreaming intent. A clean
   axiomatic surface is a prerequisite for upstream review.

## Related Gallery Proofs

| Slug                                    | Relevance                                                |
|-----------------------------------------|----------------------------------------------------------|
| `sperner-mathlib`                       | Parent: hosts the door-counting parity proof to be audited |
| `sperner-simplicial-bridge-oq-01`       | Sibling: alternative axiomatization via `SimplicialBridge` |
| `sperner-simplicial-instance-oq-05`     | Sibling: instance-based variant of the simplicial bridge   |
| `sperner-ndim-mathlib-oq-01`            | Sibling: n-dim cube specialization of `SpernerMathlib`     |
| `sperner-ndim-mathlib-oq-02`            | Sibling: alternative n-dim cube generalization             |
| `sperner-freudenthal`                   | Concrete model: Freudenthal triangulation as an instance   |
| `sperner-grid`                          | Concrete model: integer-grid triangulation as an instance  |
| `Mathlib.Combinatorics.AbstractSimplicialComplex` | Mathlib analog (pure complexes)                  |

## Open Sub-Questions

- **OQ-01-A** (hypergraph): is the right Mathlib name
  `CellAdjacencyHypergraph` or `AbstractDoorComplex`? Decision
  deferred to S2 ACT.
- **OQ-01-B** (non-pure): does the parity argument *fail* on
  non-pure complexes, or can it be salvaged by restricting to the
  top-dimensional sub-complex? S1 OBSERVE conjectures *fail*, with
  a 3-cell counter-example sketched in `knowledge.md` § 5.
- **OQ-01-C** (boundary-axioms): is `hadj_ne` (adjacent cells
  distinct) load-bearing, or derivable from `hadj_vertex` +
  `hadj_symm`? S1 OBSERVE conjectures *derivable* in characteristic
  0 settings, *load-bearing* otherwise; concrete argument deferred.

## References

- De Longueville, M. (2013). *A Course in Topological Combinatorics*.
  Springer. § 2 (Sperner / KKM family).
- Sperner, E. (1928). "Neuer Beweis für die Invarianz der
  Dimensionszahl und des Gebietes." *Abh. Math. Sem. Univ. Hamburg*
  6: 265–272.
- Bárány, I. (2010). "Sperner's lemma and discrete fixed-point
  theory." In *Handbook of Discrete and Computational Geometry*.
- Mathlib: `Mathlib.Combinatorics.AbstractSimplicialComplex` (pure
  complexes), `Mathlib.AlgebraicTopology.SimplicialSet` (simplicial
  sets, more general but heavier).
- Local file: `proofs/Proofs/SpernerMathlib.lean` (897 lines, 0
  sorries) — the audit target.
