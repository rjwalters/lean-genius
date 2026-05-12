# Knowledge: CellComplex Axioms Audit and Weakening Map

## 1. Current axiomatic surface (proofs/Proofs/SpernerMathlib.lean)

The file does **not** use a `structure CellComplex`. Instead, every
theorem takes the abstraction as **explicit hypotheses**. This is a
deliberate design choice (per the module docstring: "uses hypotheses
rather than a structure"). The combined axiomatic surface, gathered
from the four core theorems, is:

### 1.1 Type-level data

| Symbol  | Type                                              | Role                                    |
|---------|---------------------------------------------------|-----------------------------------------|
| `V`     | `Type*`, `DecidableEq V`                          | vertex type                             |
| `Cell`  | `Type*`, `DecidableEq Cell`, `Fintype Cell`       | cell type                               |
| `d`     | `ℕ`                                               | uniform top dimension                   |
| `vertex` | `Cell → Fin (d + 1) → V`                         | each cell has `d + 1` indexed vertices  |
| `adj`   | `Cell → Fin (d + 1) → Option (Cell × Fin (d + 1))` | symmetric face-adjacency               |
| `c`     | `V → Fin (d + 1)`                                 | coloring                                |

### 1.2 Hypotheses on `adj`

| Name           | Statement                                                                       | Used in                                              |
|----------------|---------------------------------------------------------------------------------|------------------------------------------------------|
| `hadj_symm`    | `∀ s k s' k', adj s k = some ⟨s', k'⟩ → adj s' k' = some ⟨s, k⟩`                | `even_card_interior_doors` (involution-pair step)    |
| `hadj_vertex`  | `∀ s k s' k', adj s k = some ⟨s', k'⟩ → (univ.erase k).image (vertex s) = (univ.erase k').image (vertex s')` | `even_card_interior_doors` (door transfer)           |
| `hadj_ne`      | `∀ s k s' k', adj s k = some ⟨s', k'⟩ → s ≠ s'`                                 | `even_card_interior_doors` (no-fixed-point)          |

### 1.3 No global axioms beyond the above

There are **no** axioms on `vertex` itself (e.g., the proof does
**not** require `vertex s` to be injective per cell, nor that
`vertex s i ≠ vertex s j` for `i ≠ j`, nor that `vertex s` and
`vertex s'` agree on the shared face beyond the image-equality).
This is consistent with the parity argument's robustness: parity
arguments survive vertex-degeneracy.

### 1.4 Pureness assumption — implicit

The pureness assumption ("all cells have the same dimension `d`")
is encoded by the fixed type `Fin (d + 1)` indexing every cell.
There is no per-cell dimension; every cell *must* have exactly
`d + 1` vertices, and every face position is `Fin (d + 1)`. To
weaken to non-pure complexes, one needs a *cell-dependent* index
type `ι : Cell → Type*`.

## 2. Weakening map by proof step

For each axiom/hypothesis, we identify the proof step that consumes
it and the *minimal* weakening that step admits.

### 2.1 `Fin (d + 1)` → cell-dependent `ι s`

| Proof step                                                | Current usage of `Fin (d + 1)`                | Minimal weakening admitted |
|----------------------------------------------------------|-----------------------------------------------|---------------------------|
| `IsDoor` definition                                       | `∀ j : Fin d, ∃ i : Fin (d + 1), ...`         | Requires a notion of "rank ≤ d − 1 face"; with `ι s` of varying cardinality, we need `Fintype.card (ι s) = d + 1` |
| `per_cell_door_parity`                                    | sums over `Fin (d + 1)`                       | Needs `Fintype (ι s)` and a count formula independent of how `ι s` is realized |
| `even_card_interior_doors` adjacency involution           | adjacency map `Cell × Fin (d+1) → Cell × Fin (d+1)` | Refactor to `Σ s : Cell, ι s` (dependent pairs)            |
| `door_count_parity` finite-sum over `Fin (d+1)`           | uses `Finset.univ : Finset (Fin (d+1))`       | Generalises to `Finset.univ : Finset (ι s)`               |
| Boundary-door counting argument                           | uses surjectivity onto `Fin (d + 1)`         | Surjectivity onto a *coloring palette* `P`                 |

**Conclusion (Hypergraph weakening).** The argument generalises to
`ι : Cell → Type*` with `Fintype (ι s)` provided:
1. The coloring takes values in a fixed *palette* `P` of size
   `d + 1` (otherwise "panchromatic" loses meaning).
2. The adjacency `adj : (s : Cell) → ι s → Option (Σ s' : Cell, ι s')`
   is symmetric and preserves the "shared face" image equality.
3. *No* extra hypothesis is needed on `ι s` beyond `Fintype` and
   `DecidableEq`.

**Conjecture.** The proof goes through verbatim after replacing
`Fin (d + 1)` with `ι s` everywhere. Estimated Lean delta: ~80 LOC,
mostly mechanical substitution. S2 ACT candidate.

### 2.2 Pureness → non-pure

For non-pure complexes, cells may have **different** values of
`Fintype.card (ι s)`. The proof breaks at:

| Proof step                                | Breakage                                                                        |
|-------------------------------------------|---------------------------------------------------------------------------------|
| `IsDoor` definition                       | "all lower colors `{0, ..., d-1}` are achieved" requires a *fixed* d across cells |
| `per_cell_door_parity`                    | parity formula `# doors ≡ 𝟙[panchromatic]` requires uniform vertex count       |
| `even_card_interior_doors` adjacency-pair | a (d+1)-cell can share a face with a (d')-cell with d ≠ d', breaking the involution |
| `sperner_parity` (panchromatic count)     | "panchromatic" is dimension-dependent; mixing dimensions is ill-defined         |

**Conjecture.** Sperner's parity *fails* on non-pure complexes in
the literal sense. A salvageable form restricts the panchromatic
existence to the *top-dimensional* sub-complex, *provided* the
top-dimensional cells form a pure sub-complex with consistent
adjacency. This is essentially a tautology (restrict to the pure
piece) and does not yield new content.

**Counter-example sketch (3 cells, mixed dimensions).** See § 5.

### 2.3 `hadj_ne` (adjacent cells distinct)

Used in `even_card_interior_doors` to argue that the involution has
no fixed points. Specifically: `adjMap` sends `(s, k)` to its
adjacent `(s', k')`, and `hadj_ne` ensures `s ≠ s'`, hence
`adjMap (s, k) ≠ (s, k)`.

**Derivability question.** Can `hadj_ne` be derived from
`hadj_vertex` (image-equality on `erase k`) and `hadj_symm`?

- If `s = s'`, then `hadj_vertex s k s k'` gives
  `(univ.erase k).image (vertex s) = (univ.erase k').image (vertex s)`,
  and `hadj_symm` gives `adj s k = some ⟨s, k'⟩` and
  `adj s k' = some ⟨s, k⟩`. The image equality forces a permutation
  of the vertex indices.
- If `vertex s` is injective on `(univ.erase k) ∪ (univ.erase k') =
  univ \ (k ∩ k')`, this permutation is forced to be the identity,
  giving `k = k'`. But `adj s k = some ⟨s, k⟩` is allowed (self-loop
  at the same face index), which is geometrically meaningless but
  not excluded by the *other* two axioms.

**Conclusion.** `hadj_ne` is **load-bearing** in the absence of
`vertex`-injectivity-per-cell. With per-cell vertex injectivity, it
is partially derivable but the corner case `adj s k = some ⟨s, k⟩`
(self-face-loop) remains. **Recommendation:** keep `hadj_ne` as an
axiom; it is one line and removes a corner case.

## 3. Mathlib alignment

### 3.1 `Mathlib.Combinatorics.AbstractSimplicialComplex`

This Mathlib module defines abstract simplicial complexes as
`Finset (Finset V)` closed under taking subsets, with the pure /
non-pure distinction implicit. Sperner's lemma in Mathlib is
currently stated for **specific** triangulations (e.g., barycentric
subdivisions), not at the level of abstract complexes.

**Subsumption check.** Mathlib's `AbstractSimplicialComplex` does
NOT subsume the `SpernerMathlib.lean` abstraction because:
1. Mathlib's version represents cells as `Finset V`, not as a
   *typed* indexing `Fin (d+1) → V`. The indexed form is essential
   for the door-counting parity (which relies on a distinguished
   face per cell).
2. Mathlib's version does not carry an `adj` field; adjacency is
   *derived* from `Finset` intersection. The derivation requires
   choice of face-index, which re-introduces the indexed
   abstraction.

### 3.2 `Mathlib.AlgebraicTopology.SimplicialSet`

Heavier-weight (uses `CategoryTheory`); the door-counting argument
does not need the simplicial *set* machinery (face/degeneracy maps,
simplicial identities). **Not relevant** to OQ-01.

### 3.3 Recommended Mathlib placement

If/when the hypergraph generalization is upstreamed, target
`Mathlib.Combinatorics.AbstractSimplicialComplex` as a sibling
namespace `Mathlib.Combinatorics.AbstractDoorComplex` (or
`Mathlib.Combinatorics.Sperner.Hypergraph`). The new module
provides the **indexed** view that Mathlib's existing
`AbstractSimplicialComplex` cannot give.

## 4. Formal signature proposals (S2 ACT scope)

### 4.1 Hypergraph generalization (OQ-01-A)

```lean
section HypergraphDoor

variable {V : Type*} [DecidableEq V]
variable {Cell : Type*} [DecidableEq Cell] [Fintype Cell]
variable {ι : Cell → Type*} [∀ s, Fintype (ι s)] [∀ s, DecidableEq (ι s)]

/-- Cell vertices indexed by `ι s`. -/
abbrev VertexMap := ∀ s : Cell, ι s → V

/-- Cell-face adjacency over a dependent index. -/
abbrev AdjMap :=
  ∀ s : Cell, ι s → Option (Σ s' : Cell, ι s')

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- A coloring assigns each vertex an element of the palette `P`. -/
abbrev Coloring := V → P

/-- Panchromaticity, hypergraph version. -/
def IsPanchromaticHyper (vertex : VertexMap (ι := ι)) (c : V → P)
    (s : Cell) : Prop :=
  Function.Surjective (c ∘ vertex s)

/-- A face is a door, hypergraph version. -/
def IsDoorHyper (vertex : VertexMap (ι := ι)) (c : V → P)
    (s : Cell) (k : ι s) : Prop :=
  ∀ p : P, p ≠ (c ∘ vertex s) k → ∃ i : ι s, i ≠ k ∧ c (vertex s i) = p

/-- Hypergraph version of the interior-doors parity lemma. -/
theorem even_card_interior_doors_hyper
    (vertex : VertexMap (ι := ι)) (adj : AdjMap (ι := ι))
    (hadj_symm : ∀ s i s' i', adj s i = some ⟨s', i'⟩ → adj s' i' = some ⟨s, i⟩)
    (hadj_vertex : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (Finset.univ.erase i).image (vertex s) =
      (Finset.univ.erase i').image (vertex s'))
    (hadj_ne : ∀ s i s' i', adj s i = some ⟨s', i'⟩ →
      (⟨s, i⟩ : Σ s : Cell, ι s) ≠ ⟨s', i'⟩)
    (c : V → P) :
    Even ((Finset.univ : Finset (Σ s : Cell, ι s)).filter
      (fun p => IsDoorHyper vertex c p.1 p.2 ∧ adj p.1 p.2 ≠ none)).card := by
  sorry  -- S2 ACT target

end HypergraphDoor
```

Estimated Lean delta: ~120 LOC (mechanical adaptation of the existing
`even_card_interior_doors` proof).

### 4.2 Non-pure failure (OQ-01-B)

```lean
/-- Concrete 3-cell complex with two dimensions, demonstrating that
    Sperner-style parity fails on non-pure complexes. -/
def nonPureCounterexample : ... := ...

theorem sperner_fails_on_nonpure_counterexample :
    ∃ (Cell V : Type*) (vertex adj c : ...),
      (∀ ...) ∧                            -- Sperner-coloring hypothesis
      ¬ ∃ s : Cell, IsPanchromatic ... s := sorry
```

Estimated Lean delta: ~50 LOC, concrete enumeration of a 3-cell complex.

## 5. Non-pure counter-example sketch

Consider the following 3-cell, 2-dimensional complex with mixed
top dimensions:

- **Cell `s₀` (2-simplex)**: vertices `{v₀, v₁, v₂}`, colors `(0, 1, 2)`.
- **Cell `s₁` (1-simplex / edge)**: vertices `{v₁, v₂}`, colors `(1, 2)`.
- **Cell `s₂` (1-simplex / edge)**: vertices `{v₀, v₂}`, colors `(0, 2)`.

Set the adjacency: `s₀` shares the edge `{v₁, v₂}` with `s₁` and
the edge `{v₀, v₂}` with `s₂`. Both `s₁` and `s₂` are 1-cells, so
their "doors" are 0-faces (single vertices).

**The coloring `(v₀, v₁, v₂) ↦ (0, 1, 2)` is Sperner on the
boundary `{v₀, v₁, v₂}` of `s₀`.** It is *not* Sperner on the
"boundary" of the whole complex, because the 1-cells `s₁`, `s₂` do
not have boundaries in the same sense.

The parity argument applied to this mixed complex:
- Door count of `s₀` (2-simplex) is 3 (every face is a door because
  the coloring is panchromatic) — `IsPanchromatic` predicate gives
  parity `1`.
- Door count of `s₁` (1-simplex) — definition of `IsDoor` requires
  `∀ j : Fin d', ...` with `d' = 1`, so the "lower colors" are
  `{0}`. The face `{v₁}` of `s₁` has color `1`, the face `{v₂}` has
  color `2` — neither is a door, so door count is 0 (even).
- Door count of `s₂` analogously is 0.

The **sum of door counts** modulo 2 is `1` (odd), but the
**number of panchromatic cells** is `1` (the 2-cell `s₀`).
Coincidentally, the parity check works out for this example.

**But** if we *flip* the coloring on `s₁` to `(2, 1)`, then `s₀`'s
door indicator still gives parity 1 (still panchromatic), and
`s₁`'s door count becomes 1 (because the face `{v₂}` carries
color `2 ≠ 1 = c v₂`'s erase-target — wait, this needs care).

A cleaner failure: take a 2-cell `s₀` and a 0-cell (vertex)
adjacent to it. The 0-cell has no faces, so it cannot host doors;
the parity formula `# panchromatic ≡ # boundary doors` no longer
balances because the boundary-door count from the 0-cell is
ill-defined.

**Conclusion of § 5.** The clean statement is: on non-pure
complexes, the door-counting parity statement is *not even
well-formed* in the current `Fin (d + 1)` framework. It can be
salvaged by restricting to the pure sub-complex of top-dimensional
cells, but doing so reduces the question to the pure case and
yields no new content.

S2 ACT could either (a) formalise the restriction-to-pure lemma as
a corollary of `sperner_parity` or (b) skip non-pure entirely and
focus on hypergraph generalization (recommended).

## 6. Recommended S2 ACT scope

**Primary:** ship `proofs/Proofs/SpernerMathlibHyper.lean` with the
hypergraph-generalized `IsDoorHyper`, `IsPanchromaticHyper`, and
`even_card_interior_doors_hyper`. ~120 LOC, 0 sorries if the
mechanical adaptation works; otherwise 1 strategic sorry tracking
the per-cell parity step.

**Secondary (deferred to S3):** restriction-to-pure-sub-complex
lemma for non-pure complexes.

**Tertiary (deferred):** Mathlib upstreaming experiment.

## 7. Out of scope for this OQ

- KKM-style chromatic theorems (separate OQ family).
- Tucker's lemma generalisation (separate OQ family; `even_card_fpf_invol`
  is the shared dependency, but no further weakening is needed).
- Topological / continuous Sperner (Brouwer fixed-point via direct
  limits — separate OQ family).
- Aristotle integration — the strategic sorry, if introduced, is a
  parity calculation amenable to Aristotle.

## 8. Risks and mitigations

| Risk                                            | Mitigation                                                  |
|-------------------------------------------------|-------------------------------------------------------------|
| Hypergraph version requires per-cell `IsDoor` rephrasing | Use palette `P` of fixed cardinality `d + 1`               |
| `IsDoorHyper` definition diverges from `IsDoor` | S1 OBSERVE locks the palette-based form; review at S2       |
| Parity formula `# doors ≡ 𝟙[panchromatic]` may not survive the dependent type | Verify on a small instance (`Cell = Fin 2, ι s = Fin (s+1)`) before S2 |
| Sister-slug `sperner-simplicial-bridge-oq-01` reaches the same generalisation | Coordinate: simplicial bridge is *concrete* (specific triangulations), hypergraph is *abstract* |

## 9. Sister-slug compatibility

The sibling slugs `sperner-simplicial-bridge-oq-01`,
`sperner-simplicial-instance-oq-05`, and `sperner-ndim-mathlib-oq-01`
all work at the **concrete** level (specific triangulations). The
hypergraph generalisation here is **abstract** and complementary:
once shipped, the concrete sibling proofs can each provide
`CellAdjacencyHypergraph` instances and reuse `even_card_interior
_doors_hyper` instead of the existing `even_card_interior_doors`.

## 10. Estimated total cost (S1 OBSERVE → S3)

| Phase | Effort      | Lean delta             |
|-------|-------------|------------------------|
| S1 OBSERVE | doc-only | +0 Lean (~750 LOC markdown/JSON) |
| S2 ACT    | ~60 min Lean | +120 LOC new file (hypergraph), 0–1 sorries |
| S3 ACT (optional) | ~30 min Lean | +30 LOC (restriction lemma) |
