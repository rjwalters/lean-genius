# H5 stratum (five high vertices, cells T0 / T1 / T2): Lean statement chain

Branch `erdos85/h5-formal-20261008`, based on the H3 pair-cell branch at
`85d336bfbfe`. New modules only (`proofs/Proofs/Erdos85H5*.lean`); no
existing file is edited. Build status, jobs and timings are in `receipt.md`.

## Target

```
FiveHighCanonicalRepresentativeExcluded c      for c = 0, 1, 2
OrderFortyNineStratumExcluded 5
```

The second follows from the three first statements by the existing
`orderFortyNineStratumExcluded_five_of_representativeExclusions`
(`Erdos85OrderFortyNineFiveHighTwoFiber.lean`), which already contains the
proved graph cover `fiveHighCanonicalGraphCover_all`.

`FiveHighCanonicalRepresentativeExcluded c` quantifies over edge vectors
satisfying `orderFortyNineBooleanConstraints 5 (fiveHighRepresentativeMasks c)`.
This is the cheapest shape to reach from a Boolean search, exactly as
`ThreeHighCanonicalRepresentativeExcluded 0` was for the pair cell.

## Labellings

`fiveHighRepresentativeMasks c` orders the vertices as highs, triple
supports, uncovered pair supports, singleton supports by colour, empties:

| cell | triples | pairs | singletons per colour | core | empties |
|------|---------|-------|-----------------------|------|---------|
| T0 | – | 5..14 | 4,4,4,4,4 (15..34) | 5..34 | 35..48 |
| T1 | 5 (012) | 6..12 | 5,5,5,4,4 (13..35) | 5..35 | 36..48 |
| T2 | 5 (012), 6 (034) | 7..10 | 6,5,5,5,5 (11..36) | 5..36 | 37..48 |

"Core" means the low vertices with a nonempty support. `e0 c` is the first
empty vertex.

## How the pair engine generalizes

Reused unchanged, by import from `Erdos85H3PairEngine` (Mathlib only): the
partial-graph type `St`, `addEdge`, `St.WF`, `Compat`, `SFresh`, `pairOK`
and the bit lemmas. None of these mention the labelling.

Restated in `Erdos85H5Engine` with the cell index `c : Fin 3` as a
parameter, five colours and five highs: the tables (`maskArr`, `fiberList`,
`fiberMask`, `coreVerts`, `emptyVerts`), `Model`, `allowed`/`tryAdd`,
`twin_transport`, and the three phases. The proofs are the pair-cell proofs
with `3 ≤` replaced by `5 ≤` and `24 ≤` by `e0 c ≤`. Three things changed in
substance:

1. **Dead-clause check in phase 1.** `clauseDead c s (u, w)`: `u` is low,
   its colour-`w` clause is open and no vertex of fibre `w` can be added to
   `u`. `dfs1` rejects a state when any clause of a given list is dead.
   Soundness (`clauseDead_sound`) is three lines: a model has a colour-`w`
   neighbour `k` of `u`, and `allowed_sound` says `k` is admissible.
2. **Clause lists are arguments.** `dfs1 c fcl cl leaf fuel s` checks `fcl`
   for dead clauses and branches on the first open clause of `cl`. Both
   lists are arbitrary; the properties soundness needs (`5 ≤ u`, clause
   open) are re-checked at run time, as in the pair engine.
3. **Patterns are lists.** In phase 2 the core neighbourhood of an empty
   vertex is a list with one vertex per colour (repetitions allowed when a
   pair or triple support covers several colours), instead of a triple.
   `PatOf c adj e t` says every member of `t` is a core neighbour of `e`
   and every colour is met. `allPats c` is the product of the five fibres;
   inconsistent products are removed by the first `insertable` filter,
   because two distinct members sharing a colour share a high neighbour.

Phase 3 is the pair-cell phase 3.

## Split

For the pair cell nearly all the time was in phases 2 and 3, so the split
selected phase-1 leaves. Here nearly all the time is in phase 1 (see the
prototype figures below), so the split point is inside phase 1:

```
part c k m r s =
  dfs1 c (coreClauses c) ((coreClauses c).take (5 * k)) (leafPart c m r) 170 s
leafPart c m r s = decide (stKey s % m ≠ r) || search c 170 20 20 s
```

Part `r` runs phase 1 on the clauses of the first `k` core vertices; at each
state where those are closed it continues with the full search only if the
state key is `r` mod `m`. `parts_sound` is an instance of
`dfs1_sound_fam`, which proves phase-1 soundness for a family of leaf tests
at once: if at every state the family's leaf tests jointly exclude all
models, and every member of the family returns `true`, there is no model.
`dfs1_sound` is the one-member instance.

## Chain of statements

`proofs/Proofs/Erdos85H5Engine.lean` (imports `Erdos85H3PairEngine`):

| # | Statement | Role |
|---|-----------|------|
| 1 | `Model c adj` | Symmetric, irreflexive, `c4`, `colEx`/`colUniq` for low vertices and the five colours, `nb` (nodup neighbour list of length `capOf`). |
| 2 | `allowed_sound`, `tryAdd_none`, `tryAdd_some`, `addMany_*` | Adding edges of a compatible model never fails and keeps `WF` and `Compat`. |
| 3 | `twin_transport` | Swapping two low vertices with equal masks and equal known rows preserves `Model c` and `Compat s`. |
| 4 | `clauseDead_sound` | A dead clause excludes every compatible model. |
| 5 | `dfs1_sound_fam`, `dfs1_sound` | Phase 1. |
| 6 | `freshWit_allPats`, `insertable_sound`, `exists_fresh_nbr`, `patLoop_sound`, `dfs2_sound` | Phase 2. |
| 7 | `count_gate`, `dfs3_sound` | Phase 3. |
| 8 | `search_sound` | `search c f1 f2 f3 s = true → ∀ adj, Model c adj → Compat s adj → False`. |
| 9 | `parts_sound` | `(∀ r < m, part c k m r s = true) → ∀ adj, Model c adj → Compat s adj → False`. |

`proofs/Proofs/Erdos85H5Bridge.lean`:

| # | Statement | Role |
|---|-----------|------|
| 10 | `s0 c`, `s0_wf` | Initial partial graph = the high–low edges. |
| 11 | `mask_col` | `fiveHighRepresentativeMasks c` agrees with the engine tables (kernel `decide`). |
| 12 | `model_of_constraints c` | `orderFortyNineRelationConstraints 5 (fiveHighRepresentativeMasks c) adj` (+ symmetric, irreflexive) gives `Model c adj ∧ Compat (s0 c) adj`. |
| 13 | `fiveHighCanonicalRepresentativeExcluded_of_parts c k m` | `(∀ r < m, cellPart c k m r = true) → FiveHighCanonicalRepresentativeExcluded c`. |

`proofs/Proofs/Erdos85H5Fast.lean` (imports the bridge):

| # | Statement | Role |
|---|-----------|------|
| 14 | `okF_of_allowed` | `allowed s u x` implies the candidate test against the union of the rows of the neighbours of `u` (`nbrUnion`), and that `u` is not full. |
| 15 | `vertDead_sound`, `deadAll_sound` | Per-vertex dead-end test: a low vertex with an open colour clause that is full or has no candidate passing `okF`. |
| 16 | `dfs1G_sound_fam` | Phase 1 with an abstract dead-end test (`dead : St → Bool`, assumed never to fire on a state with a compatible model) and the clause list as a recursion argument. |
| 17 | `searchF_sound`, `partsF_sound` | Composed search and its split, as items 8 and 9. |
| 18 | `fiveHighCanonicalRepresentativeExcluded_of_partsF c k m` | `(∀ r < m, cellPartF c k m r = true) → FiveHighCanonicalRepresentativeExcluded c`. |

`dfs1G` with `deadAll` visits the same tree as `dfs1` with the full clause
list; it only spends less per node. The native parts use `cellPartF`. The
`part`/`cellPart` functions of the Engine and Bridge modules (items 9 and
13) are proved sound but no computation was completed with them.

`proofs/Proofs/Erdos85H5T{c}PartNN.lean`: one `native_decide` each,
`cellPartF c k m NN = true`. Generated by `gen_parts.py`. Split parameters
`(k, m)`: T0 `(4, 16)`, T1 `(6, 16)`, T2 `(12, 8)`.

`proofs/Proofs/Erdos85H5T{c}.lean`: `fiveHighCanonicalRepresentativeExcluded_{c}`.

`proofs/Proofs/Erdos85H5Stratum.lean`:
`orderFortyNineTripleCellExcluded_five_{zero,one,two}` and
`orderFortyNineStratumExcluded_five : OrderFortyNineStratumExcluded 5`.

## What a reviewer should check

1. `Model c` is implied by the constraints (item 12) and nothing stronger
   is assumed. `colEx`/`colUniq` are the partition law for low vertices
   only; highs are pairwise non-adjacent because their masks are 0.
2. `twin_transport` hypotheses: both vertices low, equal masks, equal known
   rows. Phase 1 checks these at run time (`twinSkip`); phase 2 applies it
   to two empty vertices with zero rows.
3. Every `true` return of `dfs1`, `dfs2`, `dfs3` is justified; running out
   of fuel and reaching a complete graph both return `false`.
4. `coreClauses`, `pickCore`, `pick3`, `patCounts` and `stKey` are
   heuristics: no lemma is stated about them.
5. In `dfs2_sound` the transported witness uses that pattern members are
   below `e0 c` (so the swap of two empties fixes them); this bound is part
   of `PatOf`.

## Prototype (sizing only, not evidence)

`h5proto.c` mirrors the Lean search (first-open clause order, dead-clause
check, same key). Runs on the cloud builder, one core each:

| cell | phase-1 nodes | phase-1 leaves | phase-2 nodes | phase-3 nodes | completions | C seconds |
|------|--------------:|---------------:|--------------:|--------------:|------------:|----------:|
| T0 | 59,408,034 | 882 | 14,888 | 240 | 0 | 71 |
| T1 | 29,403,925 | 154 | 1,360 | 52 | 0 | 31 |
| T2 | 18,288,563 | 92 | 372 | 0 | 0 | 21 |

Choosing the clause with the fewest candidates instead of the first open
clause was much worse (no cell finished phase 1 in 40 s). Without the
dead-clause check T2 needs 66,477,497 phase-1 nodes.

Split sizing from the prototype (`pre=K mod=M`; nodes above the split point
are repeated in every part):

| cell | k | m | nodes above split | part nodes, min – max |
|------|--:|--:|------------------:|----------------------:|
| T0 | 4 | 16 | 13,711 | 2,904,233 – 4,460,733 |
| T1 | 6 | 16 | 68,776 | 1,450,498 – 2,219,693 |
| T2 | 12 | 8 | 1,278,013 | 2,024,272 – 2,148,113 |

Smaller prefixes for T2 leave two subtrees of about 7M nodes each in single
parts.

Lean evaluates the parts in the interpreter. A probe part of 284,733 nodes
(T2, `k = 4`, `m = 8`, `r = 2`) took 209 s with `cellPart` and 151 s with
`cellPartF`, i.e. roughly 0.5 ms per node for the latter, against about
1 µs per node in C.

Nothing in the Lean proof depends on the prototype.
