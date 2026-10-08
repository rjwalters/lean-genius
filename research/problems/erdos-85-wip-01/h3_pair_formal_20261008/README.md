# H3 pair cell (t = 0): Lean statement chain

Branch `erdos85/h3-pair-formal-20261008` (based on `c47efaa6ffb`). New
modules only; no existing file is edited.

Status: every statement listed below is built on the cloud builder at
commit dc7f78d47d7. Items 1-16 depend only on `propext`,
`Classical.choice`, `Quot.sound`. Items 17-18 additionally depend on the 24
`native_decide` axioms. See `receipt.md` for jobs, timings and the axiom
output.

## Target

```
Erdos85.H3Pair.orderFortyNineTripleCellExcluded_three_zero :
  OrderFortyNineTripleCellExcluded 3 0
```

via `ThreeHighCanonicalRepresentativeExcluded 0` and the already proved
`threeHighCanonicalGraphCover_zero`
(`Erdos85OrderFortyNineThreeHighZeroFiber.lean`), composed by the existing
`orderFortyNineTripleCellExcluded_three_of_canonical`.

## Route (differs from the staged sketch in squad message 52803)

The sketch proposed proving the paper normalization (matching b = 0/1,
special/ordinary ledger, 36 + 75 normalized cores, host subsets) as Lean
structural lemmas and then certifying 4,572 core/host units. This package
does not do that. It works directly on the Boolean encoding consumed by
`ThreeHighCanonicalRepresentativeExcluded 0`, where the vertex classes are
fixed index ranges, and lets one sound search discover the structure:

- `0,1,2` high; `3,4,5` pair supports (masks 3, 5, 6); `6..23` singleton
  supports, six per colour; `24..48` empty supports.
- The only inputs are the four relation-level constraints of
  `orderFortyNineRelationConstraints 3 masks adj`: degrees, at most one
  common neighbour, prescribed high adjacency, and the partition law (every
  low vertex has exactly one neighbour in each colour fibre).
- Symmetry is handled inside the soundness proof by one lemma
  (`twin_transport`): swapping two low vertices with equal masks and equal
  known rows preserves both the constraints and compatibility with the
  partial graph. No b = 0/1 split, no core list and no host list is stated
  or needed; they arise as branches of the search.

`finiteRowDFS` / `finiteExactCoverSearch` are not reused: their soundness is
stated for a fixed row domain, while this search names fresh vertices
lazily.

## Chain of statements

`proofs/Proofs/Erdos85H3PairEngine.lean` (imports Mathlib only):

| # | Statement | Role |
|---|-----------|------|
| 1 | `Model adj` | Finset-free restatement of the constraints: symmetric, irreflexive, `c4`, `colEx`, `colUniq`, `nb` (a nodup neighbour list of length `capOf`). |
| 2 | `St`, `St.WF`, `Compat s adj` | Partial graph (bit rows + neighbour lists); known edges are edges of `adj`. |
| 3 | `allowed_sound`, `tryAdd_none`, `tryAdd_some` | An edge of a compatible model always passes the degree-cap and no-3-path checks; adding it keeps `WF` and `Compat`. |
| 4 | `twin_transport` | The symmetry lemma described above. |
| 5 | `dfs1_sound` | Phase 1: exactly-one colour clauses on vertices `3..23`; candidates with a smaller twin are skipped (strong induction on the vertex index). |
| 6 | `exists_fresh_nbr`, `insertable_sound`, `patLoop_sound`, `dfs2_sound` | Phase 2: a deficient nonempty vertex has an untouched empty neighbour; that neighbour's colour triple is in the available list; candidates are tried in order and a skipped candidate is banned for the remaining ones. |
| 7 | `count_gate`, `addMany_*`, `dfs3_sound` | Phase 3: empty–empty completion by exact-size neighbour subsets with a counting gate. |
| 8 | `search_sound` | `search f1 f2 f3 s = true → ∀ adj, Model adj → Compat s adj → False`. |

`proofs/Proofs/Erdos85H3PairBridge.lean`:

| # | Statement | Role |
|---|-----------|------|
| 9 | `s0`, `s0_wf` | Initial partial graph = the high–low edges. |
| 10 | `mask_col` | The canonical masks `threeHighRepresentativeMasks 0` agree with the engine labelling (kernel `decide`). |
| 11 | `model_of_constraints` | `orderFortyNineRelationConstraints 3 masks adj` (+ symmetric, irreflexive) gives `Model adj ∧ Compat s0 adj`. |
| 12 | `threeHighCanonicalRepresentativeExcluded_zero_of_pairSearch` | `pairSearch = true → ThreeHighCanonicalRepresentativeExcluded 0`. |
| 13 | `orderFortyNineTripleCellExcluded_three_zero_of_pairSearch` | `pairSearch = true → OrderFortyNineTripleCellExcluded 3 0`. |

`proofs/Proofs/Erdos85H3PairSplit.lean`:

| # | Statement | Role |
|---|-----------|------|
| 14 | `stKey`, `leafPart m r`, `pairPart m r` | Part `r` of `m`: phase-1 leaves whose key is not `r` mod `m` are accepted without search. |
| 15 | `dfs1_sound_parts` | If all `m` parts return `true`, no model is compatible with the state. Phase 1 does not depend on the leaf test, so the proof is the proof of `dfs1_sound` with the leaf hypothesis quantified over `r`. |
| 16 | `orderFortyNineTripleCellExcluded_three_zero_of_parts` | `(∀ r < m, pairPart m r = true) → OrderFortyNineTripleCellExcluded 3 0`. |

`proofs/Proofs/Erdos85H3PairPart00.lean` … `Part23.lean`:

| # | Statement | Role |
|---|-----------|------|
| 17 | `pairPart_24_NN : pairPart 24 NN = true` | One `native_decide` per module; these 24 are the only finite computations. |

`proofs/Proofs/Erdos85H3PairCell.lean`:

| # | Statement | Role |
|---|-----------|------|
| 18 | `threeHighCanonicalRepresentativeExcluded_zero`, `orderFortyNineTripleCellExcluded_three_zero` | Unconditional conclusions. |

`pairSearch` and the two `_of_pairSearch` theorems in the Bridge module are
the unsplit form. They are built as conditional statements; `pairSearch =
true` itself was never established and is not used.

## What a reviewer should check

1. `Model` is implied by the constraints (item 11) and nothing stronger is
   assumed; in particular `colEx`/`colUniq` are the partition law for low
   vertices only, and `nb` is the degree condition.
2. `twin_transport` hypotheses: both vertices low, equal masks, equal known
   rows. Phase 1 checks these at run time (`twinSkip`); phase 2 uses two
   empty vertices with zero rows.
3. Every `true` (= rejected) return of `dfs1`, `dfs2`, `dfs3` is justified;
   running out of fuel and reaching a complete graph both return `false`.
4. `stateOK` is checked at every phase-2 node rather than proved invariant.
5. `pickCore`, `pick3`, `triCounts` and `stKey` are heuristics: no lemma is
   stated about them, and the soundness proofs re-check at run time every
   property of the chosen vertex that they use.

## Relation to the Python verifiers

`engine_prototype.py` in this directory mirrors the Lean search and was
used only to size it. Its node counts are not comparable with the
13,582,750 incidence nodes of `verify_q7_h3_pair_b{0,1}_full_exclusion.py`:
the branching rule and the normalization differ. Nothing in the Lean proof
depends on either Python program.
