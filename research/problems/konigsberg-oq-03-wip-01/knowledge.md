# Knowledge Base: konigsberg-oq-03-wip-01

## S2 SURVEY (2026-05-30, researcher-1) — honest gap assessment

### Current Lean state (as of 2026-05-30)

`proofs/Proofs/KonigsbergOQ03.lean` is 74 lines:

| Metric | Count | Notes |
|--------|-------|-------|
| Axioms | 0 | clean |
| Raw `sorry` | 0 | clean |
| **`:= True` placeholders** | **3** | **honest gaps masquerading as completeness** |
| `def` / `noncomputable def` | 3 + 2 | `RUniformHypergraph` + `InfiniteGraph` structures + `hyperDegree` + 3 prop placeholders + `infiniteDegree` |
| Theorems | 0 | no theorems proved or stated |

The 3 `True` placeholders are:

1. **`HasEulerTour (H : RUniformHypergraph V 2) : Prop := True`** — claim is
   "for r=2, reduces to the graph case", but the actual reduction is not
   implemented. The honest definition would convert `H` to a `SimpleGraph V`
   (via `e ∈ H.edges ↦ (e.toList.head, e.toList.getLast)` or similar) and
   require `∃ u v (w : G.Walk u v), w.IsEulerian`.

2. **`HasInfiniteEulerPath (G : InfiniteGraph V) : Prop := True`** — claim
   is "requires careful definition of infinite paths". The honest definition
   needs an infinite-walk type (Mathlib has `Stream'` but no
   `SimpleGraph.InfiniteWalk` at v4.26.0); this is a non-trivial mini-project.

3. **`HasOneWayEulerPath (G : InfiniteGraph V) : Prop := True`** — claim is
   "path from v₀ through all edges"; same infrastructure gap as (2).

### Mathlib infrastructure survey (v4.26.0 pin)

| Need | Mathlib has | Mathlib does NOT have |
|------|-------------|-----------------------|
| Finite-graph Euler trail | `SimpleGraph.Walk.IsEulerian` (`Mathlib/Combinatorics/SimpleGraph/Trails.lean`) — used by parent `Konigsberg.lean` | — |
| Finite-graph Euler trail iff degree condition | exercised by parent gallery `Konigsberg.lean` | — |
| Hypergraph type | none in `Mathlib.Combinatorics` | r-uniform hypergraph; hypergraph walk; hyperedge trail |
| Infinite walk | none specialized | `SimpleGraph.InfiniteWalk` / `Stream`-based walk |
| Erdős-Grünwald-Weiszfeld (1936) | none | the countable-graph Euler characterisation |

### Honest difficulty assessment

This is a **stub file**, not a "WIP proof". The `problem.md` description says
"this proof is currently marked as a work in progress and needs to be
completed and verified", but the file has zero actual mathematical content
beyond definitions and three `True` placeholders. The path to real progress
is not "close existing sorries" — it is **build the missing infrastructure**.

Estimated effort breakdown:
* **r=2 hypergraph → SimpleGraph reduction**: ~30 LOC (define the conversion;
  prove `HasEulerTour H ↔ ∃ trail, trail.IsEulerian` for r=2).
* **Hypergraph walk infrastructure (r≥3)**: ~200–400 LOC (define hyperedge
  walks, IsEulerian for hypergraphs; the abstraction is non-trivial because
  consecutive hyperedges share at least one vertex but not necessarily a
  specific endpoint).
* **Infinite walk infrastructure**: ~300–500 LOC (a Stream-based walk type,
  IsEulerian predicate, basic API).
* **Erdős-Grünwald-Weiszfeld**: ~200 LOC on top of infinite walk infrastructure.

Total: ~700–1300 LOC, a multi-month project. The problem.md's "medium
difficulty / 1–2 weeks if tractable" assessment is optimistic.

### Why r≥3 hypergraph Euler tours are NOT simply degree-conditioned

The file's docstring correctly notes "for r ≥ 3, the existence of Euler
tours in r-uniform hypergraphs is NP-complete (Lonc-Naroski 2010)". This
means there is **no simple degree condition characterising existence**.
Any "completion" of this slug would need to either:

1. Settle for the r=2 case (which is just the existing graph result).
2. Define the (NP-complete) decision problem and prove its NP-completeness.
3. Pivot to a stronger restriction (e.g., r-partite hypergraphs, or
   the linear hypergraph case where any two hyperedges share ≤1 vertex).

Option 1 is the cleanest small-scope target; options 2 and 3 are independent
mini-projects.

### Recommended path forward

The honest classification is **SURVEY-BLOCKED**:
- The "WIP" framing is misleading; this is a scaffold, not a partially-completed proof.
- The path to completion requires infrastructure that does not exist in Mathlib v4.26.0.
- The first concrete sub-step would be the r=2 case (option 1 above): ~30 LOC,
  fully dischargable using existing Mathlib `SimpleGraph.Walk.IsEulerian`.

### S3 candidate menu

* **A**: Implement the r=2 case — define `toSimpleGraph (H : RUniformHypergraph V 2) : SimpleGraph V`
  and prove `HasEulerTour H ↔ ∃ u v (w : (toSimpleGraph H).Walk u v), w.IsEulerian`.
  Smallest concrete win (~30 LOC), fully dischargable.

* **B**: Convert the three `True` placeholders to `sorry`-guarded honest stubs.
  One-line change per placeholder; lays foundation for sub-OQ scaffolding without
  committing to a specific definitional choice.

* **C**: Pivot to a different slug if no infrastructure work is in scope.

* **D**: Open child sub-OQs (`konigsberg-oq-03-wip-01-oq-01` for r=2, `-oq-02`
  for hypergraph walk infrastructure, etc.) to formalise the 4-step decomposition
  in separate slugs.

---

## Earlier sections (S1 OBSERVE placeholders, never filled in)

### Problem Understanding

[Initial observations about the problem will be recorded here]

### Insights

[Insights from research attempts will be accumulated here]

### Dead Ends

[Approaches known not to work will be documented here]

---

## S16 ACT (2026-07-24, researcher-1) — EGW connectivity necessity + disconnected witness

**What was added** (KonigsbergOQ03.lean 1186 → 1511 LOC, 0 sorry / 0 axiom):

* `InfiniteGraph.Joined` — finite-chain joinedness (`∃ n f, f 0 = u ∧ f n = v ∧
  ∀ i < n, adj (f i) (f (i+1))`), with `refl` / `of_adj` / `symm` (chain
  reversal via `G.symm`) / `trans` (chain concatenation).
* Walk segments are chains: `InfiniteWalk.joined_of_le` / `joined_vertex` (ℕ)
  and `BiInfiniteWalk.joined_of_le` / `joined_vertex` (ℤ).
* **Connectivity necessity, both notions**: a non-isolated vertex appears on
  any Euler walk (`exists_vertex_eq`, from edge coverage), so
  `joined_of_hasOneWayEulerPath` / `joined_of_hasInfiniteEulerPath`;
  contrapositives `not_has{OneWay,Infinite}EulerPath_of_not_joined`; combined
  headline `connectivity_picture`.
* **Disconnected witness `twoLinesGraph`** (`m ~ n ↔ |m − n| = 2`; the line
  graph duplicated on even and odd integers): every vertex has degree 2
  (`twoLinesGraph_even_ncard_neighbors`), so S14/S15 parity is satisfied
  everywhere, yet `0` and `1` are not joined (parity invariant
  `twoLinesGraph_joined_emod`: edges change vertices by ±2, so `% 2` is a
  component invariant) — hence no Euler path of either kind. Headline
  `biInfinite_parity_not_sufficient` completes the insufficiency picture:
  S14's `lineGraph_parity_not_sufficient` covered one-way; this covers
  bi-infinite.

**Lean idioms:** concatenation `if i ≤ n then f i else g (i − n)` needs
explicit `show` to beta-reduce before `rw [if_pos/if_neg]`; reversal
`f (n − i)` needs `n − i − 1 + 1 = n − i` rewritten *in the hypothesis*
before `G.symm`; `omega` closes `Int.toNat` index goals in the ℤ-segment
lemma; `rcases h with hs | hs <;> omega` destructures definitional
adjacency disjunctions of concrete graphs (same trick as `lineGraph`).

**State after S16:** necessity side of EGW now covers **parity (S14/S15) and
connectivity (S16)** for both path notions, each with witnesses showing
independence. Remaining elementary rung: **S17 end-structure necessity**
(one-way Euler path ⟹ at most one "infinite-edge end" survives deleting any
finite edge set) — needs a finite-edge-deletion subgraph construction, ~1
session. Beyond that only the blocked routes remain (EGW sufficiency via
König-lemma compactness, multi-week; r ≥ 3 hypergraph NP-completeness).
