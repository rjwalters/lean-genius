# erdos-1009-oq-02: Edge-Disjoint K₄ Copies Beyond Turán Threshold

## Problem Summary

**Open Question**: Is there an analogue of Györi's theorem for K₄?
If G has ⌊n²/3⌋ + k edges with k < cn, does G contain ≥ k - g(c) edge-disjoint K₄ copies?

The open question (edgeDisjointK4_question) remains open — it's a research-level conjecture.
We proved the supporting infrastructure: Turán's theorem for K₄ and existence above threshold.

## Session 2026-04-03 (Session 1) - COMPLETED: All supporting theorems proved

**Mode**: FRESH
**Outcome**: completed — 0 sorries in Erdos1009OQ02Problem.lean

### What I Did
- Proved `turanK4_extremal`: K₄-free graphs have ≤ ⌊n²/3⌋ edges
  - Used `CliqueFree.card_edgeFinset_le` from Mathlib `Extremal/Turan.lean` (v4.26.0)
  - Extracted arithmetic into private lemma `turanK4_arith`  
  - `simp [h] ; omega` works per case after 3-way case split on n%3
- Proved `exceeds_turanK4_has_clique4`: exceeding Turán threshold implies K₄ exists
  - Used `Finset.card_eq_four` to decompose 4-element clique finset
  - Constructed `Clique4 G` from the 4 vertices + clique adjacencies

### Key Findings
- `CliqueFree.card_edgeFinset_le` in Mathlib returns `let n := Fintype.card V; ...` — `simp only at hbound` unfolds this, but doesn't reduce constants like `3-1`, `2*3`, `0^2`; need `simp [h]` (full simp) or extract arithmetic into a separate lemma
- `push_neg` on `¬ ∃ K : Clique4 G, True` gives `∀ K, False` (simplifies ¬True)
- `Finset.card_eq_four` at `Mathlib.Data.Finset.Card` gives the needed 4-element decomposition
- Pattern follows exactly the K₃ proof in `Erdos1009Problem.lean`

### Files Modified
- `proofs/Proofs/Erdos1009OQ02Problem.lean` (sorries 0 → 0, was 4)
- `src/data/research/problems/erdos-1009-oq-02.json`

### Next Steps
- The main open question `edgeDisjointK4_question` remains open (research-level)
- Future work: K₅ analog? Or sharp bounds for K₄ excess?

## Session 2026-04-27 (Session 2) - COMPLETED: Infrastructure + follow-up questions

**Mode**: REVISIT
**Outcome**: completed — added 2 infrastructure lemmas, generated follow-up questions

### What I Did
- Added `Clique4.edges_subset_edgeFinset`: every K₄ edge is in `G.edgeFinset`
  - Proof: `simp only [Clique4.edges, Finset.mem_insert, Finset.mem_singleton]` then 6-way `rcases`,
    `all_goals simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]`, then `exact K.h{ab,ac,...}`.
  - Pattern validated against `Erdos1017OQ01.lean:278`.
- Added `Clique4.edges_nonempty`: K₄ edge set is nonempty
  - Direct witness `s(K.a, K.b)` + `simp [Clique4.edges]`
- Generated `follow-ups.md` with 3 candidate research questions
- Corrected stale `phase: NEW` → `phase: COMPLETED` in pool metadata (file is 0-sorry, 0-axiom)

### Why These Lemmas
Both are prerequisites for any future induction on edge-disjoint K₄ count. The
trivial bound `excess ≥ 6k+1 → ≥ k+1 edge-disjoint K₄'s` requires removing the
6 edges of one K₄ (proved via `SimpleGraph.deleteEdges`) and arguing the
remaining graph still exceeds the Turán threshold. `edges_subset_edgeFinset`
gives `K.edges.card ≤ G.edgeFinset.card` (via `Finset.card_le_card`),
which is the cardinality side of the induction step.

### Key Findings
- Mathlib provides `SimpleGraph.deleteEdges : Set (Sym2 V) → SimpleGraph V`
  with `(G.deleteEdges s).Adj v w ↔ G.Adj v w ∧ ¬s(v, w) ∈ s` (Basic.lean:803)
- `edgeFinset_deleteEdges`: `(G.deleteEdges s).edgeFinset = G.edgeFinset \ s` (Finite.lean:122)
- These give the path to a trivial linear bound theorem (see follow-ups.md #1)
- The infrastructure is sufficient; what's missing is `Clique4.edges.card = 6`
  (cardinality count from distinct vertices via `Sym2.eq_iff` case analysis)

### Files Modified
- `proofs/Proofs/Erdos1009OQ02Problem.lean` (+ 2 lemmas, 0 sorries → 0 sorries)
- `src/data/research/problems/erdos-1009-oq-02.json` (phase NEW → COMPLETED, knowledge updated)
- `research/problems/erdos-1009-oq-02/state.md` (NEW → COMPLETED)
- `research/problems/erdos-1009-oq-02/follow-ups.md` (new)

### Cross-Application
The K₄ subset/nonempty lemmas are likely useful for `erdos-1009-oq-01` (K₃ analog
already has this kind of edge-set arithmetic) and any future K_r generalization.
The `Clique4.edges` definition pattern transfers directly.
