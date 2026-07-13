# Follow-Up Research Questions: erdos-1009-oq-02

Generated 2026-04-27 after completing the infrastructure (turanK4_extremal,
exceeds_turanK4_has_clique4) for the K₄ analog of Györi 1988.

## 1. Trivial linear lower bound on edge-disjoint K₄ copies

**Statement**: If `excessEdgesK4 G ≥ 6 * k + 1`, then `maxEdgeDisjointK4 G ≥ k + 1`.

**Why this matters**:
- This is the K₄ analog of the trivial K₃ bound `excess ≥ 3k+1 → ≥ k+1 triangles`.
- The leading constant 1/6 is far from the conjectured 1 (Györi-style for K₄), so
  this is *not* the open conjecture. But it is the first non-trivial step:
  showing that the rate is positive.
- Distinct from existing gallery: the K₃ version is in Erdos1009Problem.lean
  encoded as an axiom (`gyori_optimal`); the K₄ version is unproved anywhere
  in the gallery, even at the trivial 1/6 rate.

**Proof sketch (formalizable today, ~80 lines)**:
1. Induction on k.
2. Base: k = 0, excess ≥ 1 gives one K₄ via `exceeds_turan_k4_one_copy`.
3. Step: from excess ≥ 6(k+1)+1, get K₁ via base case.
4. Form `G' := G.deleteEdges (K₁.edges : Set (Sym2 V))`.
5. `numEdges G' = numEdges G - 6` via `Clique4.edges_subset_edgeFinset` +
   `Finset.card_sdiff` + `Clique4.edges.card = 6`.
6. excess of G' ≥ 6k+1, so by IH `maxEdgeDisjointK4 G' ≥ k+1`.
7. Lift to G via `deleteEdges_le` + edge-disjointness from `deleteEdges_adj`.

**Missing infrastructure**:
- `Clique4.edges.card = 6` (need `Sym2.eq_iff` + 15-way distinctness analysis from
  K.distinct). Tedious but routine.
- Maybe: `maxEdgeDisjointK4_mono_subgraph` — if `G' ≤ G` and family is in G',
  it's in G.

**Tractability**: 6/10 — substantial but no novel mathematics required.

## 2. Sharpness of K₄ Turán bound

**Statement**: For each n ≥ 3, the balanced complete tripartite graph T(n,3)
has exactly `⌊n²/3⌋` edges and is K₄-free, witnessing tightness of `turanK4_extremal`.

**Why this matters**:
- Demonstrates the bound `turanK4_extremal` is best possible.
- Mathlib has `SimpleGraph.turanGraph 3 n` and `turanGraph_cliqueFree` already.
- Edge count needs an argument. This is a sharp boundary phenomenon.

**Proof sketch (formalizable today, ~30 lines)**:
- `SimpleGraph.turanGraph 3 n` from Mathlib; `turanGraph_cliqueFree` gives K₄-free.
- Edge count: `SimpleGraph.turanGraph_edgeFinset_card` or compute directly via
  `Fintype.card_quotient_eq_quot_div` on the equivalence partition.
- Connect to our `turanThresholdK4` definition.

**Tractability**: 7/10 — requires familiarity with Mathlib's `turanGraph` API
but no new mathematics.

## 3. Generalization to K_r for r ≥ 5

**Statement (Open)**: For r ≥ 5 and c > 0, does there exist g_r(c) such that
every n-vertex graph with ≥ ex(n, K_r) + k edges (k < cn) contains
≥ k - g_r(c) edge-disjoint K_r copies?

**Why this matters**:
- The K₃ case (Györi 1988) is solved with f(c) ≪ c².
- The K₄ case is the immediate next step (this problem, oq-02).
- For r ≥ 5 the question is wide open and the difficulty likely grows
  quasi-polynomially in r.
- Structural consequence: if the conjecture holds for some r, the
  Mantel-Turán-style "excess implies clique copies" extends to K_r families.

**Tractability**: 1/10 (open research). But the formalization of the
*statement* and the trivial-rate version (1/binomial(r,2)) is mechanical
once oq-02 is mature.

## Recommended Action

Submit candidate question #1 (trivial linear bound for K₄) as a new pool entry.
Candidate #2 (sharpness) could be folded into the existing oq-02 file as a
follow-up theorem in a future session.
