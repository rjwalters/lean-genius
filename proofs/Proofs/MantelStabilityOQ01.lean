/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

/-!
# Mantel stability — min-degree (Andrásfai–Erdős–Sós) ingredient

`Proofs/MantelTheorem.lean` and `Proofs/MantelTheoremUniqueness.lean` settle the *exact* extremal
form of Mantel's theorem: a triangle-free (`K₃`-free) graph on `n` vertices has at most `⌊n²/4⌋`
edges, the bound is attained by `turanGraph n 2`, and equality holds **iff** the graph is
isomorphic to that balanced complete bipartite graph.

The open question `mantel-theorem-oq-01` asks for the *robust* (Erdős–Simonovits) stability
statement: a triangle-free graph whose edge count is within `o(n²)` of `⌊n²/4⌋` can be made
bipartite by deleting only `o(n²)` edges. That edge-count stability is **not** yet in Mathlib and
is genuinely harder (its standard proof routes through degree-cleaning + the
Andrásfai–Erdős–Sós theorem, or through the triangle removal lemma).

This file packages the first concrete ingredient of the degree-cleaning route, which **is**
available in Mathlib: the triangle-free case of the Andrásfai–Erdős–Sós theorem. Mathlib's general
`SimpleGraph.colorable_of_cliqueFree_lt_minDegree`
(`Mathlib/Combinatorics/SimpleGraph/FiveWheelLike.lean`, Brandt's proof) states that a
`Kᵣ₊₁`-free graph with `(3r-4)·n/(3r-1) < δ(G)` is `r`-colorable. At `r = 2` this is:

> A triangle-free graph on `n` vertices with minimum degree `> 2n/5` is bipartite.

This is a *min-degree* stability statement (high min-degree forces exact bipartiteness), distinct
from the edge-count stability of the open question, but it is the load-bearing lemma in the
cleaning argument: delete vertices of degree `≤ 2n/5` (few enough that few edges are lost when the
graph is dense), then the surviving subgraph satisfies the AES hypothesis and is bipartite.

## Status

ORPHAN, build-pending: not registered in `Proofs.lean`, no gallery entry — so no false "green".
Names were checked against the offline Mathlib checkout at the pinned revision
(`leanprover-community/mathlib4` @ `2df2f0150c`, Lean `v4.26.0`); a Docker build is still required
to confirm it compiles. The two results below are thin specializations of
`SimpleGraph.colorable_of_cliqueFree_lt_minDegree` and carry no new assumptions (0 sorries,
0 axioms by construction).
-/

open Finset Fintype SimpleGraph

namespace MantelStability

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Andrásfai–Erdős–Sós, triangle-free case.** A triangle-free (`K₃`-free) simple graph on `n`
vertices whose minimum degree exceeds `2n/5` is bipartite (`2`-colorable). This is the `r = 2`
specialization of `SimpleGraph.colorable_of_cliqueFree_lt_minDegree`, where the general threshold
`(3r-4)·n/(3r-1)` collapses to `2n/5`. -/
theorem triangleFree_colorable_two_of_lt_minDegree (h3 : G.CliqueFree 3)
    (hd : 2 * Fintype.card V / 5 < G.minDegree) : G.Colorable 2 := by
  refine colorable_of_cliqueFree_lt_minDegree (r := 2) (show G.CliqueFree (2 + 1) from h3) ?_
  -- The instantiated threshold `(3·2-4)·n/(3·2-1)` is literally `2·n/5`.
  omega

/-- Contrapositive form, the shape used by the degree-cleaning step toward edge-count stability:
a triangle-free graph that fails to be bipartite must be **sparse at some vertex**, i.e. its
minimum degree is at most `2n/5`. -/
theorem minDegree_le_of_triangleFree_not_colorable_two (h3 : G.CliqueFree 3)
    (hnb : ¬ G.Colorable 2) : G.minDegree ≤ 2 * Fintype.card V / 5 := by
  by_contra hlt
  push_neg at hlt
  exact hnb (triangleFree_colorable_two_of_lt_minDegree G h3 hlt)

end MantelStability
