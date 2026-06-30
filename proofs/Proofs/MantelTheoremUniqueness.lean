/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Proofs.MantelTheorem

/-!
# Mantel's Theorem — Equality Characterization (Uniqueness)

The companion entry `Proofs/MantelTheorem.lean` proves the Mantel edge bound
`#G.edgeFinset ≤ ⌊n²/4⌋` for triangle-free `G` (`mantel_card_edgeFinset_le`) and its
sharpness (`mantel_bound_is_tight`), but explicitly defers the **equality characterization**
to a future direction.

This file packages that characterization: a triangle-free graph on `n` vertices attains the
maximum `⌊n²/4⌋` edges **iff** it is isomorphic to the balanced complete bipartite graph
`turanGraph n 2`. This is the full extremal form of Mantel's theorem (the `r = 2` case of the
uniqueness half of Turán's theorem).

## Proof

The bridge is `SimpleGraph.IsTuranMaximal 2 = IsExtremal (CliqueFree · 3)`, i.e. being a
triangle-free graph with the maximum possible number of edges.

* **Forward.** If `#G.edgeFinset = ⌊n²/4⌋`, then `G` is `IsTuranMaximal 2`: it is triangle-free
  (hypothesis), and every triangle-free `G'` has `#G'.edgeFinset ≤ ⌊n²/4⌋ = #G.edgeFinset` by
  `Mantel.mantel_card_edgeFinset_le`. Mathlib's Turán uniqueness
  `SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph` then yields the isomorphism.
* **Reverse.** A graph isomorphism preserves the edge count
  (`SimpleGraph.Iso.card_edgeFinset_eq`), and `turanGraph n 2` has exactly `⌊n²/4⌋` edges
  (`Mantel.card_edgeFinset_turanGraph_two`).

## Build status

BUILD GREEN (machine-verified, 7744 jobs, exit 0) via
`docker-build.sh Proofs.MantelTheoremUniqueness` against the pinned revision
(`leanprover-community/mathlib4` @ `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, Lean
`v4.26.0`). Load-bearing Mathlib lemmas: `IsTuranMaximal`, `IsExtremal`
(`p G ∧ ∀ ⦃G'⦄ [DecidableRel G'.Adj], p G' → #G'.edgeFinset ≤ #G.edgeFinset`),
`isTuranMaximal_iff_nonempty_iso_turanGraph`, and `Iso.card_edgeFinset_eq`. Registered in
`Proofs.lean`; 0 sorries, 0 axioms.
-/

open Finset Fintype SimpleGraph

namespace Mantel

/-- **Mantel's theorem, equality characterization.** For a triangle-free (`K₃`-free) simple
graph `G` on `n` vertices, the edge count equals the maximum `⌊n²/4⌋` **iff** `G` is isomorphic
to the balanced complete bipartite graph `turanGraph n 2`. Together with
`mantel_card_edgeFinset_le` this is the complete extremal statement of Mantel's theorem. -/
theorem mantel_equality_iff {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.CliqueFree 3) :
    G.edgeFinset.card = (Fintype.card V) ^ 2 / 4 ↔
      Nonempty (G ≃g turanGraph (Fintype.card V) 2) := by
  rw [← isTuranMaximal_iff_nonempty_iso_turanGraph (show 0 < 2 by norm_num)]
  constructor
  · -- Attaining the maximum makes `G` Turán-maximal.
    intro hcard
    refine ⟨h, fun G' _ hG' => ?_⟩
    calc G'.edgeFinset.card
          ≤ (Fintype.card V) ^ 2 / 4 := mantel_card_edgeFinset_le G' hG'
        _ = G.edgeFinset.card := hcard.symm
  · -- An isomorphism to `turanGraph n 2` transfers its exact edge count `⌊n²/4⌋`.
    intro hmax
    obtain ⟨f⟩ := (isTuranMaximal_iff_nonempty_iso_turanGraph (show 0 < 2 by norm_num)).mp hmax
    rw [f.card_edgeFinset_eq, card_edgeFinset_turanGraph_two]

end Mantel
