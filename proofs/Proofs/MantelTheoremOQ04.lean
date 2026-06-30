/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Proofs.MantelTheorem
import Proofs.MantelTheoremUniqueness

/-!
# Mantel's Theorem — Complete-Bipartite Form of the Extremal Graph

`Proofs/MantelTheoremUniqueness.lean` proves the Mantel equality characterization
(`mantel_equality_iff`): a triangle-free graph on `n` vertices attains the maximum
`⌊n²/4⌋` edges **iff** it is isomorphic to Mathlib's canonical Turán graph
`turanGraph n 2` (adjacency `v % 2 ≠ w % 2` on `Fin n`).

That phrasing names the extremal graph abstractly. The *classical* statement of
Mantel's theorem identifies it concretely as the **balanced complete bipartite graph**
`K_{⌈n/2⌉,⌊n/2⌋}`. This file supplies that identification and re-states the equality
characterization in complete-bipartite form.

## Main results

* `turanGraphTwoIsoCompleteBipartite` : `completeBipartiteGraph (Fin ⌈n/2⌉) (Fin ⌊n/2⌋) ≃g
  turanGraph n 2`. The two parts are the even-index and odd-index vertices of `Fin n`.
* `mantel_equality_iff_completeBipartite` : a triangle-free `G` has exactly `⌊n²/4⌋` edges
  **iff** `G ≃g K_{⌈n/2⌉,⌊n/2⌋}` — the full extremal form of Mantel's theorem with the
  unique extremal graph named explicitly.

## Why this is not already in Mathlib

Mathlib's `completeEquipartiteGraph.turanGraph` gives `completeEquipartiteGraph r t ≃g
turanGraph (r * t) r`, i.e. the *equipartite* case with all parts equal — it requires
`n = r * t`. For general `n` (odd `n` in particular) the two parts of `turanGraph n 2`
have **unequal** sizes `⌈n/2⌉ = ⌊n/2⌋ + 1`, which the equipartite isomorphism does not
cover. The interleaved parity bijection below handles arbitrary `n`.

## Proof of the isomorphism

The vertices of `turanGraph n 2` are `Fin n` with two adjacency classes by parity:
even indices (there are `⌈n/2⌉ = (n+1)/2` of them) and odd indices (`⌊n/2⌋ = n/2`).
Two vertices are adjacent iff their parities differ. The map

* `inl k ↦ 2 * k`  (the `k`-th even index),
* `inr k ↦ 2 * k + 1`  (the `k`-th odd index)

is a bijection `Fin ⌈n/2⌉ ⊕ Fin ⌊n/2⌋ ≃ Fin n` carrying "different side of the bipartition"
to "different parity", i.e. carrying complete-bipartite adjacency to `turanGraph n 2`
adjacency. All `Fin`/divmod side conditions are discharged by `omega`.
-/

open Finset Fintype SimpleGraph

namespace Mantel

/-- The interleaved parity bijection `Fin ⌈n/2⌉ ⊕ Fin ⌊n/2⌋ ≃ Fin n`: the left part enumerates
the even indices `2*k`, the right part the odd indices `2*k + 1`. -/
def binEquiv (n : ℕ) : Fin ((n + 1) / 2) ⊕ Fin (n / 2) ≃ Fin n where
  toFun := Sum.elim (fun k => ⟨2 * k, by have := k.2; omega⟩)
                    (fun k => ⟨2 * k + 1, by have := k.2; omega⟩)
  invFun := fun v =>
    if h : (v : ℕ) % 2 = 0 then Sum.inl ⟨v / 2, by have := v.2; omega⟩
    else Sum.inr ⟨v / 2, by have := v.2; omega⟩
  left_inv := by
    rintro (⟨k, hk⟩ | ⟨k, hk⟩)
    · simp only [Sum.elim_inl]
      rw [dif_pos (by simp)]
      simp only [Sum.inl.injEq, Fin.mk.injEq]
      omega
    · simp only [Sum.elim_inr]
      rw [dif_neg (by simp)]
      simp only [Sum.inr.injEq, Fin.mk.injEq]
      omega
  right_inv := by
    rintro ⟨v, hv⟩
    dsimp only
    by_cases h : v % 2 = 0
    · rw [dif_pos h]
      simp only [Sum.elim_inl, Fin.mk.injEq]
      omega
    · rw [dif_neg h]
      simp only [Sum.elim_inr, Fin.mk.injEq]
      omega

/-- **The balanced complete bipartite graph is the Mantel/Turán extremal graph.**
`turanGraph n 2` is isomorphic to `K_{⌈n/2⌉,⌊n/2⌋}`, the complete bipartite graph whose parts
are the even-index and odd-index vertices. Generalizes Mathlib's equipartite
`completeEquipartiteGraph.turanGraph` to arbitrary (possibly odd) `n`. -/
def turanGraphTwoIsoCompleteBipartite (n : ℕ) :
    completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2)) ≃g turanGraph n 2 where
  toEquiv := binEquiv n
  map_rel_iff' := by
    rintro (a | a) (b | b) <;>
      simp [binEquiv, turanGraph_adj, completeBipartiteGraph_adj, Nat.mul_add_mod] <;>
      omega

/-- **Mantel's theorem, complete-bipartite equality characterization.** A triangle-free graph
`G` on `n` vertices has exactly `⌊n²/4⌋` edges **iff** it is isomorphic to the balanced complete
bipartite graph `K_{⌈n/2⌉,⌊n/2⌋}`. This is the classical extremal form of Mantel's theorem with
the unique extremal graph named explicitly, sharpening `mantel_equality_iff` (which names it as
the abstract `turanGraph n 2`). -/
theorem mantel_equality_iff_completeBipartite {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (h : G.CliqueFree 3) :
    G.edgeFinset.card = (Fintype.card V) ^ 2 / 4 ↔
      Nonempty (G ≃g completeBipartiteGraph
        (Fin ((Fintype.card V + 1) / 2)) (Fin (Fintype.card V / 2))) := by
  rw [mantel_equality_iff G h]
  exact ⟨fun ⟨f⟩ => ⟨f.trans (turanGraphTwoIsoCompleteBipartite _).symm⟩,
         fun ⟨f⟩ => ⟨f.trans (turanGraphTwoIsoCompleteBipartite _)⟩⟩

end Mantel
