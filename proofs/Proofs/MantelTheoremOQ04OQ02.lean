/-
Copyright (c) 2024-2026 lean-genius contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Proofs.MantelTheoremOQ04

/-!
# Mantel's Theorem — Sharpness of the Bound: `⌊n²/4⌋` is Attained

`Proofs/MantelTheoremUniqueness.lean` proves Mantel's *equality characterization*
(`mantel_equality_iff`): a triangle-free graph on `n` vertices attains the maximum
`⌊n²/4⌋` edges **iff** it is isomorphic to `turanGraph n 2`; and
`Proofs/MantelTheoremOQ04.lean` identifies that extremal graph concretely as the balanced
complete bipartite graph `K_{⌈n/2⌉,⌊n/2⌋}`.

Both of those statements are *conditional* — "if a graph attains the maximum, then …".
What is missing is the **sharpness/tightness** half: that the bound `⌊n²/4⌋` is actually
**attained**, i.e. there genuinely exists a triangle-free graph on `n` vertices with exactly
`⌊n²/4⌋` edges. Without it, `⌊n²/4⌋` could a priori be a non-tight upper bound. This file
supplies the missing existence direction by computing the edge count of the extremal graph
explicitly.

This answers the second open question posed by `mantel-theorem-oq-04`:
> Prove `#E(K_{⌈n/2⌉,⌊n/2⌋}) = ⌈n/2⌉·⌊n/2⌋ = ⌊n²/4⌋` for a self-contained complete-bipartite
> tightness proof.

## Main results

* `card_edgeFinset_completeBipartiteGraph` : `#E(K_{V,W}) = |V| · |W|`. The basic edge-count
  formula for a complete bipartite graph, proved via the degree-sum (handshake) formula. (No
  such lemma exists in Mathlib; cf. `card_edgeFinset_completeEquipartiteGraph` for the
  equipartite multipartite analogue.)
* `half_succ_mul_half` : `⌈n/2⌉ · ⌊n/2⌋ = ⌊n²/4⌋`, the arithmetic identity behind the bound.
* `card_edgeFinset_turanGraphTwo` : `#E(turanGraph n 2) = ⌊n²/4⌋` — the extremal graph has
  exactly the Mantel-maximal number of edges.
* `mantel_bound_attained` : `turanGraph n 2` is triangle-free **and** has exactly `⌊n²/4⌋`
  edges. Together with `mantel_card_edgeFinset_le` (the upper bound) this makes Mantel's
  bound provably sharp.

## Proof outline

The edge count of `K_{V,W}` follows from the handshake formula
`∑ v, deg v = 2 · #E`: every left vertex has degree `|W|` and every right vertex degree `|V|`,
so the degree sum is `|V|·|W| + |W|·|V| = 2·|V|·|W|`. The arithmetic identity
`⌈n/2⌉·⌊n/2⌋ = ⌊n²/4⌋` is a two-case parity computation. The extremal edge count then
transports along the isomorphism `turanGraphTwoIsoCompleteBipartite` (edge counts are
isomorphism invariants), and triangle-freeness comes from the parity 2-colouring
`v ↦ v % 2` (a `2`-colourable graph is `K₃`-free).
-/

open Finset Fintype SimpleGraph

namespace Mantel

open scoped Classical

variable {V W : Type*} [Fintype V] [Fintype W]

/-- The neighbours of a left vertex in `K_{V,W}` are exactly the right vertices. -/
theorem neighborFinset_completeBipartiteGraph_inl (i : V) :
    (completeBipartiteGraph V W).neighborFinset (Sum.inl i) = univ.image Sum.inr := by
  ext x
  cases x <;> simp [mem_neighborFinset]

/-- The neighbours of a right vertex in `K_{V,W}` are exactly the left vertices. -/
theorem neighborFinset_completeBipartiteGraph_inr (j : W) :
    (completeBipartiteGraph V W).neighborFinset (Sum.inr j) = univ.image Sum.inl := by
  ext x
  cases x <;> simp [mem_neighborFinset]

/-- Every left vertex of `K_{V,W}` has degree `|W|`. -/
theorem degree_completeBipartiteGraph_inl (i : V) :
    (completeBipartiteGraph V W).degree (Sum.inl i) = Fintype.card W := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_completeBipartiteGraph_inl,
    card_image_of_injective _ Sum.inr_injective, card_univ]

/-- Every right vertex of `K_{V,W}` has degree `|V|`. -/
theorem degree_completeBipartiteGraph_inr (j : W) :
    (completeBipartiteGraph V W).degree (Sum.inr j) = Fintype.card V := by
  rw [← card_neighborFinset_eq_degree, neighborFinset_completeBipartiteGraph_inr,
    card_image_of_injective _ Sum.inl_injective, card_univ]

/-- **Edge count of a complete bipartite graph.** `K_{V,W}` has exactly `|V| · |W|` edges.
Proved from the handshake formula: the degree sum is `|V|·|W| + |W|·|V| = 2·|V|·|W|`. -/
theorem card_edgeFinset_completeBipartiteGraph :
    #(completeBipartiteGraph V W).edgeFinset = Fintype.card V * Fintype.card W := by
  have h := (completeBipartiteGraph V W).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at h
  simp only [degree_completeBipartiteGraph_inl, degree_completeBipartiteGraph_inr,
    Finset.sum_const, card_univ, smul_eq_mul] at h
  rw [mul_comm (Fintype.card W) (Fintype.card V)] at h
  omega

/-- Specialisation to `Fin a ⊕ Fin b`: `#E(K_{a,b}) = a · b`. -/
theorem card_edgeFinset_completeBipartiteGraph_fin (a b : ℕ) :
    #(completeBipartiteGraph (Fin a) (Fin b)).edgeFinset = a * b := by
  rw [card_edgeFinset_completeBipartiteGraph, Fintype.card_fin, Fintype.card_fin]

/-- **The balanced-bipartite arithmetic identity** `⌈n/2⌉ · ⌊n/2⌋ = ⌊n²/4⌋`, by parity cases. -/
theorem half_succ_mul_half (n : ℕ) : ((n + 1) / 2) * (n / 2) = n ^ 2 / 4 := by
  rcases Nat.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · -- `n = m + m`
    have e1 : (m + m + 1) / 2 = m := by omega
    have e2 : (m + m) / 2 = m := by omega
    rw [e1, e2, pow_two]
    have hsq : (m + m) * (m + m) = 4 * (m * m) := by ring
    rw [hsq, Nat.mul_div_cancel_left _ (by norm_num : (0 : ℕ) < 4)]
  · -- `n = 2 * m + 1`
    have e1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have e2 : (2 * m + 1) / 2 = m := by omega
    rw [e1, e2, pow_two]
    have hsq : (2 * m + 1) * (2 * m + 1) = 4 * ((m + 1) * m) + 1 := by ring
    rw [hsq]
    omega

/-- **The Mantel/Turán extremal graph attains `⌊n²/4⌋` edges.** The edge count transports along
`turanGraphTwoIsoCompleteBipartite` and equals `⌈n/2⌉ · ⌊n/2⌋ = ⌊n²/4⌋`. -/
theorem card_edgeFinset_turanGraphTwo (n : ℕ) :
    #(turanGraph n 2).edgeFinset = n ^ 2 / 4 := by
  rw [← (turanGraphTwoIsoCompleteBipartite n).card_edgeFinset_eq,
    card_edgeFinset_completeBipartiteGraph_fin, half_succ_mul_half]

/-- The Mantel/Turán extremal graph is triangle-free: the parity 2-colouring `v ↦ v % 2`
makes it `2`-colourable, and a `2`-colourable graph is `K₃`-free. -/
theorem turanGraphTwo_cliqueFree_three (n : ℕ) : (turanGraph n 2).CliqueFree 3 := by
  have hcol : (turanGraph n 2).Colorable 2 := by
    refine ⟨Coloring.mk (fun v => (⟨(v : ℕ) % 2, by omega⟩ : Fin 2)) ?_⟩
    intro v w hadj heq
    rw [turanGraph_adj] at hadj
    exact hadj (by simpa using heq)
  exact hcol.cliqueFree (by norm_num)

/-- **Sharpness of Mantel's theorem.** For every `n`, the extremal graph `turanGraph n 2`
(equivalently `K_{⌈n/2⌉,⌊n/2⌋}`) is triangle-free and has exactly `⌊n²/4⌋` edges. Combined with
the upper bound `mantel_card_edgeFinset_le`, this shows the Mantel bound `⌊n²/4⌋` is attained —
the missing existence/tightness direction of the equality characterisation. -/
theorem mantel_bound_attained (n : ℕ) :
    (turanGraph n 2).CliqueFree 3 ∧ #(turanGraph n 2).edgeFinset = n ^ 2 / 4 :=
  ⟨turanGraphTwo_cliqueFree_three n, card_edgeFinset_turanGraphTwo n⟩

end Mantel
