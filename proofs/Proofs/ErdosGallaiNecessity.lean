/-
# Erdős–Gallai: the necessity (counting) core

## Problem (handshake-lemma-oq-02)
The Erdős–Gallai theorem characterises which non-increasing sequences
`d₁ ≥ d₂ ≥ ⋯ ≥ dₙ ≥ 0` are *graphical* (are the degree sequence of some finite
simple graph): the sum must be even and, for every `k`,

  `∑_{i≤k} dᵢ ≤ k(k-1) + ∑_{i>k} min(dᵢ, k)`.

The hard direction is **sufficiency** (these inequalities let one *build* a graph,
e.g. via a Havel–Hakimi / edge-swap argument). This file proves the **necessity**
direction in its sharpest, sorting-free form: the inequality holds for *every*
vertex subset `A`, not just the top-`k` by degree. Specialising `A` to the `k`
highest-degree vertices of a graph realising a sorted sequence recovers the
classical statement.

## Main result
`erdos_gallai_necessity` : for a finite simple graph `G` and any `A : Finset V`,

  `∑_{v ∈ A} G.degree v ≤ |A|·(|A|-1) + ∑_{w ∈ Aᶜ} min (G.degree w) |A|`.

The proof is the standard two-part count:
* edges inside `A` contribute `∑_{v∈A} |N(v) ∩ A| ≤ |A|·(|A|-1)` (each vertex has
  at most `|A|-1` neighbours inside `A`);
* edges from `A` to its complement are counted from the `Aᶜ` side via a
  double-counting swap, `∑_{v∈A} |N(v) ∩ Aᶜ| = ∑_{w∈Aᶜ} |N(w) ∩ A|`, and each
  `|N(w) ∩ A| ≤ min (G.degree w) |A|`.

`Even`-ness of `∑ v, G.degree v` (the other necessity condition) is the handshake
lemma, already in the gallery (`HandshakeLemma.even_sum_degrees`).

Sorry-free and axiom-free.
-/
import Mathlib

namespace ErdosGallaiNecessity

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Neighbours of `v` lying inside the finset `s`. -/
private def nbrIn (v : V) (s : Finset V) : Finset V := s.filter (fun w => G.Adj v w)

/-- The degree of `v` splits as (neighbours in `A`) + (neighbours outside `A`). -/
theorem degree_eq_nbr_add_nbr_compl (v : V) (A : Finset V) :
    G.degree v = (nbrIn G v A).card + (nbrIn G v Aᶜ).card := by
  classical
  have hfilter : G.neighborFinset v = Finset.univ.filter (fun w => G.Adj v w) := by
    ext w; simp [SimpleGraph.mem_neighborFinset]
  have hdeg : G.degree v = (Finset.univ.filter (fun w => G.Adj v w)).card := by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, hfilter]
  have huniv : (Finset.univ.filter (fun w => G.Adj v w))
      = (nbrIn G v A) ∪ (nbrIn G v Aᶜ) := by
    unfold nbrIn
    rw [← Finset.filter_union, Finset.union_compl]
  have hdisj : Disjoint (nbrIn G v A) (nbrIn G v Aᶜ) := by
    unfold nbrIn
    exact (Finset.disjoint_filter_filter (disjoint_compl_right))
  rw [hdeg, huniv, Finset.card_union_of_disjoint hdisj]

omit [Fintype V] in
/-- A vertex `v ∈ A` has at most `|A|-1` neighbours inside `A` (it is not its own
neighbour, so its `A`-neighbours lie in `A.erase v`). -/
theorem card_nbrIn_le {v : V} {A : Finset V} (hv : v ∈ A) :
    (nbrIn G v A).card ≤ A.card - 1 := by
  classical
  have hsub : nbrIn G v A ⊆ A.erase v := by
    intro w hw
    unfold nbrIn at hw
    rw [Finset.mem_filter] at hw
    rw [Finset.mem_erase]
    refine ⟨?_, hw.1⟩
    rintro rfl
    exact (SimpleGraph.irrefl G) hw.2
  calc (nbrIn G v A).card ≤ (A.erase v).card := Finset.card_le_card hsub
    _ = A.card - 1 := Finset.card_erase_of_mem hv

/-- Double-counting swap for the `A`–`Aᶜ` edges:
`∑_{v∈A} |N(v) ∩ Aᶜ| = ∑_{w∈Aᶜ} |N(w) ∩ A|`. -/
theorem sum_cross_swap (A : Finset V) :
    ∑ v ∈ A, (nbrIn G v Aᶜ).card = ∑ w ∈ Aᶜ, (nbrIn G w A).card := by
  classical
  have hL : ∀ v, (nbrIn G v Aᶜ).card
      = ∑ w ∈ Aᶜ, (if G.Adj v w then 1 else 0) := by
    intro v; unfold nbrIn; rw [Finset.card_filter]
  have hR : ∀ w, (nbrIn G w A).card
      = ∑ v ∈ A, (if G.Adj w v then 1 else 0) := by
    intro w; unfold nbrIn; rw [Finset.card_filter]
  simp only [hL, hR]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro v _
  simp [SimpleGraph.adj_comm]

/-- **Erdős–Gallai, necessity (subset form).**
For any finite simple graph `G` and any vertex subset `A`,
`∑_{v∈A} deg v ≤ |A|·(|A|-1) + ∑_{w∈Aᶜ} min (deg w) |A|`.
This is the counting inequality every graphical sequence must satisfy; taking `A`
to be the `k` highest-degree vertices gives the classical Erdős–Gallai bound. -/
theorem erdos_gallai_necessity (A : Finset V) :
    ∑ v ∈ A, G.degree v
      ≤ A.card * (A.card - 1) + ∑ w ∈ Aᶜ, min (G.degree w) A.card := by
  classical
  -- Split each degree into inside-A and outside-A parts.
  have hsplit : ∑ v ∈ A, G.degree v
      = (∑ v ∈ A, (nbrIn G v A).card) + (∑ v ∈ A, (nbrIn G v Aᶜ).card) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v _ => degree_eq_nbr_add_nbr_compl G v A)
  -- Inside part ≤ |A|·(|A|-1).
  have hinside : ∑ v ∈ A, (nbrIn G v A).card ≤ A.card * (A.card - 1) := by
    calc ∑ v ∈ A, (nbrIn G v A).card
        ≤ ∑ _v ∈ A, (A.card - 1) := Finset.sum_le_sum (fun v hv => card_nbrIn_le G hv)
      _ = A.card * (A.card - 1) := by rw [Finset.sum_const, smul_eq_mul]
  -- Cross part = ∑_{w∈Aᶜ} |N(w)∩A| ≤ ∑_{w∈Aᶜ} min (deg w) |A|.
  have hcross : ∑ v ∈ A, (nbrIn G v Aᶜ).card ≤ ∑ w ∈ Aᶜ, min (G.degree w) A.card := by
    rw [sum_cross_swap G A]
    apply Finset.sum_le_sum
    intro w _
    apply le_min
    · -- |N(w) ∩ A| ≤ deg w
      have : nbrIn G w A ⊆ G.neighborFinset w := by
        intro x hx
        unfold nbrIn at hx
        rw [Finset.mem_filter] at hx
        rw [SimpleGraph.mem_neighborFinset]
        exact hx.2
      calc (nbrIn G w A).card ≤ (G.neighborFinset w).card := Finset.card_le_card this
        _ = G.degree w := SimpleGraph.card_neighborFinset_eq_degree G w
    · -- |N(w) ∩ A| ≤ |A|
      have : nbrIn G w A ⊆ A := by
        intro x hx; unfold nbrIn at hx; exact (Finset.mem_filter.mp hx).1
      exact Finset.card_le_card this
  rw [hsplit]
  omega

-- Axiom audit: only the foundational propext / Classical.choice / Quot.sound.
-- No sorryAx, no Lean.ofReduceBool.
#print axioms erdos_gallai_necessity

end ErdosGallaiNecessity
