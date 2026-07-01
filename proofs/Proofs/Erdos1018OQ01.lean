/-
Erdős Problem #1018 — Open Question OQ-01:
What is the optimal bound on `C_ε` as a function of `ε`?

Erdős #1018 (Kostochka–Pyber, 1988): every graph on `n` vertices with at least
`n^(1+ε)` edges contains a non-planar subgraph (indeed a `K₅`-subdivision) on
`O_ε(1)` vertices.  OQ-01 asks for the optimal dependence of the constant
`C_ε` on `ε`.

The standard quantitative route to such results factors through one elementary,
graph-theoretic reduction that is *independent* of the topological (planarity)
input and controls the whole constant:

  > A graph that is dense on average contains an induced subgraph of large
  > minimum degree.

Precisely (the **degeneracy / min-degree extraction lemma**): if a finite graph
has more than `k · n` edges, then some nonempty vertex set `T` induces a subgraph
in which **every** vertex has more than `k` neighbours inside `T`
(`exists_dense_induced_subgraph`).  Equivalently, average degree `> 2k` forces an
induced subgraph of minimum degree `≥ k+1`.

This is exactly the first step of Kostochka–Pyber and Bollobás–Thomason: the
minimum-degree subgraph is then fed to a topological-clique argument.  Bounding
`C_ε` reduces to bounding how minimum degree converts into a `K₅`-subdivision;
the density-to-min-degree step proved here is the part with the clean optimal
constant (`k+1` from `> k·n` edges is best possible — any `k`-degenerate graph,
e.g. the `k`-th power of a path, has `≤ k·n` edges and no subgraph of minimum
degree `> k`).

Mathlib has `minDegree`, `degree`, and the handshake lemma
`sum_degrees_eq_twice_card_edges`, but not the density ⟹ min-degree subgraph
extraction; this file proves it from scratch.  The topological step — turning the
min-degree subgraph into a small non-planar subgraph — remains the genuinely open
part of OQ-01 and is *not* claimed here.

**Status**: VERIFIED, 0 axioms.  Self-contained.
Reference: https://erdosproblems.com/1018
-/

import Mathlib

open Finset

namespace Erdos1018OQ01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The number of neighbours of `v` that lie inside the vertex set `S`
(the degree of `v` in the subgraph induced on `S`, when `v ∈ S`). -/
def degOn (S : Finset V) (v : V) : ℕ := (S.filter (fun w => G.Adj v w)).card

/-- Twice the number of edges inside `S`: the handshake sum of induced degrees
over `S`. Working with the doubled count keeps everything in `ℕ` with no
division. -/
def edgeSum (S : Finset V) : ℕ := ∑ v ∈ S, degOn G S v

/-- Removing a vertex `v` from the ambient set changes the within-set degree of a
different vertex `u` by exactly `1` if `u ~ v` and `0` otherwise. -/
lemma degOn_erase {S : Finset V} {u v : V} (hvS : v ∈ S) :
    degOn G S u = degOn G (S.erase v) u + (if G.Adj u v then 1 else 0) := by
  classical
  unfold degOn
  have h1 : (S.erase v).filter (fun w => G.Adj u w)
          = (S.filter (fun w => G.Adj u w)).erase v := by
    ext w; simp only [mem_filter, mem_erase]; tauto
  rw [h1]
  by_cases hadj : G.Adj u v
  · have hmem : v ∈ S.filter (fun w => G.Adj u w) := by
      simp only [mem_filter]; exact ⟨hvS, hadj⟩
    rw [card_erase_of_mem hmem, if_pos hadj]
    have hpos : 1 ≤ (S.filter (fun w => G.Adj u w)).card := card_pos.mpr ⟨v, hmem⟩
    omega
  · have hnmem : v ∉ S.filter (fun w => G.Adj u w) := by
      simp only [mem_filter, not_and]; intro _; exact hadj
    rw [erase_eq_of_notMem hnmem, if_neg hadj, Nat.add_zero]

/-- **Edge-deletion identity.** Removing a vertex `v ∈ S` decreases the doubled
edge count `edgeSum` by exactly twice the within-`S` degree of `v`. -/
lemma edgeSum_erase {S : Finset V} {v : V} (hvS : v ∈ S) :
    edgeSum G S = edgeSum G (S.erase v) + 2 * degOn G S v := by
  classical
  simp only [edgeSum]
  rw [← Finset.sum_erase_add S (fun x => degOn G S x) hvS]
  have hstep : ∑ x ∈ S.erase v, degOn G S x
      = (∑ x ∈ S.erase v, degOn G (S.erase v) x)
        + ∑ x ∈ S.erase v, (if G.Adj x v then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    exact degOn_erase G hvS
  have hfilter : (S.erase v).filter (fun u => G.Adj u v)
               = S.filter (fun w => G.Adj v w) := by
    ext w; simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨_, hwS⟩, hadj⟩; exact ⟨hwS, G.symm hadj⟩
    · rintro ⟨hwS, hadj⟩; exact ⟨⟨hadj.ne', hwS⟩, G.symm hadj⟩
  have hcount : ∑ x ∈ S.erase v, (if G.Adj x v then 1 else 0) = degOn G S v := by
    unfold degOn
    rw [← card_filter, hfilter]
  rw [hstep, hcount]
  ring

/-- The doubled edge count over the whole vertex set is `2·#edges` (handshake). -/
lemma edgeSum_univ : edgeSum G univ = 2 * G.edgeFinset.card := by
  unfold edgeSum
  have hdeg : ∀ v, degOn G univ v = G.degree v := by
    intro v
    rw [degOn, SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  simp_rw [hdeg]
  exact G.sum_degrees_eq_twice_card_edges

/-- **Degeneracy / min-degree extraction (set form).**
If `S` carries more than `k·|S|` edges (`2·(k·|S|) < edgeSum S`), then some
nonempty `T ⊆ S` induces a subgraph of minimum degree `> k`: every vertex of `T`
has more than `k` neighbours inside `T`. Proved by repeatedly deleting a vertex
of small within-set degree; the density invariant `2·(k·|·|) < edgeSum` is
preserved at each deletion and forces nonemptiness. -/
lemma exists_min_degOn (k : ℕ) :
    ∀ S : Finset V, 2 * (k * S.card) < edgeSum G S →
      ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T, k < degOn G T v := by
  intro S
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro hS
    by_cases hmin : ∀ v ∈ S, k < degOn G S v
    · refine ⟨S, subset_rfl, ?_, hmin⟩
      rcases S.eq_empty_or_nonempty with rfl | hne
      · simp [edgeSum] at hS
      · exact hne
    · push_neg at hmin
      obtain ⟨v, hvS, hdeg⟩ := hmin
      have hsub : S.erase v ⊂ S := erase_ssubset hvS
      have hsplit : edgeSum G S = edgeSum G (S.erase v) + 2 * degOn G S v :=
        edgeSum_erase G hvS
      have hcard : S.card = (S.erase v).card + 1 := by
        rw [card_erase_of_mem hvS]
        have : 1 ≤ S.card := card_pos.mpr ⟨v, hvS⟩
        omega
      have hP : k * S.card = k * (S.erase v).card + k := by
        rw [hcard]; ring
      have hkey : 2 * (k * (S.erase v).card) < edgeSum G (S.erase v) := by omega
      obtain ⟨T, hTsub, hTne, hTmin⟩ := ih _ hsub hkey
      exact ⟨T, hTsub.trans (erase_subset _ _), hTne, hTmin⟩

/-- **Density forces a dense induced subgraph.**
If `G` has more than `k · n` edges (`n = |V|`), then there is a nonempty set of
vertices `T` in which every vertex has more than `k` neighbours inside `T`.
Equivalently: average degree `> 2k` ⟹ an induced subgraph of minimum degree
`≥ k+1`. This is the density-to-min-degree reduction underlying the optimal
constant in Erdős #1018 (Kostochka–Pyber). The bound is best possible:
`k`-degenerate graphs have `≤ k·n` edges and no such subgraph. -/
theorem exists_dense_induced_subgraph {k : ℕ}
    (h : k * Fintype.card V < G.edgeFinset.card) :
    ∃ T : Finset V, T.Nonempty ∧ ∀ v ∈ T, k < degOn G T v := by
  obtain ⟨T, -, hTne, hTmin⟩ := exists_min_degOn G k univ <| by
    rw [edgeSum_univ G, card_univ]; omega
  exact ⟨T, hTne, hTmin⟩

end Erdos1018OQ01
