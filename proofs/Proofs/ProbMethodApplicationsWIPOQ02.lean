/-
  Probabilistic Method Applications — WIP OQ-02

  Open question (prob-method-applications-wip-01-oq-02):
    "Formalize Property B (m(k) ≥ 2^(k-1)) directly from the abstract
     first-moment engine `exists_good_of_card_bound` / `ramsey_avoidance`."

  The companion file `ProbMethodApplicationsWIP.lean` proves the abstract
  first-moment avoidance engine

      ProbMethod.Core.ramsey_avoidance :
        (cliques : Finset (Finset E)) (m : ℕ)
        (∀ K ∈ cliques, K.card = m)
        (cliques.card * 2^(|E| - m + 1) < 2^|E|)
        ⟹ ∃ S : Finset E, ∀ K ∈ cliques, ¬ (K ⊆ S ∨ Disjoint K S),

  over an arbitrary finite "ground" set `E`, where a block `K` is monochromatic
  under the colouring `S` (= the set of `true`-coloured ground elements) exactly
  when `K ⊆ S` (all `true`) or `Disjoint K S` (all `false`).

  Its docstring advertises a *Ramsey* reading (`E` = the edge set of `Kₙ`,
  blocks = the `Kₘ`-cliques), carried out in `ProbMethodApplicationsWIPOQ01`.
  This file supplies the *other* headline consequence of the same engine —
  **Property B**, the 2-colourability threshold for uniform hypergraphs.

  Reading of the engine for Property B:
    * take `E := V`, the **vertex** set of a hypergraph (not the edge set of
      `Kₙ`);
    * take `cliques := edges`, the family of hyperedges, each a `k`-element
      subset of `V`;
    * a colouring `S : Finset V` splits `V` into `true`/`false` classes, and a
      hyperedge `e` is monochromatic exactly when `e ⊆ S ∨ Disjoint e S`.
  The engine's hypothesis `edges.card · 2^(|V| - k + 1) < 2^|V|` is equivalent,
  since `2^|V| = 2^(k-1)·2^(|V|-k+1)` for `k ≤ |V|`, to the classical Property B
  criterion `edges.card < 2^(k-1)`.  The engine then produces a proper
  2-colouring, i.e. one with no monochromatic edge.

  Consequences proved here (both `0 sorry`, `0 axiom`):
    * `property_B_two_colorable` — every `k`-uniform hypergraph with fewer than
      `2^(k-1)` edges is 2-colourable;
    * `property_B_lower_bound`   — its contrapositive, **m(k) ≥ 2^(k-1)**: every
      `k`-uniform hypergraph that is *not* 2-colourable has at least `2^(k-1)`
      edges (Erdős, 1963/64).

  `m(k)` denotes the least number of edges in a non-2-colourable `k`-uniform
  hypergraph; the lower bound `m(k) ≥ 2^(k-1)` is exactly the statement that no
  hypergraph below that edge count can fail to be 2-colourable, which is what
  `property_B_lower_bound` asserts (uniformly over all vertex types `V`).

  Status: 0 sorries, 0 axioms, no native_decide.
-/
import Mathlib
import Proofs.ProbMethodApplicationsWIP

open Finset

namespace ProbMethod.PropertyB

open ProbMethod.Core

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A hypergraph `edges` on vertex set `V` is **2-colourable** (has *Property B*)
when some 2-colouring `S : Finset V` (the vertices coloured `true`) leaves no
hyperedge monochromatic.  A hyperedge `e` is monochromatic under `S` exactly
when `ProbMethod.Core.Mono e S`, i.e. `e ⊆ S` (all `true`) or `Disjoint e S`
(all `false`). -/
def TwoColorable (edges : Finset (Finset V)) : Prop :=
  ∃ S : Finset V, ∀ e ∈ edges, ¬ Mono e S

/-- **Property B (Erdős 1963/64), upper form.**
Every `k`-uniform hypergraph on `V` with strictly fewer than `2^(k-1)` edges is
2-colourable.

The proof is a direct instantiation of the abstract union-bound engine
`ProbMethod.Core.ramsey_avoidance` with the *vertex* set `V` as ground set: the
only arithmetic content is turning the classical criterion `edges.card < 2^(k-1)`
into the engine's hypothesis `edges.card · 2^(|V|-k+1) < 2^|V|`, using
`2^|V| = 2^(k-1)·2^(|V|-k+1)` (valid since a nonempty `k`-edge forces `k ≤ |V|`). -/
theorem property_B_two_colorable
    (edges : Finset (Finset V)) (k : ℕ) (hk : 1 ≤ k)
    (huniform : ∀ e ∈ edges, e.card = k)
    (hsmall : edges.card < 2 ^ (k - 1)) :
    TwoColorable edges := by
  rcases edges.eq_empty_or_nonempty with hE | hE
  · -- No edges: any colouring is proper.
    exact ⟨∅, by simp [hE]⟩
  · -- A witnessing edge pins `k ≤ |V|`, which drives the exponent bookkeeping.
    obtain ⟨e₀, he₀⟩ := hE
    have hkn : k ≤ Fintype.card V := by
      have h1 := Finset.card_le_univ e₀
      rwa [huniform e₀ he₀] at h1
    have hpos : 0 < 2 ^ (Fintype.card V - k + 1) := pow_pos (by norm_num) _
    have hmul : edges.card * 2 ^ (Fintype.card V - k + 1)
        < 2 ^ (k - 1) * 2 ^ (Fintype.card V - k + 1) :=
      mul_lt_mul_of_pos_right hsmall hpos
    have hlt : edges.card * 2 ^ (Fintype.card V - k + 1) < 2 ^ (Fintype.card V) := by
      refine hmul.trans_le (le_of_eq ?_)
      rw [← pow_add]
      congr 1
      omega
    exact ramsey_avoidance edges k huniform hlt

/-- **Property B lower bound: m(k) ≥ 2^(k-1).**
Every `k`-uniform hypergraph on `V` that is *not* 2-colourable has at least
`2^(k-1)` hyperedges.

This is the contrapositive of `property_B_two_colorable`.  Since it holds for
every finite vertex type `V`, it is exactly the Erdős lower bound on
`m(k)`, the minimum number of edges in a non-2-colourable `k`-uniform
hypergraph: no such hypergraph can have fewer than `2^(k-1)` edges. -/
theorem property_B_lower_bound
    (edges : Finset (Finset V)) (k : ℕ) (hk : 1 ≤ k)
    (huniform : ∀ e ∈ edges, e.card = k)
    (hnot : ¬ TwoColorable edges) :
    2 ^ (k - 1) ≤ edges.card := by
  by_contra h
  push_neg at h
  exact hnot (property_B_two_colorable edges k hk huniform h)

end ProbMethod.PropertyB
