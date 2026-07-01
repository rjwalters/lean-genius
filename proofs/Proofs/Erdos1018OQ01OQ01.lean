/-
Erdős Problem #1018 — Open Question OQ-01, follow-up OQ-01-OQ-01:
Sharpness of the degeneracy / density edge threshold.

The parent entry (`Erdos1018OQ01`, Kostochka–Pyber first reduction) proves the
**density ⟹ dense-subgraph** extraction lemma:

  > if a finite graph has more than `k · n` edges, then some nonempty vertex set
  > induces a subgraph of minimum degree `> k`.

Its docstring *asserts* that the linear constant `k` is best possible —
"`k`-degenerate graphs have `≤ k·n` edges and no such subgraph" — but does not
prove it. This file supplies the two missing halves.

**1. Converse edge bound (`degenerate_edge_bound`).** If a graph is
`k`-degenerate (every nonempty vertex set induces a vertex of within-degree
`≤ k`), then it has at most `k · n` edges. This is the exact contrapositive of
the extraction theorem, and pins the *upper* side of the threshold.

**2. Extremal witness (`splitGraph_sharp`).** The complete split graph
`S_{n,k} = K_k ∨ \overline{K_{n-k}}` — the first `k` vertices universal, the rest
an independent set — is `k`-degenerate and has exactly `k·n − C(k+1,2)` edges.
So the coefficient `k` cannot be lowered, and the additive slack between the
proven bound `k·n` and the true extremal count is exactly `C(k+1,2)`.

Together: the degeneracy edge bound `≤ k·n` is optimal in its linear coefficient,
with a `C(k+1,2)` additive gap that the split graph realises. The witness needs
no vertex ordering (unlike a `k`-tree): its `k`-degeneracy is a direct degree
computation, which keeps the whole argument elementary and finite.

**Status**: VERIFIED, 0 axioms. Self-contained (builds on `Erdos1018OQ01`).
Reference: https://erdosproblems.com/1018
-/

import Mathlib
import Proofs.Erdos1018OQ01

open Finset
open Erdos1018OQ01 (degOn)

namespace Erdos1018OQ01OQ01

/-! ### Part 1 — the converse edge bound (upper side of the threshold) -/

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A finite graph is **`k`-degenerate** when every nonempty vertex set induces a
subgraph with a vertex of within-degree `≤ k`. Equivalently: no nonempty induced
subgraph has minimum degree `> k`. This is exactly the negation of the conclusion
of the extraction theorem. -/
def IsKDegenerate (k : ℕ) : Prop :=
  ∀ T : Finset V, T.Nonempty → ∃ v ∈ T, degOn G T v ≤ k

/-- **Converse edge bound.** A `k`-degenerate graph has at most `k · n` edges
(`n = |V|`). Contrapositive of `Erdos1018OQ01.exists_dense_induced_subgraph`:
more than `k·n` edges would force a nonempty induced subgraph of minimum degree
`> k`, contradicting `k`-degeneracy. -/
theorem degenerate_edge_bound {k : ℕ} (h : IsKDegenerate G k) :
    G.edgeFinset.card ≤ k * Fintype.card V := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨T, hTne, hTmin⟩ := Erdos1018OQ01.exists_dense_induced_subgraph G hcon
  obtain ⟨v, hvT, hvle⟩ := h T hTne
  have := hTmin v hvT
  omega

/-! ### Part 2 — the extremal witness (complete split graph) -/

/-- The **complete split graph** `S_{n,k}` on `Fin n`: the first `k` vertices
(those with value `< k`) are universal, the remaining `n − k` form an independent
set. Two vertices are adjacent iff they differ and at least one lies in the
universal part. This is the extremal `k`-degenerate graph. -/
def splitGraph (n k : ℕ) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ ((i : ℕ) < k ∨ (j : ℕ) < k)
  symm := by rintro i j ⟨hij, h⟩; exact ⟨hij.symm, h.symm⟩
  loopless := by rintro i ⟨h, _⟩; exact h rfl

@[simp] lemma splitGraph_adj (n k : ℕ) (i j : Fin n) :
    (splitGraph n k).Adj i j ↔ i ≠ j ∧ ((i : ℕ) < k ∨ (j : ℕ) < k) := Iff.rfl

instance splitGraph_decidableAdj (n k : ℕ) : DecidableRel (splitGraph n k).Adj :=
  fun i j => decidable_of_iff _ (splitGraph_adj n k i j).symm

/-- The universal part `{w : w.val < k}` has at most `k` vertices (exactly
`min n k`). Proof: `Fin.val` injects it into `range k`. -/
lemma card_lt_le (n k : ℕ) :
    (univ.filter (fun w : Fin n => (w : ℕ) < k)).card ≤ k := by
  have hsub : (univ.filter (fun w : Fin n => (w : ℕ) < k)).image (Fin.val)
            ⊆ Finset.range k := by
    intro m hm
    simp only [mem_image, mem_filter, mem_univ, true_and] at hm
    obtain ⟨w, hw, rfl⟩ := hm
    exact Finset.mem_range.mpr hw
  calc (univ.filter (fun w : Fin n => (w : ℕ) < k)).card
      = ((univ.filter (fun w : Fin n => (w : ℕ) < k)).image (Fin.val)).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range k).card := Finset.card_le_card hsub
    _ = k := Finset.card_range k

/-- When `k ≤ n` the universal part has exactly `k` vertices. -/
lemma card_lt_eq (n k : ℕ) (hk : k ≤ n) :
    (univ.filter (fun w : Fin n => (w : ℕ) < k)).card = k := by
  rw [← Finset.card_image_of_injective _ Fin.val_injective]
  have himg : (univ.filter (fun w : Fin n => (w : ℕ) < k)).image (Fin.val)
            = Finset.range k := by
    ext m
    simp only [mem_image, mem_filter, mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨w, hw, rfl⟩; exact hw
    · intro hm; exact ⟨⟨m, lt_of_lt_of_le hm hk⟩, hm, rfl⟩
  rw [himg, Finset.card_range]

/-- Degree of a universal vertex (`i.val < k`) is `n − 1`: it is adjacent to
every other vertex. -/
lemma degree_universal (n k : ℕ) (i : Fin n) (hi : (i : ℕ) < k) :
    (splitGraph n k).degree i = n - 1 := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  have : univ.filter ((splitGraph n k).Adj i) = univ.erase i := by
    ext w
    simp only [mem_filter, mem_univ, true_and, and_true, mem_erase, splitGraph_adj]
    constructor
    · rintro ⟨hne, _⟩; exact Ne.symm hne
    · intro hwi; exact ⟨Ne.symm hwi, Or.inl hi⟩
  rw [this, card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]

/-- Degree of an independent-part vertex (`k ≤ i.val`) is `k`: it is adjacent to
exactly the `k` universal vertices. -/
lemma degree_independent (n k : ℕ) (hk : k ≤ n) (i : Fin n) (hi : k ≤ (i : ℕ)) :
    (splitGraph n k).degree i = k := by
  rw [SimpleGraph.degree, SimpleGraph.neighborFinset_eq_filter]
  have : univ.filter ((splitGraph n k).Adj i)
       = univ.filter (fun w : Fin n => (w : ℕ) < k) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, splitGraph_adj]
    constructor
    · rintro ⟨_, hor⟩; rcases hor with h | h
      · omega
      · exact h
    · intro hw
      refine ⟨?_, Or.inr hw⟩
      intro heq; rw [heq] at hi; omega
  rw [this, card_lt_eq n k hk]

/-- **Handshake / edge count.** For `k ≤ n` the split graph satisfies
`2·|E| + k(k+1) = 2kn`, i.e. `|E| = k·n − C(k+1,2)`. Proved by summing degrees:
`k` universal vertices of degree `n − 1` and `n − k` independent vertices of
degree `k`. -/
lemma splitGraph_two_mul_edges (n k : ℕ) (hk : k ≤ n) :
    2 * (splitGraph n k).edgeFinset.card + k * (k + 1) = 2 * (k * n) := by
  have hcardA : (univ.filter (fun v : Fin n => (v : ℕ) < k)).card = k :=
    card_lt_eq n k hk
  have htot : (univ.filter (fun v : Fin n => (v : ℕ) < k)).card
            + (univ.filter (fun v : Fin n => ¬ (v : ℕ) < k)).card = n := by
    rw [Finset.filter_card_add_filter_neg_card_eq_card, card_univ, Fintype.card_fin]
  have hcardB : (univ.filter (fun v : Fin n => ¬ (v : ℕ) < k)).card = n - k := by
    omega
  have hA : ∑ v ∈ univ.filter (fun v : Fin n => (v : ℕ) < k), (splitGraph n k).degree v
          = (univ.filter (fun v : Fin n => (v : ℕ) < k)).card * (n - 1) := by
    rw [Finset.sum_congr rfl fun v hv => degree_universal n k v (mem_filter.mp hv).2,
        Finset.sum_const, smul_eq_mul]
  have hB : ∑ v ∈ univ.filter (fun v : Fin n => ¬ (v : ℕ) < k), (splitGraph n k).degree v
          = (univ.filter (fun v : Fin n => ¬ (v : ℕ) < k)).card * k := by
    rw [Finset.sum_congr rfl fun v hv =>
          degree_independent n k hk v (by have := (mem_filter.mp hv).2; omega),
        Finset.sum_const, smul_eq_mul]
  have hsplit : ∑ v, (splitGraph n k).degree v
      = ∑ v ∈ univ.filter (fun v : Fin n => (v : ℕ) < k), (splitGraph n k).degree v
      + ∑ v ∈ univ.filter (fun v : Fin n => ¬ (v : ℕ) < k), (splitGraph n k).degree v :=
    (Finset.sum_filter_add_sum_filter_not univ (fun v : Fin n => (v : ℕ) < k)
        (fun v => (splitGraph n k).degree v)).symm
  have h2E : 2 * (splitGraph n k).edgeFinset.card = k * (n - 1) + (n - k) * k := by
    rw [← (splitGraph n k).sum_degrees_eq_twice_card_edges, hsplit, hA, hB, hcardA, hcardB]
  rw [h2E]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  cases k with
  | zero => simp
  | succ k' =>
    have e1 : k' + 1 + m - 1 = k' + m := by omega
    have e2 : k' + 1 + m - (k' + 1) = m := by omega
    rw [e1, e2]; ring

/-- The split graph `S_{n,k}` is `k`-degenerate. Any independent-part vertex in a
set `T` has within-degree `≤ k` (its only neighbours are the `≤ k` universal
vertices); if `T` is contained in the universal part then `|T| ≤ k` and any
vertex has within-degree `≤ |T| − 1 ≤ k`. -/
lemma splitGraph_kDegenerate (n k : ℕ) : IsKDegenerate (splitGraph n k) k := by
  intro T hTne
  by_cases hB : ∃ v ∈ T, k ≤ (v : ℕ)
  · obtain ⟨v, hvT, hv⟩ := hB
    refine ⟨v, hvT, ?_⟩
    have hsub : T.filter (fun w => (splitGraph n k).Adj v w)
             ⊆ univ.filter (fun w : Fin n => (w : ℕ) < k) := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      obtain ⟨_, hadj⟩ := hw
      rw [splitGraph_adj] at hadj
      obtain ⟨_, hor⟩ := hadj
      rcases hor with h | h
      · omega
      · exact h
    calc degOn (splitGraph n k) T v
        = (T.filter (fun w => (splitGraph n k).Adj v w)).card := rfl
      _ ≤ (univ.filter (fun w : Fin n => (w : ℕ) < k)).card := Finset.card_le_card hsub
      _ ≤ k := card_lt_le n k
  · push_neg at hB
    obtain ⟨v, hvT⟩ := hTne
    refine ⟨v, hvT, ?_⟩
    have hTsub : T ⊆ univ.filter (fun w : Fin n => (w : ℕ) < k) := by
      intro w hw
      simp only [mem_filter, mem_univ, true_and]
      have := hB w hw; omega
    have hTcard : T.card ≤ k := le_trans (Finset.card_le_card hTsub) (card_lt_le n k)
    have hdeg : degOn (splitGraph n k) T v ≤ T.card - 1 := by
      have hsub : T.filter (fun w => (splitGraph n k).Adj v w) ⊆ T.erase v := by
        intro w hw
        simp only [mem_filter] at hw
        rw [mem_erase]
        obtain ⟨hwT, hadj⟩ := hw
        rw [splitGraph_adj] at hadj
        exact ⟨Ne.symm hadj.1, hwT⟩
      calc degOn (splitGraph n k) T v
          = (T.filter (fun w => (splitGraph n k).Adj v w)).card := rfl
        _ ≤ (T.erase v).card := Finset.card_le_card hsub
        _ = T.card - 1 := by rw [card_erase_of_mem hvT]
    omega

/-- **Sharpness of the degeneracy edge bound.** The complete split graph
`S_{n,k}` (for `k ≤ n`) is `k`-degenerate and has exactly `k·n − C(k+1,2)` edges
(here in the division-free form `2·|E| + k(k+1) = 2kn`). Combined with
`degenerate_edge_bound` (`k`-degenerate ⟹ `|E| ≤ k·n`), this shows the linear
coefficient `k` in the density threshold of Erdős #1018 is optimal, with additive
slack exactly `C(k+1,2)`. -/
theorem splitGraph_sharp (n k : ℕ) (hk : k ≤ n) :
    IsKDegenerate (splitGraph n k) k ∧
      2 * (splitGraph n k).edgeFinset.card + k * (k + 1) = 2 * (k * n) :=
  ⟨splitGraph_kDegenerate n k, splitGraph_two_mul_edges n k hk⟩

/-- Closed form for the extremal edge count: `|E(S_{n,k})| = k·n − C(k+1,2)`. -/
theorem splitGraph_edge_count (n k : ℕ) (hk : k ≤ n) :
    (splitGraph n k).edgeFinset.card = k * n - k * (k + 1) / 2 := by
  have h := splitGraph_two_mul_edges n k hk
  obtain ⟨t, ht⟩ := Nat.even_mul_succ_self k
  omega

end Erdos1018OQ01OQ01
