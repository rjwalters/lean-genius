/-
  Property B: Upper Bounds on m(k) via Explicit Non-2-Colorable Hypergraphs

  The companion entry `PropertyBFirstMoment` (Erdős 1963) proves the LOWER
  bound: every k-uniform hypergraph with fewer than `2^(k-1)` edges is
  2-colorable, i.e. `m(k) ≥ 2^(k-1)`, where `m(k)` is the minimum number of
  edges in a NON-2-colorable k-uniform hypergraph.

  This file supplies the matching UPPER side by exhibiting explicit
  non-2-colorable hypergraphs, thereby bracketing `m(k)`:

    • General, all k:  the complete k-uniform hypergraph on `2k-1` vertices is
      not 2-colorable (one colour class has ≥ k vertices, so it contains a
      monochromatic edge). Hence `m(k) ≤ C(2k-1, k)`.

    • Sharp at k = 3:  the **Fano plane** PG(2,2) — 7 lines on 7 points — is
      not 2-colorable. Hence `m(3) ≤ 7`, beating the general bound
      `C(5,3) = 10`. (In fact `m(3) = 7`; the Fano plane is the extremal
      example.)

  Together with the first-moment lower bound this gives, e.g.,
  `4 = 2^(3-1) ≤ m(3) ≤ 7`.

  HONESTY: `C(2k-1, k) ≈ 4^k/√(πk)` is exponentially weaker than the
  Erdős–Lovász `m(k) = O(k²·2^k)`. These are explicit, unconditional,
  elementary witnesses bracketing `m(k)` from above — not the optimal
  probabilistic construction.

  Status: 0 sorries, 0 axioms. The Fano result uses `decide` (kernel
  evaluation over the 2^7 colourings), NOT `native_decide`, so it is
  axiom-free.
-/
import Mathlib

namespace ProbMethod.PropertyB.Upper

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A coloring `c : V → Bool` is **monochromatic** on an edge `e` if all of
    `e`'s vertices receive the same color. (Same notion as
    `ProbMethod.PropertyB.Mono` in the first-moment entry.) -/
def Mono (e : Finset V) (c : V → Bool) : Prop := ∃ b : Bool, ∀ x ∈ e, c x = b

instance (e : Finset V) (c : V → Bool) : Decidable (Mono e c) := by
  unfold Mono; infer_instance

/-- A hypergraph `E` is **not 2-colorable** (lacks Property B) if every
    2-coloring monochromatizes some edge — the negation of Property B. A
    `k`-uniform such `E` witnesses `m(k) ≤ |E|`. -/
def NotTwoColorable (E : Finset (Finset V)) : Prop :=
  ∀ c : V → Bool, ∃ e ∈ E, Mono e c

-- ═══════════════════════════════════════════════════
-- Part I: General bound m(k) ≤ C(2k-1, k) via the complete hypergraph
-- ═══════════════════════════════════════════════════

/-- The complete k-uniform hypergraph on `Fin (2k-1)`: all k-element subsets. -/
def completeHypergraph (k : ℕ) : Finset (Finset (Fin (2 * k - 1))) :=
  (univ : Finset (Fin (2 * k - 1))).powersetCard k

/-- Every edge of the complete k-uniform hypergraph has exactly `k` vertices. -/
theorem completeHypergraph_uniform (k : ℕ) :
    ∀ e ∈ completeHypergraph k, e.card = k := by
  intro e he; exact (mem_powersetCard.mp he).2

/-- The complete k-uniform hypergraph on `2k-1` vertices has `C(2k-1, k)` edges. -/
theorem completeHypergraph_card (k : ℕ) :
    (completeHypergraph k).card = Nat.choose (2 * k - 1) k := by
  rw [completeHypergraph, card_powersetCard, card_univ, Fintype.card_fin]

/-- **The complete k-uniform hypergraph on `2k-1` vertices is not 2-colorable.**
    Pigeonhole: a 2-coloring of `2k-1` vertices has a colour class of size
    `≥ k`, any `k` of whose vertices form a monochromatic edge. -/
theorem completeHypergraph_notTwoColorable (k : ℕ) :
    NotTwoColorable (completeHypergraph k) := by
  intro c
  -- From a colour class `S = {x | c x = b}` of size ≥ k, extract a mono edge.
  have main : ∀ b : Bool,
      k ≤ (univ.filter (fun x : Fin (2 * k - 1) => c x = b)).card →
      ∃ e ∈ completeHypergraph k, Mono e c := by
    intro b hb
    obtain ⟨S, hSsub, hScard⟩ := exists_subset_card_eq hb
    refine ⟨S, ?_, b, ?_⟩
    · rw [completeHypergraph, mem_powersetCard]
      exact ⟨hSsub.trans (filter_subset _ _), hScard⟩
    · intro x hx
      exact (mem_filter.mp (hSsub hx)).2
  -- The two colour classes partition the `2k-1` vertices.
  have hpart :
      (univ.filter (fun x : Fin (2 * k - 1) => c x = true)).card
        + (univ.filter (fun x : Fin (2 * k - 1) => c x = false)).card = 2 * k - 1 := by
    have key := filter_card_add_filter_neg_card_eq_card
      (s := (univ : Finset (Fin (2 * k - 1)))) (p := fun x => c x = true)
    have hcard : (univ : Finset (Fin (2 * k - 1))).card = 2 * k - 1 := by
      rw [card_univ, Fintype.card_fin]
    have heq : (univ.filter (fun x : Fin (2 * k - 1) => ¬ (c x = true)))
             = univ.filter (fun x => c x = false) := by
      apply filter_congr; intro x _; cases c x <;> simp
    rw [hcard, heq] at key; exact key
  -- One class has size ≥ k.
  have hdisj :
      k ≤ (univ.filter (fun x : Fin (2 * k - 1) => c x = true)).card ∨
      k ≤ (univ.filter (fun x : Fin (2 * k - 1) => c x = false)).card := by omega
  rcases hdisj with h | h
  · exact main true h
  · exact main false h

/-- **Upper bound `m(k) ≤ C(2k-1, k)`.** For every `k` there is a `k`-uniform
    hypergraph that is not 2-colorable and has exactly `C(2k-1, k)` edges.
    With the first-moment lower bound `2^(k-1) ≤ m(k)` this brackets `m(k)`. -/
theorem exists_notTwoColorable_le_choose (k : ℕ) :
    ∃ E : Finset (Finset (Fin (2 * k - 1))),
      (∀ e ∈ E, e.card = k) ∧ E.card = Nat.choose (2 * k - 1) k ∧ NotTwoColorable E :=
  ⟨completeHypergraph k, completeHypergraph_uniform k, completeHypergraph_card k,
    completeHypergraph_notTwoColorable k⟩

-- ═══════════════════════════════════════════════════
-- Part II: Sharp bound m(3) ≤ 7 via the Fano plane PG(2,2)
-- ═══════════════════════════════════════════════════

/-- The seven lines of the **Fano plane** PG(2,2) on the points `Fin 7`. -/
def fanoLines : Finset (Finset (Fin 7)) :=
  {{0, 1, 2}, {0, 3, 4}, {0, 5, 6}, {1, 3, 5}, {1, 4, 6}, {2, 3, 6}, {2, 4, 5}}

set_option maxRecDepth 10000 in
/-- The Fano plane is a 3-uniform hypergraph: every line has 3 points. -/
theorem fano_uniform : ∀ e ∈ fanoLines, e.card = 3 := by decide

set_option maxRecDepth 10000 in
/-- The Fano plane has 7 lines. -/
theorem fano_card : fanoLines.card = 7 := by decide

set_option maxRecDepth 10000 in
/-- **The Fano plane is not 2-colorable.** Verified by kernel evaluation over
    all `2^7 = 128` colorings: every one leaves some line monochromatic. -/
theorem fano_notTwoColorable : NotTwoColorable fanoLines := by
  unfold NotTwoColorable; decide

/-- **Sharp upper bound `m(3) ≤ 7`.** The Fano plane is a 3-uniform,
    not-2-colorable hypergraph with 7 edges. -/
theorem exists_notTwoColorable_three :
    ∃ E : Finset (Finset (Fin 7)),
      (∀ e ∈ E, e.card = 3) ∧ E.card = 7 ∧ NotTwoColorable E :=
  ⟨fanoLines, fano_uniform, fano_card, fano_notTwoColorable⟩

/-- The Fano bound `7` strictly beats the general bound `C(5,3) = 10` at `k = 3`. -/
theorem fano_beats_general : (7 : ℕ) < Nat.choose 5 3 := by decide

end ProbMethod.PropertyB.Upper
