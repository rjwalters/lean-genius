/-
  Aristotle targets for Erdős Problem #780
  Routine supporting lemmas for automated proof search.
  See Erdos780Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (AFL 1986, Kneser's conjecture)
  - Known result or small decidable case
  - Clean theorem statement with no definition sorries
  - No axioms (use theorem ... := by sorry instead)
-/
import Mathlib

namespace Erdos780Aristotle

open Finset

/-- The complete r-uniform hypergraph on n vertices -/
def completeHypergraph (n r : ℕ) := {S : Finset (Fin n) // S.card = r}

/-- Pairwise disjoint edges -/
def PairwiseDisjoint {α : Type*} (edges : Finset (Finset α)) : Prop :=
  ∀ e₁ ∈ edges, ∀ e₂ ∈ edges, e₁ ≠ e₂ → Disjoint e₁ e₂

/-- Chromatic number of the Kneser hypergraph KG^r(n,k) -/
noncomputable def chromaticNumber (n r k : ℕ) : ℕ :=
  sInf { t : ℕ | ∃ c : completeHypergraph n r → Fin t,
    ∀ i : Fin t, ∀ edges : Finset (completeHypergraph n r),
      PairwiseDisjoint (edges.image Subtype.val) →
      (∀ e ∈ edges, c e = i) →
      edges.card < k }

-- ============================================================
-- Routine lemmas about hypergraph structure
-- ============================================================

/-- The complete hypergraph on n vertices with r > n has no edges -/
theorem completeHypergraph_empty_of_lt (n r : ℕ) (h : n < r) :
    IsEmpty (completeHypergraph n r) := by sorry

/-- The complete 1-uniform hypergraph on n vertices has exactly n edges -/
theorem completeHypergraph_one_card (n : ℕ) (hn : 0 < n) :
    Fintype.card (completeHypergraph n 1) = n := by sorry

/-- Any two 1-element subsets of [n] are disjoint iff they are distinct -/
theorem disjoint_singletons_iff {n : ℕ} (a b : Fin n) :
    Disjoint ({a} : Finset (Fin n)) {b} ↔ a ≠ b := by sorry

/-- PairwiseDisjoint for a singleton set is trivially true -/
theorem pairwiseDisjoint_singleton {α : Type*} [DecidableEq α] (s : Finset α) :
    PairwiseDisjoint ({s} : Finset (Finset α)) := by sorry

/-- PairwiseDisjoint for two elements iff they are disjoint or equal -/
theorem pairwiseDisjoint_pair {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    PairwiseDisjoint ({s, t} : Finset (Finset α)) ↔ (s = t ∨ Disjoint s t) := by sorry

-- ============================================================
-- Supporting facts for Kneser chromatic number
-- ============================================================

/-- When n = 2r, every r-subset has a unique disjoint complement -/
theorem complement_unique_2r (r : ℕ) (hr : 0 < r) (S : Finset (Fin (2 * r)))
    (hS : S.card = r) :
    ∃! T : Finset (Fin (2 * r)), T.card = r ∧ Disjoint S T := by sorry

/-- The number of r-subsets of [n] is C(n, r) -/
theorem card_completeHypergraph (n r : ℕ) (hr : r ≤ n) :
    Fintype.card (completeHypergraph n r) = Nat.choose n r := by sorry

/-- Two r-subsets of [n] are disjoint only if n ≥ 2r -/
theorem disjoint_rsubsets_bound {n r : ℕ} (S T : Finset (Fin n))
    (hS : S.card = r) (hT : T.card = r) (hd : Disjoint S T) :
    2 * r ≤ n := by sorry

-- ============================================================
-- Threshold and bound lemmas
-- ============================================================

/-- The threshold is monotone in each parameter -/
theorem threshold_mono_k (k₁ k₂ r t : ℕ) (h : k₁ ≤ k₂) :
    k₁ * r + (t - 1) * (k₁ - 1) ≤ k₂ * r + (t - 1) * (k₂ - 1) := by sorry

/-- The threshold for k=2 simplifies to n ≥ 2r + t - 1 -/
theorem threshold_k2 (r t : ℕ) :
    2 * r + (t - 1) * 1 = 2 * r + t - 1 := by sorry

end Erdos780Aristotle
