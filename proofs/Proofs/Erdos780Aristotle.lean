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
    IsEmpty (completeHypergraph n r) := by
  constructor
  intro ⟨S, hS⟩
  have := S.card_le_univ
  simp [Finset.card_univ, Fintype.card_fin, hS] at this
  omega

/-- The complete 1-uniform hypergraph on n vertices has exactly n edges -/
theorem completeHypergraph_one_card (n : ℕ) (hn : 0 < n) :
    Fintype.card (completeHypergraph n 1) = n := by
  unfold completeHypergraph
  have : Fintype.card {S : Finset (Fin n) // S.card = 1} =
      ((Finset.univ : Finset (Fin n)).powersetCard 1).card := by
    rw [Fintype.card_subtype]
    congr 1; ext S
    simp [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ]
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin, Nat.choose_one_right]

/-- Any two 1-element subsets of [n] are disjoint iff they are distinct -/
theorem disjoint_singletons_iff {n : ℕ} (a b : Fin n) :
    Disjoint ({a} : Finset (Fin n)) {b} ↔ a ≠ b := by
  rw [Finset.disjoint_left]
  simp

/-- PairwiseDisjoint for a singleton set is trivially true -/
theorem pairwiseDisjoint_singleton {α : Type*} [DecidableEq α] (s : Finset α) :
    PairwiseDisjoint ({s} : Finset (Finset α)) := by
  intro e₁ he₁ e₂ he₂ hne
  rw [Finset.mem_singleton] at he₁ he₂
  exact absurd (he₁.trans he₂.symm) hne

/-- PairwiseDisjoint for two elements iff they are disjoint or equal -/
theorem pairwiseDisjoint_pair {α : Type*} [DecidableEq α]
    (s t : Finset α) :
    PairwiseDisjoint ({s, t} : Finset (Finset α)) ↔ (s = t ∨ Disjoint s t) := by
  constructor
  · intro h
    by_cases heq : s = t
    · exact Or.inl heq
    · exact Or.inr (h s (Finset.mem_insert_self s _) t
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self t)) heq)
  · intro hor e₁ he₁ e₂ he₂ hne
    rw [Finset.mem_insert, Finset.mem_singleton] at he₁ he₂
    rcases he₁ with rfl | rfl <;> rcases he₂ with rfl | rfl <;> first | exact absurd rfl hne | exact hor.resolve_left hne | exact (hor.resolve_left hne).symm

-- ============================================================
-- Supporting facts for Kneser chromatic number
-- ============================================================

/-- When n = 2r, every r-subset has a unique disjoint complement -/
theorem complement_unique_2r (r : ℕ) (hr : 0 < r) (S : Finset (Fin (2 * r)))
    (hS : S.card = r) :
    ∃! T : Finset (Fin (2 * r)), T.card = r ∧ Disjoint S T := by
  refine ⟨Sᶜ, ?_, ?_⟩
  · constructor
    · rw [Finset.card_compl, Finset.card_univ, Fintype.card_fin, hS]
      omega
    · exact Finset.disjoint_compl_right
  · intro T ⟨hTcard, hTdisj⟩
    have hTsub : T ⊆ Sᶜ := fun x hx =>
      Finset.mem_compl.mpr (Finset.disjoint_right.mp hTdisj hx)
    have hSc_card : Sᶜ.card = r := by
      rw [Finset.card_compl, Finset.card_univ, Fintype.card_fin, hS]; omega
    exact Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard, hSc_card])

/-- The number of r-subsets of [n] is C(n, r) -/
theorem card_completeHypergraph (n r : ℕ) (hr : r ≤ n) :
    Fintype.card (completeHypergraph n r) = Nat.choose n r := by
  unfold completeHypergraph
  have : Fintype.card {S : Finset (Fin n) // S.card = r} =
      ((Finset.univ : Finset (Fin n)).powersetCard r).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext S
    simp [Finset.mem_powersetCard, Finset.mem_filter, Finset.subset_univ]
  rw [this, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- Two r-subsets of [n] are disjoint only if n ≥ 2r -/
theorem disjoint_rsubsets_bound {n r : ℕ} (S T : Finset (Fin n))
    (hS : S.card = r) (hT : T.card = r) (hd : Disjoint S T) :
    2 * r ≤ n := by
  have hunion := Finset.card_union_of_disjoint hd
  rw [hS, hT] at hunion
  calc 2 * r = r + r := by ring
    _ = (S ∪ T).card := hunion.symm
    _ ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
    _ = n := by simp [Fintype.card_fin]

-- ============================================================
-- Threshold and bound lemmas
-- ============================================================

/-- The threshold is monotone in each parameter -/
theorem threshold_mono_k (k₁ k₂ r t : ℕ) (h : k₁ ≤ k₂) :
    k₁ * r + (t - 1) * (k₁ - 1) ≤ k₂ * r + (t - 1) * (k₂ - 1) := by
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right r h
  · exact Nat.mul_le_mul_left (t - 1) (Nat.sub_le_sub_right h 1)

/-- The threshold for k=2 simplifies to n ≥ 2r + t - 1 -/
theorem threshold_k2 (r t : ℕ) :
    2 * r + (t - 1) * 1 = 2 * r + t - 1 := by
  omega

end Erdos780Aristotle
