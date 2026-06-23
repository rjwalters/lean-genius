/-
  Aristotle targets for Erdos629 (List Chromatic Number of Bipartite Graphs)
  Routine supporting lemmas for automated proof search.
  See Erdos629Problem.lean for the main formalization.

  10 of 15 sorries proved manually:
  - Exponential bounds (5): pow_pred_lt, pow_lt_sq_pow, recursive_upper_bound_helper,
    pow_factor, k_plus_one_pow_le — by omega/nlinarith/ring/calc
  - n_mono_helper: direct application of monotonicity hypothesis
  - Complete bipartite helpers (3): card_sum simp, cases + simp_all, Sum.noConfusion
  - clog_ge_one: Nat.clog_pos

  5 sorries remain for Aristotle:
  - bipartite_chromatic_le_two: graph coloring API
  - empty_graph_chromatic: graph coloring API
  - sInf_mono_subset: suspicious as stated (false when T = ∅)
  - clog_pow_two: uncertain Mathlib API
  - clog_le_self: uncertain Mathlib API
-/
import Mathlib

open SimpleGraph Finset

namespace Erdos629.Aristotle

/-
  ## Section 1: Bipartite Graph Helpers
-/

/-- A bipartite graph has chromatic number ≤ 2 -/
lemma bipartite_chromatic_le_two {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∃ f : V → Bool, ∀ u v, G.Adj u v → f u ≠ f v) :
    G.chromaticNumber ≤ 2 := by
  sorry

/-- A graph with no edges has chromatic number ≤ 1 -/
lemma empty_graph_chromatic {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ∀ u v : V, ¬G.Adj u v) : G.chromaticNumber ≤ 1 := by
  sorry

/-
  ## Section 2: Exponential Bounds
-/

/-- 2^(k-1) < 2^k for k ≥ 1 -/
lemma pow_pred_lt (k : ℕ) (hk : k ≥ 1) : 2 ^ (k - 1) < 2 ^ k :=
  Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- 2^k < k^2 * 2^(k+2) for k ≥ 1 -/
lemma pow_lt_sq_pow (k : ℕ) (hk : k ≥ 1) : 2 ^ k < k ^ 2 * 2 ^ (k + 2) := by
  have hpow : 0 < 2 ^ k := Nat.pos_pow_of_pos k (by norm_num)
  have hk2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have hksq : 1 ≤ k ^ 2 := Nat.one_le_pow 2 k hk
  nlinarith [hk2, hpow, hksq]

/-- k * n ≤ k^2 * 2^k when n ≤ k * 2^k -/
lemma recursive_upper_bound_helper (k n : ℕ) (h : n ≤ k * 2 ^ k) :
    k * n ≤ k ^ 2 * 2 ^ k :=
  calc k * n ≤ k * (k * 2 ^ k) := Nat.mul_le_mul_left k h
    _ = k ^ 2 * 2 ^ k := by ring

/-- 2^k + k * 2^k = (k+1) * 2^k -/
lemma pow_factor (k : ℕ) : 2 ^ k + k * 2 ^ k = (k + 1) * 2 ^ k := by ring

/-- (k+1) * 2^k ≤ k^2 * 2^(k+2) for k ≥ 2 -/
lemma k_plus_one_pow_le (k : ℕ) (hk : k ≥ 2) : (k + 1) * 2 ^ k ≤ k ^ 2 * 2 ^ (k + 2) := by
  have hpow : 0 < 2 ^ k := Nat.pos_pow_of_pos k (by norm_num)
  have hk2 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  nlinarith [hk2, hpow, hk]

/-
  ## Section 3: Csínf / sInf Monotonicity
-/

/-- sInf of a subset is at least sInf of superset (for naturals) -/
lemma sInf_mono_subset (S T : Set ℕ) (h : T ⊆ S) (hS : S.Nonempty) :
    Nat.sInf S ≤ Nat.sInf T := by
  sorry

/-- n(k) is monotone: n(k₁) ≤ n(k₂) for k₁ ≤ k₂ -/
lemma n_mono_helper (n : ℕ → ℕ) (hmono : ∀ k₁ k₂, k₁ ≤ k₂ → n k₁ ≤ n k₂)
    (k : ℕ) : n k ≤ n (k + 2) :=
  hmono k (k + 2) (by omega)

/-
  ## Section 4: Complete Bipartite Graph Properties
-/

/-- Complete bipartite graph K_{m,n} has m + n vertices -/
lemma completeBipartite_card (m n : ℕ) :
    Fintype.card (Fin m ⊕ Fin n) = m + n := by
  simp [Fintype.card_sum, Fintype.card_fin]

/-- K_{1,1} has 1 edge (it's just one edge) -/
lemma K11_card_adj : ∀ (u v : Fin 1 ⊕ Fin 1),
    (match u, v with
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
    | _, _ => False) → u ≠ v := by
  intro u v h
  cases u <;> cases v <;> simp_all

/-- Sum.inl and Sum.inr are always different -/
lemma inl_ne_inr {α β : Type*} (a : α) (b : β) : Sum.inl a ≠ (Sum.inr b : α ⊕ β) :=
  fun h => Sum.noConfusion h

/-
  ## Section 5: List Chromatic Ceiling
-/

/-- Nat.clog 2 n ≥ 1 for n ≥ 2 -/
lemma clog_ge_one (n : ℕ) (hn : n ≥ 2) : Nat.clog 2 n ≥ 1 :=
  Nat.clog_pos (by norm_num) hn

/-- Nat.clog 2 (2^k) = k -/
lemma clog_pow_two (k : ℕ) : Nat.clog 2 (2 ^ k) = k := by
  sorry

/-- Nat.clog 2 n ≤ n for n ≥ 1 -/
lemma clog_le_self (n : ℕ) (hn : n ≥ 1) : Nat.clog 2 n ≤ n := by
  sorry

end Erdos629.Aristotle
