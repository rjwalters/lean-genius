/-
  Aristotle targets for Erdős Problem #434
  Routine supporting lemmas for automated proof search.
  See Erdos434Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main theorem (Kiss 2002) or deep Frobenius results
  - Known results provable from Mathlib (cardinality, finiteness, set operations)
  - Clean theorem statements with no definition sorries
  - No axioms

  The main file formalizes the extremal Frobenius problem: which k-element
  subset of {1, ..., n} maximizes the count of non-representable integers?
  Answer: {n-k+1, ..., n} (Kiss 2002).
-/
import Mathlib

namespace Erdos434Aristotle

open Finset

/- ## Definitions (mirrored from Erdos434Problem.lean) -/

/-- A natural number m is representable by set A if it equals a sum of elements
    from A with repetition allowed. -/
def IsRepresentableAs (m : ℕ) (A : Set ℕ) : Prop :=
  ∃ (S : Multiset ℕ), (∀ a ∈ S, a ∈ A) ∧ S.sum = m

/-- The set of non-representable integers. -/
def NonRepresentable (A : Set ℕ) : Set ℕ :=
  {n : ℕ | ¬IsRepresentableAs n A}

/-- The "top k" set: {n-k+1, n-k+2, ..., n}. -/
def topK (n k : ℕ) : Set ℕ :=
  Set.Icc (n - k + 1) n

/- ## Routine Lemmas -/

-- Cardinality of topK
/-- topK(n, k) has exactly k elements when k ≤ n and k > 0. -/
theorem topK_card (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0) :
    (topK n k).ncard = k := by
  simp only [topK]
  rw [Set.ncard_Icc]
  omega

-- Representability basics
/-- Zero is always representable (by the empty multiset). -/
theorem zero_representable (A : Set ℕ) : IsRepresentableAs 0 A :=
  ⟨0, fun _ h => absurd h (Multiset.not_mem_zero _), Multiset.sum_zero⟩

/-- Any element of A is representable. -/
theorem mem_representable {a : ℕ} {A : Set ℕ} (ha : a ∈ A) : IsRepresentableAs a A :=
  ⟨{a}, fun x hx => by rwa [Multiset.mem_singleton.mp hx], Multiset.sum_singleton a⟩

/-- If m and n are representable by A, so is m + n. -/
theorem add_representable {m n : ℕ} {A : Set ℕ}
    (hm : IsRepresentableAs m A) (hn : IsRepresentableAs n A) :
    IsRepresentableAs (m + n) A := by
  obtain ⟨S, hS, rfl⟩ := hm
  obtain ⟨T, hT, rfl⟩ := hn
  exact ⟨S + T, fun a ha => by
    rw [Multiset.mem_add] at ha
    exact ha.elim (hS a) (hT a),
    Multiset.sum_add S T⟩

-- Finiteness
/-- For a finite set A with coprime elements, non-representables are finite. -/
theorem nonrep_finite {A : Set ℕ} (hA : A.Nonempty)
    (hcop : ∃ a b ∈ A, Nat.Coprime a b) :
    (NonRepresentable A).Finite := by sorry

-- topK concrete values
/-- topK(5, 2) = {4, 5}. -/
theorem topK_5_2 : topK 5 2 = {4, 5} := by
  simp only [topK]; ext x; simp [Set.mem_Icc]; omega

/-- topK(10, 3) = {8, 9, 10}. -/
theorem topK_10_3 : topK 10 3 = {8, 9, 10} := by
  simp only [topK]; ext x; simp [Set.mem_Icc]; omega

-- Subset properties
/-- topK(n, k) ⊆ {1, ..., n} when k ≤ n and k > 0. -/
theorem topK_subset (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0) :
    topK n k ⊆ Set.Icc 1 n := by
  intro x hx
  simp only [topK, Set.mem_Icc] at hx ⊢
  exact ⟨by omega, hx.2⟩

/-- Every element of topK(n, k) is positive when k ≤ n and k > 0. -/
theorem topK_pos (n k : ℕ) (hk : k ≤ n) (hk_pos : k > 0)
    (x : ℕ) (hx : x ∈ topK n k) : x ≥ 1 := by
  have := topK_subset n k hk hk_pos hx
  exact (Set.mem_Icc.mp this).1

end Erdos434Aristotle
