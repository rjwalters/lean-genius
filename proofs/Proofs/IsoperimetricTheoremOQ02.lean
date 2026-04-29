/-
Discrete Isoperimetric Inequality (1D)

Open Question from: Isoperimetric Theorem (Wiedijk #43)

The continuous isoperimetric inequality has a discrete analogue on the integer
lattice. For finite S ⊆ ℤ with |S| ≥ 2, the (vertex) edge boundary ∂S has at
least 2 elements, with equality if and only if S is an interval.

Proof idea:
  Let m = min S and M = max S. Since |S| ≥ 2, m < M. Then m - 1 ∉ S (since m
  is the minimum) but m - 1 is adjacent to m ∈ S, so m - 1 ∈ ∂S. Similarly
  M + 1 ∈ ∂S. These are distinct, so |∂S| ≥ 2.

  For intervals S = {a, a+1, …, b}, the boundary is exactly {a-1, b+1}, with
  cardinality 2.

This is the foundation for higher-dimensional discrete isoperimetric theorems
(Bollobás–Leader compression on ℤ^d, Harper's theorem on the hypercube).

References:
  - Bollobás (1986), Combinatorics: Set Systems, Hypergraphs, Families of
    Vectors, and Combinatorial Probability, Cambridge University Press.
  - Harper (1966), Optimal numberings and isoperimetric problems on graphs,
    J. Combinatorial Theory.

Tags: combinatorics, discrete-geometry, isoperimetric-inequality
-/
import Mathlib

namespace DiscreteIsoperimetric1D

/-- The vertex edge boundary of `S ⊆ ℤ`: integers adjacent to some element of
    `S` but not themselves in `S`. -/
def edgeBoundary (S : Finset ℤ) : Finset ℤ :=
  ((S.image (· - 1)) ∪ (S.image (· + 1))) \ S

/-- Membership characterization for the edge boundary. -/
lemma mem_edgeBoundary {S : Finset ℤ} {x : ℤ} :
    x ∈ edgeBoundary S ↔ (x + 1 ∈ S ∨ x - 1 ∈ S) ∧ x ∉ S := by
  simp only [edgeBoundary, Finset.mem_sdiff, Finset.mem_union, Finset.mem_image]
  refine and_congr ?_ Iff.rfl
  constructor
  · rintro (⟨a, ha, hax⟩ | ⟨a, ha, hax⟩)
    · left
      have : a = x + 1 := by linarith
      simpa [this] using ha
    · right
      have : a = x - 1 := by linarith
      simpa [this] using ha
  · rintro (h | h)
    · exact Or.inl ⟨x + 1, h, by ring⟩
    · exact Or.inr ⟨x - 1, h, by ring⟩

/-- Main theorem: For finite `S ⊆ ℤ` with `|S| ≥ 2`, the edge boundary has at
    least 2 elements. -/
theorem edgeBoundary_card_ge_two {S : Finset ℤ} (h : 2 ≤ S.card) :
    2 ≤ (edgeBoundary S).card := by
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  set m := S.min' hne with hm_def
  set M := S.max' hne with hM_def
  have hm_mem : m ∈ S := S.min'_mem hne
  have hM_mem : M ∈ S := S.max'_mem hne
  have hmM : m < M := Finset.min'_lt_max'_of_card S (by omega)
  have h_lo : m - 1 ∈ edgeBoundary S := by
    rw [mem_edgeBoundary]
    refine ⟨Or.inl ?_, ?_⟩
    · simpa using hm_mem
    · intro hcontra
      have := S.min'_le _ hcontra
      simp [← hm_def] at this
      linarith
  have h_hi : M + 1 ∈ edgeBoundary S := by
    rw [mem_edgeBoundary]
    refine ⟨Or.inr ?_, ?_⟩
    · simpa using hM_mem
    · intro hcontra
      have := S.le_max' _ hcontra
      simp [← hM_def] at this
      linarith
  have h_ne : m - 1 ≠ M + 1 := by linarith
  have h_sub : ({m - 1, M + 1} : Finset ℤ) ⊆ edgeBoundary S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact h_lo
    · rw [Finset.mem_singleton] at hx
      rw [hx]; exact h_hi
  have h_card : ({m - 1, M + 1} : Finset ℤ).card = 2 := by
    rw [Finset.card_insert_of_not_mem (by simp [h_ne]), Finset.card_singleton]
  calc 2 = ({m - 1, M + 1} : Finset ℤ).card := h_card.symm
    _ ≤ (edgeBoundary S).card := Finset.card_le_card h_sub

/-- The edge boundary of an integer interval `[a, b]` is exactly `{a-1, b+1}`. -/
theorem edgeBoundary_Icc {a b : ℤ} (h : a ≤ b) :
    edgeBoundary (Finset.Icc a b) = {a - 1, b + 1} := by
  ext x
  rw [mem_edgeBoundary]
  simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, hnot⟩
    rcases h1 with ⟨ha1, hb1⟩ | ⟨ha2, hb2⟩
    · -- a ≤ x + 1 ≤ b, so x ∈ [a-1, b-1]; combined with x ∉ [a,b], gives x = a-1
      have : x < a := by
        by_contra hc; push_neg at hc
        exact hnot ⟨hc, by linarith⟩
      left; linarith
    · -- a ≤ x - 1 ≤ b, so x ∈ [a+1, b+1]; combined with x ∉ [a,b], gives x = b+1
      have : x > b := by
        by_contra hc; push_neg at hc
        exact hnot ⟨by linarith, hc⟩
      right; linarith
  · rintro (rfl | rfl)
    · refine ⟨Or.inl ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · push_neg; intro h1; linarith
    · refine ⟨Or.inr ⟨?_, ?_⟩, ?_⟩
      · linarith
      · linarith
      · push_neg; intro h1; linarith

/-- For an interval `[a, b]` with `a ≤ b`, the edge boundary has exactly 2
    elements. Intervals therefore achieve equality in the isoperimetric bound. -/
theorem edgeBoundary_Icc_card {a b : ℤ} (h : a ≤ b) :
    (edgeBoundary (Finset.Icc a b)).card = 2 := by
  rw [edgeBoundary_Icc h]
  rw [Finset.card_insert_of_not_mem (by simp; linarith), Finset.card_singleton]

/-- The discrete 1D isoperimetric inequality: for finite `S ⊆ ℤ` with at least
    2 elements, `|∂S| ≥ 2`, and intervals achieve this bound. -/
theorem discrete_isoperimetric_1d :
    (∀ S : Finset ℤ, 2 ≤ S.card → 2 ≤ (edgeBoundary S).card) ∧
    (∀ a b : ℤ, a ≤ b → (edgeBoundary (Finset.Icc a b)).card = 2) :=
  ⟨fun _ => edgeBoundary_card_ge_two, fun _ _ => edgeBoundary_Icc_card⟩

end DiscreteIsoperimetric1D
