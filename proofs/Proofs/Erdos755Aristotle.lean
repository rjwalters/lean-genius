/-
  Aristotle targets for Erdős Problem #755 (Equilateral Triangles in ℝ⁶)
  Routine supporting lemmas for automated proof search.
  See Erdos755Problem.lean for the main formalization.

  Key target:
  T6_unit_le_T6_aristotle: T₆ᵘ(n) ≤ T₆(n).

  Proof route:
  1. unit_implies_equilateral: IsUnitEquilateralTriangle → IsEquilateralTriangle
     (all sides = 1 implies sides equal and positive)
  2. For any configuration P, the unit triangle vertex count ≤ general vertex count
     (filter monotonicity via Finset.card_le_card + Finset.filter_subset_filter)
  3. Hence sSup of unit counts ≤ sSup of general counts (csSup_le + le_csSup).
-/
import Mathlib
import Proofs.Erdos755Problem

-- Real equalities / the Pi order on `Fin d → ℝ` are classically decidable.
attribute [local instance] Classical.propDecidable

namespace Erdos755

variable {d : ℕ}

/-- A unit equilateral triangle (all sides = 1) is an equilateral triangle
    (all sides equal, positive length). -/
theorem unit_implies_equilateral (p₁ p₂ p₃ : Fin d → ℝ)
    (h : IsUnitEquilateralTriangle p₁ p₂ p₃) : IsEquilateralTriangle p₁ p₂ p₃ := by
  simp only [IsUnitEquilateralTriangle] at h
  obtain ⟨h12, h23, h31⟩ := h
  simp only [IsEquilateralTriangle]
  refine ⟨?_, ?_, ?_⟩
  · rw [h12, h23]
  · rw [h23, h31]
  · rw [h12]; norm_num

/-- For any point configuration P, the count of vertices in unit equilateral triangles
    is ≤ the count of vertices in any equilateral triangles. -/
theorem unit_count_le_eq_count (P : Finset (Fin 6 → ℝ)) :
    (P.filter (fun p₁ =>
      (P.filter (fun p₂ =>
        (P.filter (fun p₃ =>
          IsUnitEquilateralTriangle p₁ p₂ p₃ ∧ p₁ < p₂ ∧ p₂ < p₃
        )).card > 0
      )).card > 0
    )).card ≤
    (P.filter (fun p₁ =>
      (P.filter (fun p₂ =>
        (P.filter (fun p₃ =>
          IsEquilateralTriangle p₁ p₂ p₃ ∧ p₁ < p₂ ∧ p₂ < p₃
        )).card > 0
      )).card > 0
    )).card := by
  apply Finset.card_le_card
  intro p₁ hp₁
  rw [Finset.mem_filter] at hp₁ ⊢
  refine ⟨hp₁.1, ?_⟩
  refine lt_of_lt_of_le hp₁.2 (Finset.card_le_card ?_)
  intro p₂ hp₂
  rw [Finset.mem_filter] at hp₂ ⊢
  refine ⟨hp₂.1, ?_⟩
  refine lt_of_lt_of_le hp₂.2 (Finset.card_le_card ?_)
  intro p₃ hp₃
  rw [Finset.mem_filter] at hp₃ ⊢
  refine ⟨hp₃.1, ?_⟩
  obtain ⟨hU, hord⟩ := hp₃.2
  exact ⟨unit_implies_equilateral p₁ p₂ p₃ hU, hord⟩

/-- T₆ᵘ(n) ≤ T₆(n): unit triangle vertex count ≤ equilateral triangle vertex count.
    This is the main file's `T6_unit_le_T6`, re-exposed as an Aristotle target. -/
theorem T6_unit_le_T6_aristotle (n : ℕ) : T6_unit n ≤ T6 n :=
  T6_unit_le_T6 n

end Erdos755
