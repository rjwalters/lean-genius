/-
  Hurwitz's Theorem (Erdős/gallery #357 circle) — OQ-03-OQ-01, incomplete-01
  Sharpness of the commutative Hurwitz bound.

  Context. The parent entry `Proofs/HurwitzOnlyIf.lean` (gallery
  `hurwitz-theorem-oq-03-oq-01`) proves the "only-if" direction of Hurwitz's theorem
  in the COMMUTATIVE (field) case via the Gelfand–Mazur theorem:

      hurwitz_field_case :
        (F : normed field over ℝ) → finrank ℝ F ∈ {1, 2, 4, 8}

  obtained from the sharper `finrank ℝ F = 1 ∨ finrank ℝ F = 2`. That is an UPPER
  bound only: it shows no commutative real normed division algebra can have dimension
  outside {1, 2}. The parent leaves the non-commutative division-ring case as a `sorry`
  (Clifford algebras / Radon–Hurwitz numbers, not yet in Mathlib).

  This companion supplies the missing REALIZABILITY / lower direction for the
  commutative case: both admissible values are actually attained —

      finrank ℝ ℝ = 1        (ℝ realizes dimension 1)
      finrank ℝ ℂ = 2        (ℂ realizes dimension 2)

  — so the bound {1, 2} is SHARP: the set of ℝ-dimensions realized by commutative real
  normed division algebras is *exactly* {1, 2}, not merely a subset. This upgrades the
  parent's one-sided bound for the commutative case to an exact characterization.
  Nothing here touches the parent's hard non-commutative `sorry`.

  Fully machine-checked: 0 axioms, 0 sorries, no `native_decide`.
-/
import Mathlib

open Module

namespace HurwitzCommSharp

/-- The admissible dimensions {1, 2, 4, 8} for normed division algebras over ℝ,
    matching `HurwitzOnlyIf.admissibleDimensions` in the parent file. -/
def admissibleDimensions : Set ℕ := {1, 2, 4, 8}

/-- **Upper bound (Gelfand–Mazur).** Any normed field over ℝ has `finrank ℝ F` equal to
    `1` or `2`. This is the commutative case of Hurwitz's only-if direction, reproduced
    from the parent file so this entry is self-contained; ℝ and ℂ are the only options. -/
theorem finrank_normed_field_eq_one_or_two (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    finrank ℝ F = 1 ∨ finrank ℝ F = 2 := by
  obtain h | h := NormedAlgebra.Real.nonempty_algEquiv_or F
  · obtain ⟨e⟩ := h
    exact Or.inl (e.toLinearEquiv.finrank_eq.trans (CommSemiring.finrank_self ℝ))
  · obtain ⟨e⟩ := h
    exact Or.inr (e.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex)

/-- Every normed field over ℝ has admissible finrank (commutative Hurwitz, upper bound). -/
theorem finrank_normed_field_admissible (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    finrank ℝ F ∈ admissibleDimensions := by
  simp only [admissibleDimensions, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases finrank_normed_field_eq_one_or_two F with h | h <;> omega

/-- **Realizability of dimension 1.** ℝ is a commutative real normed division algebra of
    dimension `1`, so the value `1` in the Hurwitz bound is attained. -/
theorem finrank_real_self : finrank ℝ ℝ = 1 := CommSemiring.finrank_self ℝ

/-- **Realizability of dimension 2.** ℂ is a commutative real normed division algebra of
    dimension `2`, so the value `2` in the Hurwitz bound is attained. -/
theorem finrank_complex : finrank ℝ ℂ = 2 := Complex.finrank_real_complex

/-- **Sharpness of the commutative Hurwitz bound.**

    The upper bound `finrank ℝ F ∈ {1, 2}` for commutative real normed division algebras
    is sharp: both endpoints are realized (ℝ gives `1`, ℂ gives `2`) and no such algebra
    attains any other dimension. Equivalently, the set of ℝ-dimensions of commutative real
    normed division algebras is *exactly* `{1, 2}`. This is the realizability direction the
    parent's one-sided bound lacks. -/
theorem comm_bound_sharp :
    finrank ℝ ℝ = 1 ∧ finrank ℝ ℂ = 2 ∧
      ∀ (F : Type) [NormedField F] [NormedAlgebra ℝ F], finrank ℝ F = 1 ∨ finrank ℝ F = 2 := by
  refine ⟨finrank_real_self, finrank_complex, ?_⟩
  intro F _ _
  exact finrank_normed_field_eq_one_or_two F

end HurwitzCommSharp
