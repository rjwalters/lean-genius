import Mathlib.Analysis.Normed.Algebra.GelfandMazur
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Hurwitz Only-If: Normed Division Algebras Have Dimension in {1, 2, 4, 8}

This file addresses the "only-if" direction of Hurwitz's theorem (1898):
> If A is a finite-dimensional normed division algebra over ℝ, then dim(A) ∈ {1, 2, 4, 8}.

## Strategy

**Commutative case** (A is a field): Proved via the Gelfand-Mazur theorem (Mathlib, 2025).
Any normed field over ℝ is isomorphic as an ℝ-algebra to either ℝ (dim 1) or ℂ (dim 2).
Thus `finrank ℝ F ∈ {1, 2} ⊆ {1, 2, 4, 8}`.

**Non-commutative case** (A is a division ring): Requires additional machinery.
The classical proof proceeds via Clifford algebras and Radon-Hurwitz numbers:
1. Unit elements of A generate Clifford relations on ℝ^(dim A - 1)
2. Cl(n-1) has a real n-dimensional module only when n ∈ {1, 2, 4, 8}
   (Radon-Hurwitz numbers: ρ(n) forces this via the periodicity theorem)
3. Alternatively: reduce to `NSquareIdentity n` (HurwitzTheorem.lean) and
   apply the `hurwitz_only_if` axiom there.
Currently formalized as a sorry, pending Clifford representation theory in Mathlib.

## Relation to HurwitzTheorem.lean

The parent file `HurwitzTheorem.lean` contains:
  `axiom hurwitz_only_if (n : ℕ) (hn : n > 0) (nsi : NSquareIdentity n) :
    n ∈ admissibleDimensions`
for the `NSquareIdentity` formulation. This file works with `NormedDivisionRing`,
the Mathlib typeclass for (associative) normed division algebras. The two formulations
are mathematically equivalent; the reduction is:
  NormedDivisionRing A (dim n) → NSquareIdentity n
by choosing an orthonormal basis and transporting multiplication through coordinates.

## Key results

- `hurwitz_field_case`: proved (0 sorries) — Gelfand-Mazur for commutative algebras
- `hurwitz_only_if_ring`: 1 sorry — the non-commutative case (Clifford algebras needed)
-/

namespace HurwitzOnlyIf

open Module

/-! ### Admissible Dimensions -/

/-- The admissible dimensions for normed division algebras: {1, 2, 4, 8}. -/
def admissibleDimensions : Set ℕ := {1, 2, 4, 8}

/-! ### The Field (Commutative) Case via Gelfand-Mazur -/

/-- **Gelfand-Mazur consequence**: Any normed field over ℝ has finrank 1 or 2.
    Uses the Gelfand-Mazur theorem from Mathlib: every normed ℝ-algebra field
    is isomorphic to ℝ (yielding finrank 1) or ℂ (yielding finrank 2). -/
theorem finrank_normed_field_eq_one_or_two (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    Module.finrank ℝ F = 1 ∨ Module.finrank ℝ F = 2 := by
  obtain h | h := NormedAlgebra.Real.nonempty_algEquiv_or F
  · -- Case: F ≅ ℝ as ℝ-algebra, so finrank ℝ F = finrank ℝ ℝ = 1
    obtain ⟨e⟩ := h
    exact Or.inl (e.toLinearEquiv.finrank_eq.trans (CommSemiring.finrank_self ℝ))
  · -- Case: F ≅ ℂ as ℝ-algebra, so finrank ℝ F = finrank ℝ ℂ = 2
    obtain ⟨e⟩ := h
    exact Or.inr (e.toLinearEquiv.finrank_eq.trans Complex.finrank_real_complex)

/-- **Hurwitz field case**: A normed field over ℝ has finrank in {1, 2, 4, 8}.
    This is the commutative subcase, fully proved via Gelfand-Mazur.
    No assumption of finite-dimensionality is needed: Gelfand-Mazur implies it. -/
theorem hurwitz_field_case (F : Type*) [NormedField F] [NormedAlgebra ℝ F] :
    Module.finrank ℝ F ∈ admissibleDimensions := by
  have h := finrank_normed_field_eq_one_or_two F
  simp only [admissibleDimensions, Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases h with h | h <;> omega

/-! ### The General (Division Ring) Case -/

/-- **Hurwitz Only-If for Normed Division Rings**:
    A finite-dimensional normed division ring over ℝ has finrank in {1, 2, 4, 8}.

    **Commutative subcase**: If A is also a field (commutative), this follows from
    `hurwitz_field_case` (proved via Gelfand-Mazur).

    **Non-commutative subcase** (HARD sorry): The classical proof uses Clifford algebras.
    For a normed division ring A of dimension n, the (n-1) imaginary unit vectors satisfy
    Clifford relations: eᵢeⱼ + eⱼeᵢ = -2δᵢⱼ, giving a real representation of Cl(n-1).
    The Radon-Hurwitz numbers force n ∈ {1, 2, 4, 8}.

    Alternative: reduce to `HurwitzTheorem.NSquareIdentity n` via an orthonormal basis
    construction, then apply `HurwitzTheorem.hurwitz_only_if` (axiom in that file).

    **Frobenius' theorem** (associative case): For associative division algebras over ℝ,
    the only possibilities are ℝ (dim 1), ℂ (dim 2), ℍ (dim 4). Octonions (dim 8) are
    non-associative and require a separate argument beyond `NormedDivisionRing`. -/
theorem hurwitz_only_if_ring (A : Type*) [NormedDivisionRing A] [NormedAlgebra ℝ A]
    [Module.Finite ℝ A] :
    Module.finrank ℝ A ∈ admissibleDimensions := by
  /- Proof outline:
     1. If A is commutative (a field), apply hurwitz_field_case.
     2. If A is non-commutative:
        - Let n := finrank ℝ A
        - Choose orthonormal basis {e₁,...,eₙ} of A as ℝ-vector space
        - Define mul : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ) via
          mul a b := coordinates of (∑ aᵢeᵢ) * (∑ bᵢeᵢ)
        - From ‖xy‖ = ‖x‖·‖y‖: normSq a * normSq b = normSq (mul a b)
        - This gives NSquareIdentity n
        - Apply HurwitzTheorem.hurwitz_only_if to get n ∈ {1,2,4,8}
     Building the NSquareIdentity from a basis requires Clifford algebra infrastructure
     or a direct inner product argument not yet available in Mathlib. -/
  sorry

end HurwitzOnlyIf
