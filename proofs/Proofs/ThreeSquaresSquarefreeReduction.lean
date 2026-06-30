/-
Squarefree reduction for Legendre's three-square theorem.

The lone remaining axiom of `Proofs.ThreeSquares`, `not_excluded_form_is_sum_three_sq`
(sufficiency: every `n` not of the form `4^a*(8b+7)` is a sum of three integer
squares), reduces -- entirely elementarily -- to its SQUAREFREE special case stated
over the rationals:

    every squarefree `s` with `not (IsExcludedForm s)` is a sum of three RATIONAL squares.

This file proves that reduction (`three_sq_of_squarefree_rat`), combining four
already-built ingredients:

  * `Nat.sq_mul_squarefree`                              : write `n = m^2 * s`, `s` squarefree;
  * `ThreeSquares.not_excluded_of_sq_mul_not_excluded`   : `not (IsExcludedForm n)` => `not (IsExcludedForm s)`;
  * rational scaling by `m`                              : a rational rep of `s` gives one of `n = m^2*s`;
  * `ThreeSquaresDC.exists_int_sq_of_rat_sq` (Davenport-Cassels) : rational => integral.

Mathematically this is the classical first step of Dirichlet's proof: the deep
local-global input is only ever needed for SQUAREFREE arguments. After this reduction
the genuinely irreducible frontier is precisely the hypothesis `H` below --
sum-of-three-rational-squares for squarefree non-excluded `n`, i.e. Hasse-Minkowski
solvability of `x^2+y^2+z^2 = n` over the rationals, which is absent from Mathlib.

No new axioms, no sorries.
-/
import Mathlib
import Proofs.ThreeSquares
import Proofs.ThreeSquaresDavenportCassels

namespace ThreeSquares

/-- **Squarefree reduction of three-square sufficiency.**

If every squarefree `s` not of excluded form is a sum of three *rational* squares,
then every `n` not of excluded form is a sum of three *integer* squares.

This reduces the open content of `not_excluded_form_is_sum_three_sq` from all
non-excluded `n` to the squarefree case over the rationals. -/
theorem three_sq_of_squarefree_rat
    (H : ∀ s : ℕ, Squarefree s → ¬IsExcludedForm s →
        ∃ x y z : ℚ, x ^ 2 + y ^ 2 + z ^ 2 = (s : ℚ)) :
    ∀ n : ℕ, ¬IsExcludedForm n → ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = (n : ℤ) := by
  intro n hn
  -- `n = m^2 * s` with `s` squarefree.
  obtain ⟨s, m, hms, hsf⟩ := Nat.sq_mul_squarefree n
  rcases eq_or_ne m 0 with rfl | hm0
  · -- `m = 0` forces `n = 0`; the zero representation works.
    refine ⟨0, 0, 0, ?_⟩
    have hn0 : n = 0 := by simpa using hms.symm
    simp [hn0]
  · -- `m ≠ 0`: the squarefree core `s` is also non-excluded.
    have hsne : ¬IsExcludedForm s :=
      not_excluded_of_sq_mul_not_excluded hm0 (by rw [hms]; exact hn)
    -- A rational representation of `s`, scaled by `m`, represents `n = m^2 * s`.
    obtain ⟨x, y, z, hxyz⟩ := H s hsf hsne
    refine ThreeSquaresDC.exists_int_sq_of_rat_sq (n : ℤ)
      ⟨(m : ℚ) * x, (m : ℚ) * y, (m : ℚ) * z, ?_⟩
    have hn_eq : ((n : ℤ) : ℚ) = (m : ℚ) ^ 2 * (s : ℚ) := by
      rw [← hms]; push_cast; ring
    rw [hn_eq]
    linear_combination (m : ℚ) ^ 2 * hxyz

end ThreeSquares
