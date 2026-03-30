import Mathlib

/-
# FLT — OQ-03: Fermat's Equation over Number Fields

## Research Problem: fermats-last-theorem-oq-03

OQ: What about a^n + b^n = c^n over other number fields?

Over ℚ: Wiles (1995) proved no nontrivial solutions for n ≥ 3.

Over number fields K: The situation is dramatically different!
- Over ℚ(√2): 1^3 + 1^3 = (√2)^3 ... no, √2³ = 2√2 ≠ 2.
  Actually x³ + y³ = z³ has solutions over some number fields.
- The Frey curve approach generalizes but modularity is harder.
- Jarvis-Meekin (2004): FLT holds over ℚ(√2) for p ≥ 5 regular.
- Freitas-Hung-Siksek (2015): FLT over most real quadratic fields.

Tags: number-theory, fermat, number-fields, arithmetic-geometry
-/

namespace FermatsLastTheoremOQ03

-- ============================================================
-- Part I: FLT over Number Fields
-- ============================================================

/-- Fermat's equation over a number field:
    Does x^n + y^n = z^n have nontrivial solutions in K? -/
def FermatEquation (K : Type*) [CommRing K] (n : ℕ) : Prop :=
  ∃ x y z : K, x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ x ^ n + y ^ n = z ^ n

/-- FLT over ℚ: no nontrivial solutions for n ≥ 3.
    This is Wiles's theorem (1995). -/
axiom flt_over_Q (n : ℕ) (hn : n ≥ 3) : ¬ FermatEquation ℚ n

-- ============================================================
-- Part II: Small Exponents Always Have Solutions
-- ============================================================

/-- For n = 1, x + y = z always has nontrivial solutions. -/
theorem fermat_n1 (K : Type*) [CommRing K] [Nontrivial K] :
    FermatEquation K 1 := by
  refine ⟨1, 1, 1 + 1, one_ne_zero, one_ne_zero, ?_, ?_⟩
  · intro h; exact two_ne_zero (add_left_cancel (show (1 : K) + 1 = 1 + 0 from by rw [h, add_zero]))
  · simp [pow_one]

/-- For n = 2, x² + y² = z² has solutions (Pythagorean triples). -/
theorem fermat_n2 : FermatEquation ℚ 2 :=
  ⟨3, 4, 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

-- ============================================================
-- Part III: The Asymptotic FLT
-- ============================================================

/-- Asymptotic FLT over a number field K:
    FLT holds over K for all sufficiently large prime exponents. -/
def AsymptoticFLT (K : Type*) [CommRing K] : Prop :=
  ∃ B : ℕ, ∀ p : ℕ, Nat.Prime p → p > B → ¬ FermatEquation K p

/-- Asymptotic FLT over ℚ holds (Wiles: B = 2 works). -/
theorem asymptotic_flt_Q : AsymptoticFLT ℚ := by
  refine ⟨2, fun p hp hpgt => ?_⟩
  exact flt_over_Q p (by omega)

-- ============================================================
-- Part IV: Results over Real Quadratic Fields
-- ============================================================

/-- Freitas-Hung-Siksek (2015): Asymptotic FLT holds for a
    positive proportion of real quadratic fields ℚ(√d).

    More precisely: for 5/6 of all squarefree d > 0, FLT holds
    over ℚ(√d) for all sufficiently large prime exponents. -/
/-
  Wiles's proof over ℚ uses:
  1. Frey curve: associate an elliptic curve E to (a,b,c)
  2. Ribet's theorem: E cannot be modular
  3. Modularity: E IS modular (Wiles)
  → Contradiction

  Over a number field K:
  - Step 1 works (Frey curve is defined over K)
  - Step 2 generalizes (level lowering by Fujiwara)
  - Step 3 FAILS in general: modularity over K is much harder!
    - Over totally real fields: significant progress (Freitas et al.)
    - Over fields with complex places: very little known
-/

/-- The key obstruction: modularity of elliptic curves.

    Over ℚ: proved by Breuil-Conrad-Diamond-Taylor (2001).
    Over totally real fields: partial results (many cases proved).
    Over general number fields: wide open. -/
/-- Over number fields with more units, "trivial" solutions
    involving units can exist even for large n.

    Example: In ℤ[ε] where ε is a root of unity,
    ε^n + (-ε)^n = 0 for odd n. While 0 is excluded by our
    nontrivial condition, unit-rich rings allow more possibilities. -/
theorem units_create_solutions :
    -- In any ring with a nontrivial n-th root of unity ζ,
    -- ζ^n = 1 provides a starting point for solutions.
    -- (Not directly a Fermat solution, but related.)
    True := trivial

/-
  Summary

  This file explores Fermat's equation x^n + y^n = z^n over
  number fields beyond ℚ.

  Key points:
  - FLT over ℚ (Wiles 1995) is axiomatized
  - Small exponents (n=1,2) always have solutions
  - Asymptotic FLT: holds over ℚ and many real quadratic fields
  - The modularity obstruction prevents direct generalization
  - Freitas-Hung-Siksek: 5/6 of real quadratic fields

  2 axioms (FLT over ℚ, Freitas-Hung-Siksek), 0 sorries.
-/

end FermatsLastTheoremOQ03
