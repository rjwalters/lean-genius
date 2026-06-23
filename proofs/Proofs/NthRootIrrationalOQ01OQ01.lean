/-
  Nth Root Irrationality OQ-01-OQ-01: Algebraic Irrationality of Cyclotomic Roots

  The parent file `NthRootIrrationalOQ01.lean` established the structural
  principle "a root of an irreducible degree ≥ 2 polynomial over ℚ is
  irrational", and applied it to `X^n - p` (Eisenstein).

  This file extends that principle to the **cyclotomic polynomials** Φ_n and
  their roots, the primitive n-th roots of unity.

  **Key facts used:**
  - `cyclotomic.irreducible_rat`: Φ_n is irreducible over ℚ (n > 0).
  - `natDegree_cyclotomic`: deg Φ_n = φ(n) (Euler totient).
  - `totient ≥ 2` exactly when n ≥ 3.

  **Results (0 axioms, 0 sorries):**
  1. `totient_ge_two`           : 3 ≤ n → 2 ≤ φ(n).
  2. `cyclotomic_no_rational_root` : Φ_n has no rational root for n ≥ 3.
  3. `rational_root_of_unity_le_two` : the only rational roots of unity are ±1
       (a primitive n-th root of unity in ℚ forces n ≤ 2).
  4. `primitiveRoot_not_rational` : a complex primitive n-th root of unity
       (n ≥ 3) is not in the image of ℚ — i.e. it is "irrational".
  5. `primitiveCubeRoot_not_rational` : concrete instance e^{2πi/3}.

  ## References
  - Washington, L. (1997). "Introduction to Cyclotomic Fields." Ch. 2.
  - Dummit & Foote (2004). "Abstract Algebra." §13.6 (Cyclotomic polynomials).
-/

import Mathlib

set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open Polynomial

namespace NthRootIrrationalOQ01OQ01

noncomputable section

-- ============================================================================
-- Part 0: Self-contained core (irreducible degree ≥ 2 ⟹ no rational root)
--   Re-proved here (identical to NthRootIrrationalOQ01) to keep this file
--   independent of cross-file build state.
-- ============================================================================

/-- If `p ∈ ℚ[X]` is irreducible with degree ≥ 2, then `p` has no rational root. -/
theorem irreducible_no_rational_root {p : ℚ[X]} (hirr : Irreducible p)
    (hdeg : 2 ≤ p.natDegree) (r : ℚ) : ¬ p.IsRoot r := by
  intro hroot
  obtain ⟨q, hpq⟩ := dvd_iff_isRoot.mpr hroot
  rcases hirr.isUnit_or_isUnit hpq with hu | hu
  · exact (irreducible_X_sub_C r).1 hu
  · have hne1 := X_sub_C_ne_zero r
    have hne2 : q ≠ 0 := right_ne_zero_of_mul (hpq ▸ hirr.ne_zero)
    have hd : p.natDegree = 1 + q.natDegree := by
      rw [hpq, natDegree_mul hne1 hne2, natDegree_X_sub_C]
    have hq0 : q.natDegree = 0 := by
      rcases Polynomial.isUnit_iff.mp hu with ⟨c, _, rfl⟩
      exact natDegree_C c
    omega

-- ============================================================================
-- Part I: The totient is ≥ 2 for n ≥ 3
-- ============================================================================

/-- Euler's totient satisfies `φ(n) ≥ 2` for all `n ≥ 3`.
    (φ(1) = φ(2) = 1 are the only values equal to 1.) -/
theorem totient_ge_two {n : ℕ} (hn : 3 ≤ n) : 2 ≤ n.totient := by
  have hpos : 0 < n.totient := Nat.totient_pos.mpr (by omega)
  have hne1 : n.totient ≠ 1 := by
    intro h
    rcases Nat.totient_eq_one_iff.mp h with h1 | h2 <;> omega
  omega

-- ============================================================================
-- Part II: Cyclotomic polynomials have no rational root (n ≥ 3)
-- ============================================================================

/-- **Cyclotomic irrationality core**: for `n ≥ 3`, the cyclotomic polynomial
    `Φ_n` has no rational root, because it is irreducible over ℚ of degree
    `φ(n) ≥ 2`. -/
theorem cyclotomic_no_rational_root {n : ℕ} (hn : 3 ≤ n) (r : ℚ) :
    ¬ (cyclotomic n ℚ).IsRoot r := by
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (by omega : 0 < n)
  have hdeg : 2 ≤ (cyclotomic n ℚ).natDegree := by
    rw [natDegree_cyclotomic]
    exact totient_ge_two hn
  exact irreducible_no_rational_root hirr hdeg r

-- ============================================================================
-- Part III: The only rational roots of unity are ±1
-- ============================================================================

/-- **Rational roots of unity are ±1**: if `r : ℚ` is a primitive `n`-th root
    of unity, then `n ≤ 2`. Equivalently, the only roots of unity in ℚ are
    `1` (n = 1) and `-1` (n = 2). -/
theorem rational_root_of_unity_le_two {n : ℕ} {r : ℚ}
    (hn : 0 < n) (hr : IsPrimitiveRoot r n) : n ≤ 2 := by
  by_contra h
  have h3 : 3 ≤ n := by omega
  have hroot : (cyclotomic n ℚ).IsRoot r := hr.isRoot_cyclotomic hn
  exact cyclotomic_no_rational_root h3 r hroot

-- ============================================================================
-- Part IV: Complex primitive roots of unity are irrational
-- ============================================================================

/-- **Irrationality of cyclotomic roots**: a complex primitive `n`-th root of
    unity with `n ≥ 3` is not the image of any rational number; i.e. it is a
    genuine algebraic irrational. -/
theorem primitiveRoot_not_rational {n : ℕ} (hn : 3 ≤ n) {ζ : ℂ}
    (hζ : IsPrimitiveRoot ζ n) : ζ ∉ Set.range ((algebraMap ℚ ℂ) : ℚ → ℂ) := by
  rintro ⟨r, rfl⟩
  have hrat : IsPrimitiveRoot r n :=
    hζ.of_map_of_injective (algebraMap ℚ ℂ).injective
  have hle : n ≤ 2 := rational_root_of_unity_le_two (by omega) hrat
  omega

-- ============================================================================
-- Part V: Concrete instance
-- ============================================================================

/-- The complex number `e^{2πi/3}` (a primitive cube root of unity) is not
    rational. -/
theorem primitiveCubeRoot_not_rational :
    Complex.exp (2 * ↑Real.pi * Complex.I / (3 : ℕ)) ∉ Set.range ((algebraMap ℚ ℂ) : ℚ → ℂ) :=
  primitiveRoot_not_rational (by norm_num)
    (Complex.isPrimitiveRoot_exp 3 (by norm_num))

end

end NthRootIrrationalOQ01OQ01
