/-
Pell's Equation OQ-08: Obstructions to the Negative Pell Equation x² − D y² = −1

The classical Pell equation x² − Dy² = 1 always has infinitely many integer
solutions for non-square D > 0 (the rank-1 case of Dirichlet's unit theorem). The
*negative* Pell equation

    x² − D y² = −1

is far more delicate: for many D it has **no** integer solution at all. Sibling
entry `PellEquationOQ06` builds the infinite solution chain for the smallest
solvable instance D = 2. This entry proves the complementary **non-existence**
(obstruction) side: congruence conditions on D that rule out any solution.

The key observation is purely local (mod p): a solution of `x² − D y² = −1`
forces `x² ≡ −1` in every residue ring where `D ≡ 0`. Since `−1` is a quadratic
residue mod an odd prime `p` iff `p ≢ 3 (mod 4)` (Mathlib's
`ZMod.mod_four_ne_three_of_sq_eq_neg_one`), a prime factor `p ≡ 3 (mod 4)` of `D`
is a fatal obstruction. A separate elementary `mod 4` count rules out every
`D ≡ 3 (mod 4)`.

Main results:
  • `neg_pell_no_sol_of_D_three_mod_four`
        — if D ≡ 3 (mod 4) then x² − D y² = −1 has no integer solution (mod-4 count).
  • `neg_pell_no_sol_of_prime_factor_three_mod_four`
        — if a prime p ≡ 3 (mod 4) divides D then x² − D y² = −1 has no solution.
  • `neg_pell_solvable_imp_no_prime_factor_three_mod_four`
        — solvability forces every prime factor of D to avoid the residue 3 (mod 4).
  • `neg_pell_three_no_sol`, `neg_pell_seven_no_sol`
        — the classical concrete obstructions D = 3 and D = 7.
  • `neg_pell_two_example`
        — D = 2 solves (contrast: 2 is not ≡ 3 mod 4), so the obstruction is sharp.

All proofs are `sorry`-free and axiom-free (no `native_decide`).

References:
- Parent entry: `pell-equation` (the norm `+1`, real-quadratic special case).
- Sibling: `PellEquationOQ06` (existence of the D = 2 solution chain).
- Mathlib `ZMod.exists_sq_eq_neg_one_iff` / `ZMod.mod_four_ne_three_of_sq_eq_neg_one`.
-/

import Mathlib

namespace PellEquationOQ08

/-
## The mod-4 obstruction
-/

/-- **`D ≡ 3 (mod 4)` obstruction.** If `D ≡ 3 (mod 4)`, the negative Pell
    equation `x² − D y² = −1` has no integer solution. Mod 4 the equation reads
    `x² + y² ≡ 3`, but `x² + y² ∈ {0, 1, 2}` mod 4, never `3`. -/
theorem neg_pell_no_sol_of_D_three_mod_four
    {D : ℤ} (hD : D % 4 = 3) (x y : ℤ) : x ^ 2 - D * y ^ 2 ≠ -1 := by
  intro h
  -- reduce the equation to `ZMod 4`
  have h4 : (x : ZMod 4) ^ 2 - (D : ZMod 4) * (y : ZMod 4) ^ 2 = -1 := by
    have h' : ((x ^ 2 - D * y ^ 2 : ℤ) : ZMod 4) = ((-1 : ℤ) : ZMod 4) := by rw [h]
    push_cast at h'
    exact h'
  -- `D ≡ 3 (mod 4)` becomes `(D : ZMod 4) = 3`
  have hD4 : (D : ZMod 4) = 3 := by
    have hmod : D ≡ 3 [ZMOD 4] := by show D % 4 = 3 % 4; omega
    have := (ZMod.intCast_eq_intCast_iff D 3 4).mpr hmod
    simpa using this
  rw [hD4] at h4
  -- exhaustive check over `ZMod 4`
  have hfin : ∀ a b : ZMod 4, a ^ 2 - 3 * b ^ 2 ≠ -1 := by decide
  exact hfin _ _ h4

/-
## The prime-factor obstruction
-/

/-- **Prime-factor obstruction.** If a prime `p ≡ 3 (mod 4)` divides `D`, then
    `x² − D y² = −1` has no integer solution: reducing mod `p` gives `x² ≡ −1`,
    but `−1` is not a square mod a prime `≡ 3 (mod 4)`. -/
theorem neg_pell_no_sol_of_prime_factor_three_mod_four
    {D : ℤ} {p : ℕ} (hp : p.Prime) (hp3 : p % 4 = 3) (hpD : (p : ℤ) ∣ D)
    (x y : ℤ) : x ^ 2 - D * y ^ 2 ≠ -1 := by
  intro h
  haveI : Fact p.Prime := ⟨hp⟩
  -- `p ∣ D` kills the `D`-term mod `p`
  have hD0 : (D : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd D p).mpr hpD
  -- reduce the equation mod `p` to `x² = −1`
  have hx2 : (x : ZMod p) ^ 2 = -1 := by
    have h' : ((x ^ 2 - D * y ^ 2 : ℤ) : ZMod p) = ((-1 : ℤ) : ZMod p) := by rw [h]
    push_cast at h'
    rw [hD0] at h'
    simpa using h'
  -- `−1` a square mod `p` forces `p ≢ 3 (mod 4)`, contradiction
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one hx2 hp3

/-- **Necessary condition for solvability.** If `x² − D y² = −1` has a solution,
    then no prime factor of `D` is congruent to `3 (mod 4)`. -/
theorem neg_pell_solvable_imp_no_prime_factor_three_mod_four
    {D : ℤ} (hsol : ∃ x y : ℤ, x ^ 2 - D * y ^ 2 = -1)
    {p : ℕ} (hp : p.Prime) (hpD : (p : ℤ) ∣ D) : p % 4 ≠ 3 := by
  intro hp3
  obtain ⟨x, y, h⟩ := hsol
  exact neg_pell_no_sol_of_prime_factor_three_mod_four hp hp3 hpD x y h

/-
## Concrete instances
-/

/-- The classical obstruction `x² − 3y² = −1` has no integer solution
    (`3 ≡ 3 mod 4`). -/
theorem neg_pell_three_no_sol (x y : ℤ) : x ^ 2 - 3 * y ^ 2 ≠ -1 :=
  neg_pell_no_sol_of_D_three_mod_four (by norm_num) x y

/-- The obstruction `x² − 7y² = −1` has no integer solution (`7 ≡ 3 mod 4`). -/
theorem neg_pell_seven_no_sol (x y : ℤ) : x ^ 2 - 7 * y ^ 2 ≠ -1 :=
  neg_pell_no_sol_of_D_three_mod_four (by norm_num) x y

/-- **Sharpness.** For `D = 2` (which is *not* `≡ 3 mod 4`) the equation *does*
    solve, e.g. `(x, y) = (1, 1)`: `1 − 2 = −1`. The obstructions above are
    therefore genuinely about the residue class of `D`, not vacuous. -/
theorem neg_pell_two_example : (1 : ℤ) ^ 2 - 2 * 1 ^ 2 = -1 := by norm_num

end PellEquationOQ08
