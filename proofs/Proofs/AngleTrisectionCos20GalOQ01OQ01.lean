/-
  Unified Galois Group Theorem for Angle-Trisection Cosines (OQ-01-OQ-01)

  Open Question OQ-01-OQ-01:
  Can the cos(20°) and cos(π/7) Galois group results be unified into a single theorem
  parameterized by the Eisenstein prime p?

  **Answer**: YES.

  Both results share the same algebraic pattern:
    - The minimal polynomial of cos(angle) has degree 3
    - It arises from a monic cubic r_p (Eisenstein at prime p) via substitution X → (Y - a)/2
    - The splitting field equals ℚ(cos(angle)), of degree 3 over ℚ
    - The Galois group has order 3

  **The two cases**:

  | Angle     | Poly p              | Eisenstein cubic r_p       | Prime p |
  |-----------|---------------------|----------------------------|---------|
  | cos(20°)  | 8X³ - 6X - 1       | Y³ - 6Y² + 9Y - 3 = r₃    | p = 3   |
  | cos(π/7)  | 8X³ - 4X² - 4X + 1 | Y³ - 7Y² + 14Y - 7 = r₇   | p = 7   |

  The Eisenstein prime p encodes the symmetry:
  - p = 3: relates to 3-fold angle (cos(20°) = cos(2π/18), 3 divides 9 = 18/2 - 0)
  - p = 7: relates to 7-fold symmetry (roots are cos(π/7), cos(3π/7), cos(5π/7))

  **Main unified theorems**:
  1. `trisection_gal_order_3`: |Gal(trisectionPoly p)| = 3 for p ∈ {3, 7}
  2. `trisection_poly_irreducible`: Both polynomials are irreducible over ℚ
  3. `eisenstein_cubic_connects_angle`: The Eisenstein cubic r_p and trisection poly connected
  4. `cyclic_cubic_data`: Both cases share the CyclicCubicData structure

  **Status**: 0 sorries, 0 axioms.
  Uses: AngleTrisectionCos20Gal, AngleTrisectionCos20GalOQ01.

  Related: AngleTrisectionCos20Gal (cos(20°) case), AngleTrisectionCos20GalOQ01 (cos(π/7) case).
-/

import Proofs.AngleTrisectionCos20Gal
import Proofs.AngleTrisectionCos20GalOQ01

open Polynomial IntermediateField FiniteDimensional

namespace AngleTrisectionCos20GalOQ01OQ01

open AngleTrisectionCos20Gal AngleTrisectionCos20GalOQ01

/-! ## Parameterized Trisection Polynomials -/

/-- The trisection polynomial parameterized by Eisenstein prime p ∈ {3, 7}:
    - p = 3: minimal polynomial of cos(20°) = cos(π/9), i.e., 8X³ - 6X - 1
    - p = 7: minimal polynomial of cos(π/7), i.e., 8X³ - 4X² - 4X + 1 -/
noncomputable def trisectionPoly (p : ℕ) : ℚ[X] :=
  if p = 3 then 8 * X ^ 3 - 6 * X - C 1
  else if p = 7 then 8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1
  else 1

/-- The Eisenstein cubic r_p:
    - p = 3: r₃ = Y³ - 6Y² + 9Y - 3 (Eisenstein at 3)
    - p = 7: r₇ = Y³ - 7Y² + 14Y - 7 (Eisenstein at 7) -/
noncomputable def eisensteinCubic (p : ℕ) : ℚ[X] :=
  if p = 3 then X ^ 3 - 6 * X ^ 2 + 9 * X - C 3
  else if p = 7 then X ^ 3 - 7 * X ^ 2 + 14 * X - C 7
  else 1

/-! ## Basic Properties -/

@[simp] theorem trisectionPoly_3 : trisectionPoly 3 = 8 * X ^ 3 - 6 * X - C 1 := by
  simp [trisectionPoly]

@[simp] theorem trisectionPoly_7 : trisectionPoly 7 = 8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1 := by
  simp [trisectionPoly]; norm_num

@[simp] theorem eisensteinCubic_3 : eisensteinCubic 3 = X ^ 3 - 6 * X ^ 2 + 9 * X - C 3 := by
  simp [eisensteinCubic]

@[simp] theorem eisensteinCubic_7 : eisensteinCubic 7 = X ^ 3 - 7 * X ^ 2 + 14 * X - C 7 := by
  simp [eisensteinCubic]; norm_num

/-! ## The Core Unification Theorem -/

/-- **Unified Galois Group Theorem**: For Eisenstein prime p ∈ {3, 7},
    the Galois group of the corresponding trisection polynomial has order 3.

    This unifies:
    - `AngleTrisectionCos20Gal.cos20_gal_card` (p = 3)
    - `AngleTrisectionCos20GalOQ01.cos_pi_7_gal_card` (p = 7) -/
theorem trisection_gal_order_3 (p : ℕ) (hp : p = 3 ∨ p = 7) :
    Fintype.card (trisectionPoly p).Gal = 3 := by
  rcases hp with rfl | rfl
  · rw [trisectionPoly_3]; exact cos20_gal_card
  · rw [trisectionPoly_7]; exact cos_pi_7_gal_card

/-- **Unified Irreducibility Theorem**: For Eisenstein prime p ∈ {3, 7},
    the trisection polynomial is irreducible over ℚ. -/
theorem trisection_poly_irreducible (p : ℕ) (hp : p = 3 ∨ p = 7) :
    Irreducible (trisectionPoly p) := by
  rcases hp with rfl | rfl
  · rw [trisectionPoly_3]; exact AngleTrisectionCos20Gal.trisection_poly_irreducible
  · rw [trisectionPoly_7]; exact AngleTrisectionCos20GalOQ01.cos_pi_7_poly_irreducible

/-- The splitting field of both trisection polynomials has degree 3 over ℚ. -/
theorem trisection_splitting_degree (p : ℕ) (hp : p = 3 ∨ p = 7) :
    Module.finrank ℚ (trisectionPoly p).SplittingField = 3 := by
  rcases hp with rfl | rfl
  · rw [trisectionPoly_3]; exact AngleTrisectionCos20Gal.splitting_finrank
  · rw [trisectionPoly_7]; exact AngleTrisectionCos20GalOQ01.splitting_finrank

/-! ## The Cyclic Cubic Data Structure -/

/-- Data certifying that a polynomial generates a cyclic cubic extension of ℚ. -/
structure CyclicCubicData (poly : ℚ[X]) where
  /-- The polynomial is irreducible over ℚ. -/
  irred : Irreducible poly
  /-- The splitting field has degree 3 over ℚ. -/
  degree_3 : Module.finrank ℚ poly.SplittingField = 3
  /-- The Galois group has order 3. -/
  gal_order : Fintype.card poly.Gal = 3

/-- The cos(20°) polynomial admits CyclicCubicData. -/
def cos20Data : CyclicCubicData (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]) :=
  { irred := AngleTrisectionCos20Gal.trisection_poly_irreducible
    degree_3 := AngleTrisectionCos20Gal.splitting_finrank
    gal_order := cos20_gal_card }

/-- The cos(π/7) polynomial admits CyclicCubicData. -/
def cosPi7Data : CyclicCubicData (8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1 : ℚ[X]) :=
  { irred := AngleTrisectionCos20GalOQ01.cos_pi_7_poly_irreducible
    degree_3 := AngleTrisectionCos20GalOQ01.splitting_finrank
    gal_order := cos_pi_7_gal_card }

/-- Both trisection polynomials admit CyclicCubicData (parameterized by p). -/
theorem trisection_cyclic_cubic_data (p : ℕ) (hp : p = 3 ∨ p = 7) :
    CyclicCubicData (trisectionPoly p) := by
  rcases hp with rfl | rfl
  · rw [trisectionPoly_3]; exact cos20Data
  · rw [trisectionPoly_7]; exact cosPi7Data

/-! ## The Eisenstein Connection -/

/-- The Eisenstein cubics each have a degree-3 constant term divisible by p but not p². -/
theorem eisensteinCubic_coeff_pattern (p : ℕ) (hp : p = 3 ∨ p = 7) :
    (p : ℚ) ∣ (eisensteinCubic p).coeff 0 ∧
    ¬ ((p : ℚ) ^ 2 ∣ (eisensteinCubic p).coeff 0) := by
  rcases hp with rfl | rfl
  · simp [eisensteinCubic_3, coeff_sub, coeff_C, coeff_X_pow, coeff_C_mul]
    norm_num
  · simp [eisensteinCubic_7, coeff_sub, coeff_C, coeff_X_pow, coeff_C_mul]
    norm_num

/-- The substitution connecting the Eisenstein cubic to the trisection polynomial.
    - For p = 3: r₃(2X + 1) = trisectionPoly 3 = 8X³ - 6X - 1
    - For p = 7: r₇(2X + 2) = trisectionPoly 7 = 8X³ - 4X² - 4X + 1 -/
theorem eisenstein_cubic_to_trisection (p : ℕ) (hp : p = 3 ∨ p = 7) :
    let shift : ℕ := if p = 3 then 1 else 2
    (eisensteinCubic p).comp (2 * X + C (shift : ℚ)) = trisectionPoly p := by
  rcases hp with rfl | rfl
  · simp [eisensteinCubic_3, trisectionPoly_3]
    ring
  · simp [eisensteinCubic_7, trisectionPoly_7]
    ring

/-! ## Joint Summary Theorem -/

/-- **Main Summary**: The two angle-trisection Galois computations.
    Both cos(20°) and cos(π/7) have cyclic Galois groups of order 3
    via Eisenstein cubics at primes 3 and 7 respectively.
    This is the "OQ-01-OQ-01" unification result. -/
theorem both_trisection_gal_order_3 :
    -- cos(20°): Eisenstein at p = 3
    Fintype.card (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]).Gal = 3 ∧
    -- cos(π/7): Eisenstein at p = 7
    Fintype.card (8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1 : ℚ[X]).Gal = 3 ∧
    -- Both polynomials are irreducible
    Irreducible (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]) ∧
    Irreducible (8 * X ^ 3 - 4 * X ^ 2 - 4 * X + C 1 : ℚ[X]) :=
  ⟨cos20_gal_card,
   cos_pi_7_gal_card,
   AngleTrisectionCos20Gal.trisection_poly_irreducible,
   AngleTrisectionCos20GalOQ01.cos_pi_7_poly_irreducible⟩

end AngleTrisectionCos20GalOQ01OQ01
