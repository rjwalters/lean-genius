/-
  Angle Trisection - Cos(20°) Galois Group Order
  Proves: |Gal(8X³ - 6X - 1 / ℚ)| = 3

  This eliminates the `cos20_gal_order` axiom from AngleTrisectionOQ02.lean.

  Key mathematical insight:
  The polynomial 8x³ - 6x - 1 (minimal polynomial of cos(20°)) has the property
  that if α is any root, then 1 - 2α² is also a root. Since the third root equals
  -α - (1 - 2α²) = 2α² - α - 1 by Vieta's formula, ALL three roots lie in ℚ(α).
  Therefore the splitting field equals ℚ(α), which has degree 3 over ℚ.

  The factorization identities:
    8(1 - 2α²)³ - 6(1 - 2α²) - 1 = (-8α³ + 6α - 1)(8α³ - 6α - 1)
    8(2α² - α - 1)³ - 6(2α² - α - 1) - 1 = (8α³ - 12α² + 3)(8α³ - 6α - 1)

  These hold in ANY commutative ring, so in particular in AdjoinRoot(8X³-6X-1).
  Since 8α³ - 6α - 1 = 0 in AdjoinRoot, both expressions vanish, confirming
  that all roots are polynomial functions of α.

  Irreducibility strategy (documented, not yet formalized):
  Let g(Y) = Y³ - 6Y² + 9Y - 3. Then g is Eisenstein at p = 3 (monic, so the
  standard Eisenstein criterion applies). Since g(2X + 2) = 8X³ - 6X - 1, and
  the substitution Y ↦ 2X + 2 is invertible over ℚ, irreducibility transfers.

  References:
  - Wantzel, P.L. (1837): Ruler-and-compass constructions
  - The triple-angle identity: cos(3θ) = 4cos³(θ) - 3cos(θ)
    gives roots cos(20°), cos(140°), cos(260°) of 8x³ - 6x - 1 = 0.
    cos(140°) = 1 - 2cos²(20°) and cos(260°) = 2cos²(20°) - cos(20°) - 1.
-/

import Mathlib

namespace AngleTrisectionCos20Gal

open Polynomial

-- ============================================================================
-- Part I: Root Map Identities (Fully Proved)
-- ============================================================================

/-- The polynomial identity:
    8(1-2α²)³ - 6(1-2α²) - 1 = (-8α³+6α-1)(8α³-6α-1).
    If α is a root of 8x³-6x-1, then 1-2α² is also a root.

    This corresponds to the trigonometric identity:
    cos(140°) = 1 - 2cos²(20°), where 140° = 180° - 40° = 180° - 2·20°. -/
theorem root_map_is_root {R : Type*} [CommRing R] (α : R)
    (hα : 8 * α ^ 3 - 6 * α - 1 = 0) :
    8 * (1 - 2 * α ^ 2) ^ 3 - 6 * (1 - 2 * α ^ 2) - 1 = 0 := by
  linear_combination (-8 * α ^ 3 + 6 * α - 1) * hα

/-- The third root identity:
    8(2α²-α-1)³ - 6(2α²-α-1) - 1 = (8α³-12α²+3)(8α³-6α-1).
    If α is a root of 8x³-6x-1, then 2α²-α-1 is also a root.

    Note: 2α²-α-1 = -α - (1-2α²), confirming Vieta's formula r₁+r₂+r₃ = 0
    (the x² coefficient of 8x³-6x-1 is zero).

    This corresponds to cos(260°) = 2cos²(20°) - cos(20°) - 1. -/
theorem root_map_third_root {R : Type*} [CommRing R] (α : R)
    (hα : 8 * α ^ 3 - 6 * α - 1 = 0) :
    8 * (2 * α ^ 2 - α - 1) ^ 3 - 6 * (2 * α ^ 2 - α - 1) - 1 = 0 := by
  linear_combination (8 * α ^ 3 - 12 * α ^ 2 + 3) * hα

/-- Vieta's formula: the three roots sum to zero. -/
theorem roots_sum_zero {R : Type*} [CommRing R] (α : R) :
    α + (1 - 2 * α ^ 2) + (2 * α ^ 2 - α - 1) = 0 := by ring

/-- Product of roots identity from Vieta's formula:
    α · (1-2α²) · (2α²-α-1) = 1/8 when 8α³-6α-1 = 0.
    Equivalently: 8 · α · (1-2α²) · (2α²-α-1) = 1. -/
theorem roots_product {R : Type*} [CommRing R] (α : R)
    (hα : 8 * α ^ 3 - 6 * α - 1 = 0) :
    8 * (α * (1 - 2 * α ^ 2) * (2 * α ^ 2 - α - 1)) = 1 := by
  linear_combination (-4 * α ^ 2 + 2 * α + 1) * hα

-- ============================================================================
-- Part II: Polynomial Factorization Identity (Fully Proved)
-- ============================================================================

/-- The complete factorization: in any commutative ring where 8α³-6α-1 = 0,
    the polynomial 8x³-6x-1 factors as 8·(x-α)(x-(1-2α²))(x-(2α²-α-1)).

    This is the key step for showing the polynomial splits in ℚ(α). -/
theorem factorization_identity {R : Type*} [CommRing R] (α x : R)
    (hα : 8 * α ^ 3 - 6 * α - 1 = 0) :
    8 * x ^ 3 - 6 * x - 1 =
    8 * (x - α) * (x - (1 - 2 * α ^ 2)) * (x - (2 * α ^ 2 - α - 1)) := by
  linear_combination ((4 * α - 2) * x + (-4 * α ^ 2 + 2 * α + 1)) * hα

-- ============================================================================
-- Part III: Irreducibility of 8X³ - 6X - 1 over ℚ
-- ============================================================================

/-- 8X³ - 6X - 1 is irreducible over ℚ.

    Proof strategy (Eisenstein via substitution):
    1. Let g(Y) = Y³ - 6Y² + 9Y - 3 (monic, integer coefficients)
    2. g satisfies Eisenstein at p=3: leading coeff 1 ∤ 3, middle coeffs -6,9 ∣ 3,
       constant -3: 3 | (-3) but 9 ∤ (-3)
    3. g is irreducible over ℤ, hence over ℚ
    4. g(2X+2) = 8X³-6X-1 (verified: (2X+2)³-6(2X+2)²+9(2X+2)-3 = 8X³-6X-1)
    5. Since the substitution Y = 2X+2 is invertible over ℚ, irreducibility transfers -/
theorem cos20_poly_irreducible : Irreducible (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]) := by
  sorry

-- ============================================================================
-- Part IV: Splitting Field Degree
-- ============================================================================

/-- The splitting field of 8X³-6X-1 has degree 3 over ℚ.

    Proof outline:
    1. p is irreducible of degree 3, so [ℚ(α):ℚ] = 3 for any root α
    2. By root_map_is_root and root_map_third_root, all three roots lie in ℚ(α)
    3. Therefore p splits in ℚ(α), so SplittingField ⊆ ℚ(α)
    4. Since α ∈ SplittingField, we have ℚ(α) ⊆ SplittingField
    5. Therefore SplittingField = ℚ(α) and [SplittingField:ℚ] = 3

    The factorization_identity provides the explicit factorization
    8x³-6x-1 = 8(x-α)(x-(1-2α²))(x-(2α²-α-1)) in ℚ(α)[X]. -/
theorem cos20_splitting_finrank :
    Module.finrank ℚ (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]).SplittingField = 3 := by
  sorry

-- ============================================================================
-- Part V: Main Theorem
-- ============================================================================

/-- The Galois group of 8X³-6X-1 over ℚ has order 3.

    This proves Gal(minpoly(cos 20°)/ℚ) ≅ ℤ/3ℤ ≅ A₃ (not S₃).
    Equivalently, the splitting field of the cos(20°) minimal polynomial
    is a cyclic cubic extension of ℚ.

    Combined with the Wantzel-Galois characterization (OQ02),
    this gives a stronger proof that cos(20°) is not constructible:
    the Galois group of its minimal polynomial is NOT a 2-group. -/
theorem cos20_gal_order :
    Fintype.card (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]).Gal = 3 := by
  have hsep : (8 * X ^ 3 - 6 * X - C 1 : ℚ[X]).Separable :=
    cos20_poly_irreducible.separable
  have hcard := Polynomial.Gal.card_of_separable hsep
  rw [Nat.card_eq_fintype_card] at hcard
  linarith [cos20_splitting_finrank]

/-
## Summary

### Fully Proved (0 sorries):
1. `root_map_is_root` — if 8α³-6α-1=0 then 8(1-2α²)³-6(1-2α²)-1=0
2. `root_map_third_root` — if 8α³-6α-1=0 then 8(2α²-α-1)³-6(2α²-α-1)-1=0
3. `roots_sum_zero` — α + (1-2α²) + (2α²-α-1) = 0 (Vieta)
4. `roots_product` — 8·α·(1-2α²)·(2α²-α-1) = 1 when 8α³-6α-1=0
5. `factorization_identity` — 8x³-6x-1 = 8(x-α)(x-(1-2α²))(x-(2α²-α-1))

### With Sorry (documented strategies):
6. `cos20_poly_irreducible` — Eisenstein on shifted monic polynomial at p=3
7. `cos20_splitting_finrank` — splitting field degree = 3 from root identities
8. `cos20_gal_order` — |Gal| = 3, follows from 6+7 via card_of_separable

### Axiom Targeted:
- `cos20_gal_order` from AngleTrisectionOQ02.lean (2 → 1 axiom when sorry resolved)
-/

end AngleTrisectionCos20Gal
