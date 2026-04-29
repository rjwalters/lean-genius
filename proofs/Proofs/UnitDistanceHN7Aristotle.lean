/-
  Aristotle targets for UnitDistanceHN7
  Routine supporting lemmas for automated proof search.
  See UnitDistanceHN7.lean for the main Hadwiger-Nelson upper bound (χ(ℝ²) ≤ 7).

  Status (2026-04-29): only the geometric covering-radius obligation remains as a sorry.
  hexCenter_dist_sq and the modular-arithmetic step (hexColor_eq_implies_mod) are now
  proved here as well (the latter mirrors the inline step in same_color_far).

  Criteria for inclusion:
  - NOT the main Hadwiger-Nelson theorem (follows from the supporting lemmas above)
  - Standalone theorems (sorries at theorem level, not buried in proofs)
  - No definition sorries, no axiom declarations, no open conjectures
  - No /-! docstring sections (use /- instead)
-/
import Proofs.UnitDistanceHN7
import Mathlib

open EuclideanSpace Real

namespace UnitDistanceHN7Aristotle

/-
## Target 1: Algebraic Distance Formula for Hex Centers

The A₂ lattice with basis e₁ = (s√3, 0), e₂ = (s√3/2, 3s/2) has center-to-center
squared distance equal to 3s²·(Δa² + Δa·Δb + Δb²) where s = hexSideLength.

Proof: Let da = a₁ - a₂, db = b₁ - b₂.
  Δx = s√3·(da + db/2), Δy = 3s/2·db
  Δx² + Δy² = 3s²·da² + 3s²·da·db + 3s²/4·db² + 9s²/4·db²
             = 3s²·(da² + da·db + db²)
-/

/-- Algebraic identity: squared distance between A₂ hex centers equals 3s²·Q(Δa,Δb). -/
theorem hexCenter_dist_sq_ari (a₁ b₁ a₂ b₂ : ℤ) :
    dist (hexCenter a₁ b₁) (hexCenter a₂ b₂) ^ 2 =
    3 * hexSideLength ^ 2 *
      (((a₁ : ℝ) - a₂) ^ 2 + ((a₁ : ℝ) - a₂) * ((b₁ : ℝ) - b₂) +
       ((b₁ : ℝ) - b₂) ^ 2) :=
  hexCenter_dist_sq a₁ b₁ a₂ b₂

/-
## Target 2: Hex Color Equality Implies Lattice Mod Condition

The hexColor function assigns color (3q + r) mod 7 to lattice coordinates (q, r).
If two lattice cells have the same color, then 3·(q₁-q₂) + (r₁-r₂) ≡ 0 (mod 7).
-/

/-- If two points have the same hexColor, their hexCoord satisfy the mod 7 condition. -/
theorem hexColor_eq_implies_mod_ari (p q : Plane)
    (hcolor : hexColor p = hexColor q) :
    (3 * ((hexCoord p).1 - (hexCoord q).1) + ((hexCoord p).2 - (hexCoord q).2)) % 7 = 0 := by
  set a₁ := (hexCoord p).1
  set b₁ := (hexCoord p).2
  set a₂ := (hexCoord q).1
  set b₂ := (hexCoord q).2
  simp only [hexColor, Fin.mk.injEq] at hcolor
  have h₁_pos : 0 ≤ (3 * a₁ + b₁) % 7 := Int.emod_nonneg _ (by norm_num)
  have h₂_pos : 0 ≤ (3 * a₂ + b₂) % 7 := Int.emod_nonneg _ (by norm_num)
  have h₁_lt : (3 * a₁ + b₁) % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
  have h₂_lt : (3 * a₂ + b₂) % 7 < 7 := Int.emod_lt_of_pos _ (by norm_num)
  omega

/-
## Target 3: Covering Radius of A₂ Lattice

Every point of the plane lies within distance s = hexSideLength of the center
of its assigned Voronoi hex cell. The cube-coordinate rounding algorithm in
hexCoord assigns each point to the nearest lattice site.
-/

/-- Every point is within distance hexSideLength of its assigned hex center. -/
theorem covering_radius_ari (p : Plane) :
    dist p (hexCenter (hexCoord p).1 (hexCoord p).2) ≤ hexSideLength := by
  sorry

end UnitDistanceHN7Aristotle
