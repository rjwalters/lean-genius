/-
# OQ-04: Custom Lattice API vs ZLattice Comparison

**Gallery entry**: minkowski-fundamental-theorem-oq-04

This file formalizes the relationship between the custom `Lattice` type used in
the parent Minkowski proof and Mathlib's ZSpan/ZLattice infrastructure.

## Key Results

1. `covolume_eq_volume_fundamentalDomain`: |det(L.basis)| = vol(ZSpan.fundamentalDomain)
2. `basis_det_ne_zero`: invertible Basis gives nonzero determinant matrix
3. `Lattice.ofBasis`: every Module.Basis gives a custom Lattice
4. `minkowski_custom_via_zlattice`: custom Minkowski follows from ZSpan version

## Status: 4 sorries
-/

import Mathlib
import Proofs.MinkowskiFundamentalTheorem

open MeasureTheory ZSpan Matrix

namespace MinkowskiOQ04

variable {n : ℕ} [NeZero n]

-- ============================================================================
-- Part 1: Covolume equals ZSpan fundamental domain volume
-- ============================================================================

/-- The custom covolume |det(L.basis)| equals the volume of Mathlib's ZSpan fundamental domain.
    This is the central bridge between the custom API and Mathlib's geometry-of-numbers. -/
theorem covolume_eq_volume_fundamentalDomain (L : Lattice n) :
    ENNReal.ofReal L.covolume =
    volume (ZSpan.fundamentalDomain (L.toModuleBasis n)) := by
  rw [Lattice.covolume, ZSpan.volume_fundamentalDomain, L.toModuleBasis_matrix_eq n]

-- ============================================================================
-- Part 2: Invertible basis matrices have nonzero determinant
-- ============================================================================

/-- For any `Module.Basis (Fin n) ℝ (Fin n → ℝ)`, the corresponding matrix has
    nonzero determinant (since the basis vectors are linearly independent). -/
theorem basis_det_ne_zero (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    (Matrix.of (fun i => b i)).det ≠ 0 := by
  sorry

-- ============================================================================
-- Part 3: Module.Basis → custom Lattice
-- ============================================================================

/-- Every `Module.Basis (Fin n) ℝ (Fin n → ℝ)` gives a custom `Lattice n`.
    The basis matrix (row i = basis vector i) is invertible because the vectors
    form a basis. -/
noncomputable def Lattice.ofBasis (b : Basis (Fin n) ℝ (Fin n → ℝ)) : Lattice n where
  basis := Matrix.of (fun i => b i)
  basis_invertible := basis_det_ne_zero b

/-- Round-trip: `(Lattice.ofBasis b).toModuleBasis n = b` up to the change of basis. -/
theorem ofBasis_toModuleBasis (b : Basis (Fin n) ℝ (Fin n → ℝ)) :
    Matrix.of ((Lattice.ofBasis b).toModuleBasis n) = Matrix.of (fun i => b i) := by
  rw [(Lattice.ofBasis b).toModuleBasis_matrix_eq n]

-- ============================================================================
-- Part 4: ZSpan Minkowski implies custom Minkowski (without HasVolume class)
-- ============================================================================

/-- The ZSpan-native Minkowski theorem implies the custom-API version.
    Uses the covolume bridge: vol(fundamentalDomain) = ENNReal.ofReal L.covolume.

    Statement: if S ⊆ ℝⁿ is convex, centrally symmetric, and has measure > 2ⁿ * covolume(L),
    then S contains a nonzero lattice point. -/
theorem minkowski_custom_via_zlattice
    (L : Lattice n)
    (S : Set (Fin n → ℝ))
    (hS_meas : MeasurableSet S)
    (hS_conv : Convex ℝ S)
    (hS_sym : ∀ x ∈ S, -x ∈ S)
    (hS_vol : ENNReal.ofReal (2 ^ n * L.covolume) < volume S) :
    ∃ v ∈ S, v ≠ 0 ∧ v ∈ Submodule.span ℤ (Set.range (L.toModuleBasis n)) := by
  sorry

end MinkowskiOQ04
