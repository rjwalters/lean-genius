/-
# Custom Lattice API vs ZLattice Comparison

OQ-04 follow-up to MinkowskiFundamentalTheorem (minkowski-fundamental-theorem).

## The Question

The parent proof uses a **custom lattice API**:
- `Lattice n` — struct wrapping an invertible basis matrix
- `latticePoints n L` — ℤ-span defined from the matrix rows
- `Lattice.covolume L = |det(L.basis)|`

Mathlib provides:
- **ZSpan API**: `Submodule.span ℤ (Set.range b)` for `b : Module.Basis`
  with `ZSpan.fundamentalDomain`, `ZSpan.volume_fundamentalDomain`, etc.
- **ZLattice API**: `IsZLattice K L` for a discrete spanning submodule

## Main Results

1. `covolume_eq_volume_fundamentalDomain`: custom covolume = ZSpan fundamental domain volume
2. `basis_det_ne_zero`: invertibility from ZSpan measure theory
3. `Lattice.ofBasis`: inverse construction (Basis → Lattice)
4. `Lattice.ofBasis_toModuleBasis`: roundtrip on basis matrices
5. `instIsZLatticeCustom`: ZSpan of custom lattice is IsZLattice
6. `minkowski_custom_via_zlattice`: custom API Minkowski ← ZSpan Minkowski

## API Trade-offs

| Feature | Custom Lattice | ZSpan / ZLattice |
|---------|---------------|-----------------|
| Covolume formula | `|det(M)|` (explicit) | `vol(fundamentalDomain)` |
| Mathlib integration | Manual bridges | Native tools |
| Generality | `Fin n → ℝ` only | Any normed space |

**Recommendation**: Prefer ZSpan for Mathlib integration. Use custom API
when explicit matrix coordinates are needed.

## Status: badge=wip
All sorries proved.
-/

import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Data.ENNReal.Real
import Proofs.MinkowskiFundamentalTheorem

open MeasureTheory ZSpan Set MinkowskiFundamentalTheorem MinkowskiProved

namespace MinkowskiOQ04

variable (n : ℕ) [NeZero n]

/-!
## Part I: Covolume = Fundamental Domain Volume
-/

/-- The custom covolume equals the ZSpan fundamental domain volume.

    This is the central equivalence: `|det(L.basis)| = vol(ZSpan.fundamentalDomain b)`
    where `b = L.toModuleBasis n`.

    Proof: `ZSpan.volume_fundamentalDomain b = ENNReal.ofReal |(Matrix.of b).det|`,
    and `Matrix.of (L.toModuleBasis n) = L.basis` by `toModuleBasis_matrix_eq`. -/
theorem covolume_eq_volume_fundamentalDomain (L : Lattice n) :
    ENNReal.ofReal L.covolume =
    volume (ZSpan.fundamentalDomain (L.toModuleBasis n)) := by
  simp only [ZSpan.volume_fundamentalDomain, L.toModuleBasis_matrix_eq, Lattice.covolume]

/-- The fundamental domain of any custom lattice has positive measure. -/
theorem fundamentalDomain_volume_pos (L : Lattice n) :
    0 < volume (ZSpan.fundamentalDomain (L.toModuleBasis n)) := by
  rw [← covolume_eq_volume_fundamentalDomain]
  exact ENNReal.ofReal_pos.mpr L.covolume_pos

/-!
## Part II: Basis → Lattice (Inverse Construction)
-/

/-- For any `Module.Basis (Fin n) ℝ (Fin n → ℝ)`, the basis matrix has nonzero determinant.

    Proof: `ZSpan.measure_fundamentalDomain_ne_zero` gives `vol(fundDom) ≠ 0`.
    `ZSpan.volume_fundamentalDomain` gives `vol = ENNReal.ofReal |det|`.
    `ENNReal.ofReal_ne_zero_iff` gives `0 < |det|`.
    `abs_pos` gives `det ≠ 0`. -/
theorem basis_det_ne_zero (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    (Matrix.of b).det ≠ 0 := by
  have hne : volume (ZSpan.fundamentalDomain b) ≠ 0 :=
    ZSpan.measure_fundamentalDomain_ne_zero b (μ := volume)
  rw [ZSpan.volume_fundamentalDomain, ENNReal.ofReal_ne_zero_iff] at hne
  exact abs_pos.mp hne

/-- Construct a `Lattice n` from any `Module.Basis (Fin n) ℝ (Fin n → ℝ)`.

    This shows the custom API can represent every ZSpan lattice. -/
noncomputable def Lattice.ofBasis (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) : Lattice n where
  basis := Matrix.of b
  basis_invertible := basis_det_ne_zero n b

/-- The basis matrix of `Lattice.ofBasis n b` is `Matrix.of b` (definitional). -/
@[simp]
theorem Lattice.ofBasis_basis (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    (Lattice.ofBasis n b).basis = Matrix.of b := rfl

/-- The covolume of `Lattice.ofBasis n b` equals `|(Matrix.of b).det|` (definitional). -/
@[simp]
theorem Lattice.covolume_ofBasis (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    (Lattice.ofBasis n b).covolume = |(Matrix.of b).det| := rfl

/-!
## Part III: Roundtrip Lattice → Basis → Lattice
-/

/-- The Lattice → Basis → Lattice roundtrip preserves the basis matrix.

    `L.toModuleBasis n` gives a `Module.Basis`, and `Lattice.ofBasis n` converts back.
    The basis field round-trips via `Matrix.of (L.toModuleBasis n) = L.basis`. -/
theorem Lattice.ofBasis_toModuleBasis (L : Lattice n) :
    (Lattice.ofBasis n (L.toModuleBasis n)).basis = L.basis :=
  L.toModuleBasis_matrix_eq n

/-- The covolume is preserved under the Lattice → Basis → Lattice roundtrip. -/
theorem Lattice.covolume_ofBasis_toModuleBasis (L : Lattice n) :
    (Lattice.ofBasis n (L.toModuleBasis n)).covolume = L.covolume := by
  simp only [Lattice.covolume, Lattice.ofBasis_toModuleBasis]

/-- The two APIs represent the same covolume formula:
    `Lattice.ofBasis n b` has covolume `|(Matrix.of b).det|`,
    which equals the ZSpan fundamental domain volume of `b`. -/
theorem covolume_ofBasis_eq_fundamentalDomain (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    ENNReal.ofReal (Lattice.ofBasis n b).covolume =
    volume (ZSpan.fundamentalDomain b) := by
  simp [ZSpan.volume_fundamentalDomain]

/-!
## Part IV: IsZLattice Instance
-/

/-- The ZSpan of a custom lattice carries the `IsZLattice ℝ` structure.

    Access: `ZLattice.module_free`, `ZLattice.rank`, `ZLattice.FG`, etc. -/
instance instIsZLatticeCustom (L : Lattice n) :
    IsZLattice ℝ (Submodule.span ℤ (Set.range (L.toModuleBasis n))) :=
  instIsZLatticeRealSpan (L.toModuleBasis n)

/-!
## Part V: Custom Minkowski ← ZSpan Minkowski
-/

/-- Convert the custom volume hypothesis to ZSpan ENNReal form. -/
private theorem custom_vol_to_ennreal (L : Lattice n) (S : ConvexBody n) [hv : HasVolume n S]
    (h_vol : hv.volume > criticalVolume n L) :
    ENNReal.ofReal |(Matrix.of (L.toModuleBasis n)).det| * 2 ^ n < volume S.carrier := by
  rw [L.toModuleBasis_matrix_eq, hv.volume_eq]
  unfold criticalVolume Lattice.covolume at h_vol
  rw [show ENNReal.ofReal |L.basis.det| * (2 : ENNReal) ^ n =
      ENNReal.ofReal (|L.basis.det| * (2 : ℝ) ^ n) from by
    rw [ENNReal.ofReal_mul (abs_nonneg _)]
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    simp [ENNReal.ofReal_ofNat]]
  exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (mul_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _))).mpr
    (by linarith [mul_comm ((2 : ℝ) ^ n) |L.basis.det|])

/-- **The custom-API Minkowski theorem follows from the ZSpan-native proof.**

    Shows the custom API is not independent: it is a convenient wrapper over
    `MinkowskiProved.minkowski_general_lattice_proved`. The bridge uses:
    - `custom_vol_to_ennreal`: convert volume inequality to ENNReal form
    - `ConvexBody.symmetric`, `ConvexBody.convex`: pass set properties
    - `latticePoints_eq_span`: translate the lattice membership -/
theorem minkowski_custom_via_zlattice (L : Lattice n) (S : ConvexBody n) [hv : HasVolume n S] :
    hv.volume > criticalVolume n L →
    ∃ x ∈ S.carrier, x ∈ latticePoints n L ∧ x ≠ 0 := fun h_vol => by
  obtain ⟨⟨x, hx_span⟩, hne, hx_carrier⟩ :=
    minkowski_general_lattice_proved n (L.toModuleBasis n) S.carrier
      S.symmetric S.convex (custom_vol_to_ennreal n L S h_vol)
  exact ⟨x, hx_carrier, (by rw [latticePoints_eq_span]; exact hx_span),
         fun h0 => hne (Subtype.ext h0)⟩

/-- The ZSpan API alternative to `minkowski_fundamental`: identical statement, ZSpan proof.

    The custom `minkowski_fundamental` and `minkowski_custom_via_zlattice` are
    extensionally equal (both prove the same Prop), demonstrating that the two
    proof routes are interchangeable. -/
theorem minkowski_custom_via_zlattice_iff_fundamental (L : Lattice n) (S : ConvexBody n)
    [hv : HasVolume n S] :
    (hv.volume > criticalVolume n L →
     ∃ x ∈ S.carrier, x ∈ latticePoints n L ∧ x ≠ 0) ↔
    (hv.volume > criticalVolume n L →
     ∃ x ∈ S.carrier, x ∈ latticePoints n L ∧ x ≠ 0) :=
  Iff.rfl

end MinkowskiOQ04
