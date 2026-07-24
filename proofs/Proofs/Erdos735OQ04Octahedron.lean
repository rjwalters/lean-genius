/-
  Erdős Problem #735, Open Question #04 (oq-04) — S6b ACT:
  The regular octahedron is NOT a 2-flat-magic configuration in ℝ³.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).

  This file ships the refutation half of the S6 polytope programme (S6b PREP,
  sessions/2026-05-13-s6b-prep-octahedron-cube-not-2-flat-magic.md): the S1
  OBSERVE claim that the regular octahedron

      v₁ = ( 1, 0, 0),  v₂ = (-1, 0, 0),  v₃ = (0,  1, 0),
      v₄ = (0, -1, 0),  v₅ = (0, 0,  1),  v₆ = (0, 0, -1)

  is 2-flat magic is FALSE: no positive weighting makes all minimal-spanning
  2-flats carry the same weight-sum. Together with the S6a tetrahedron
  certificate (`Proofs.Erdos735OQ04Tetrahedron`), this pins the shape of the
  conjectured `k ≥ 2` magic family: it contains the tetrahedron but NOT the
  octahedron — "regular polytopes" is not the right class.

  ## Proof architecture (4-flat linear-arithmetic route)

  The S6b PREP refutes via O_h symmetry averaging (48-element group). This
  file uses a much lighter route needing only FOUR explicit 2-flats:

    * `flatZ` — the coordinate plane z = 0, containing v₁, v₂, v₃, v₄;
    * `flatY` — the coordinate plane y = 0, containing v₁, v₂, v₅, v₆;
    * `flatP` — the face plane x + y + z =  1, containing v₁, v₃, v₅;
    * `flatM` — the face plane x + y + z = -1, containing v₂, v₄, v₆.

  If `w` were a magic weighting with constant `c`, writing `aᵢ` for the weight
  of `vᵢ`:

      (flatZ)  a₁ + a₂ + a₃ + a₄ = c
      (flatY)  a₁ + a₂ + a₅ + a₆ = c
      (flatP)  a₁ + a₃ + a₅      = c
      (flatM)  a₂ + a₄ + a₆      = c

  Adding the first two and subtracting the last two gives `a₁ + a₂ = 0`,
  contradicting positivity. `linarith` closes it.

  Each flat is built as `AffineSubspace.mk'` over the kernel of an explicit
  linear functional (`EuclideanSpace.projₗ` / their sum), so every point
  membership is a one-line coordinate check and the direction rank is 2 by
  rank-nullity — no affine-independence case analysis is needed anywhere.

  Counts: 0 axioms, 0 sorries.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Proofs.Erdos735OQ04

namespace Erdos735OQ04Octa

open Erdos735OQ04
open scoped Classical

/- ## The six octahedron vertices -/

/-- Octahedron vertex `( 1, 0, 0)`. -/
noncomputable def p₁ : EuclideanSpace ℝ (Fin 3) := !₂[ 1,  0,  0]
/-- Octahedron vertex `(-1, 0, 0)`. -/
noncomputable def p₂ : EuclideanSpace ℝ (Fin 3) := !₂[-1,  0,  0]
/-- Octahedron vertex `( 0, 1, 0)`. -/
noncomputable def p₃ : EuclideanSpace ℝ (Fin 3) := !₂[ 0,  1,  0]
/-- Octahedron vertex `( 0,-1, 0)`. -/
noncomputable def p₄ : EuclideanSpace ℝ (Fin 3) := !₂[ 0, -1,  0]
/-- Octahedron vertex `( 0, 0, 1)`. -/
noncomputable def p₅ : EuclideanSpace ℝ (Fin 3) := !₂[ 0,  0,  1]
/-- Octahedron vertex `( 0, 0,-1)`. -/
noncomputable def p₆ : EuclideanSpace ℝ (Fin 3) := !₂[ 0,  0, -1]

/-- The regular octahedron as a `PointConfigD 3`. -/
noncomputable def octaConfig : PointConfigD 3 := {p₁, p₂, p₃, p₄, p₅, p₆}

/-- Two points of ℝ³ differing in some coordinate are distinct. -/
lemma ne_of_coord {x y : EuclideanSpace ℝ (Fin 3)} (j : Fin 3)
    (h : WithLp.ofLp x j ≠ WithLp.ofLp y j) : x ≠ y :=
  fun he => h (by rw [he])

/- Pairwise distinctness of the vertices used below. -/

lemma p12 : p₁ ≠ p₂ := ne_of_coord 0 (by norm_num [p₁, p₂, WithLp.ofLp_toLp])
lemma p13 : p₁ ≠ p₃ := ne_of_coord 0 (by norm_num [p₁, p₃, WithLp.ofLp_toLp])
lemma p14 : p₁ ≠ p₄ := ne_of_coord 0 (by norm_num [p₁, p₄, WithLp.ofLp_toLp])
lemma p15 : p₁ ≠ p₅ := ne_of_coord 0 (by norm_num [p₁, p₅, WithLp.ofLp_toLp])
lemma p16 : p₁ ≠ p₆ := ne_of_coord 0 (by norm_num [p₁, p₆, WithLp.ofLp_toLp])
lemma p23 : p₂ ≠ p₃ := ne_of_coord 0 (by norm_num [p₂, p₃, WithLp.ofLp_toLp])
lemma p24 : p₂ ≠ p₄ := ne_of_coord 0 (by norm_num [p₂, p₄, WithLp.ofLp_toLp])
lemma p25 : p₂ ≠ p₅ := ne_of_coord 0 (by norm_num [p₂, p₅, WithLp.ofLp_toLp])
lemma p26 : p₂ ≠ p₆ := ne_of_coord 0 (by norm_num [p₂, p₆, WithLp.ofLp_toLp])
lemma p34 : p₃ ≠ p₄ := ne_of_coord 1 (by norm_num [p₃, p₄, WithLp.ofLp_toLp])
lemma p35 : p₃ ≠ p₅ := ne_of_coord 1 (by norm_num [p₃, p₅, WithLp.ofLp_toLp])
lemma p46 : p₄ ≠ p₆ := ne_of_coord 1 (by norm_num [p₄, p₆, WithLp.ofLp_toLp])
lemma p56 : p₅ ≠ p₆ := ne_of_coord 2 (by
  norm_num [p₅, p₆, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

/- ## Hyperplane flats as kernels of linear functionals -/

/-- Coordinate functional `x ↦ xⱼ` on ℝ³ (bundled linear map). -/
noncomputable def coordL (j : Fin 3) : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  EuclideanSpace.projₗ j

lemma coordL_apply (j : Fin 3) (x : EuclideanSpace ℝ (Fin 3)) :
    coordL j x = WithLp.ofLp x j := rfl

/-- Sum-of-coordinates functional `x ↦ x₀ + x₁ + x₂` on ℝ³. -/
noncomputable def sumL : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  coordL 0 + coordL 1 + coordL 2

lemma sumL_apply (x : EuclideanSpace ℝ (Fin 3)) :
    sumL x = WithLp.ofLp x 0 + WithLp.ofLp x 1 + WithLp.ofLp x 2 := rfl

/-- Membership in an affine subspace `mk' p (ker φ)` is the linear equation
    `φ x = φ p`. -/
lemma mem_mk'_ker_iff (φ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (p x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ AffineSubspace.mk' p (LinearMap.ker φ) ↔ φ x = φ p := by
  rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, sub_eq_zero]

/-- Rank-nullity: the kernel of a linear functional on ℝ³ that is nonzero
    somewhere is a rank-2 subspace. -/
lemma rank_ker_two (φ : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ)
    (x₀ : EuclideanSpace ℝ (Fin 3)) (hx₀ : φ x₀ ≠ 0) :
    Module.rank ℝ (LinearMap.ker φ) = ((2 : ℕ) : Cardinal) := by
  have hsurj : Function.Surjective φ := fun c =>
    ⟨(c / φ x₀) • x₀, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx₀]⟩
  have hrange : LinearMap.range φ = ⊤ := LinearMap.range_eq_top.mpr hsurj
  have h := φ.finrank_range_add_finrank_ker
  rw [hrange, finrank_top, Module.finrank_self, finrank_euclideanSpace_fin] at h
  have hk : Module.finrank ℝ (LinearMap.ker φ) = 2 := by omega
  rw [← Module.finrank_eq_rank, hk]

/-- The coordinate plane `z = 0`. -/
noncomputable def flatZ : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' 0 (LinearMap.ker (coordL 2))

/-- The coordinate plane `y = 0`. -/
noncomputable def flatY : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' 0 (LinearMap.ker (coordL 1))

/-- The face plane `x + y + z = 1`. -/
noncomputable def flatP : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' p₁ (LinearMap.ker sumL)

/-- The face plane `x + y + z = -1`. -/
noncomputable def flatM : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' p₂ (LinearMap.ker sumL)

lemma mem_flatZ_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatZ ↔ WithLp.ofLp x 2 = 0 := by
  rw [flatZ, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp

lemma mem_flatY_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatY ↔ WithLp.ofLp x 1 = 0 := by
  rw [flatY, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp

lemma mem_flatP_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatP ↔ WithLp.ofLp x 0 + WithLp.ofLp x 1 + WithLp.ofLp x 2 = 1 := by
  rw [flatP, mem_mk'_ker_iff, sumL_apply, sumL_apply]
  simp [p₁, WithLp.ofLp_toLp]

lemma mem_flatM_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatM ↔ WithLp.ofLp x 0 + WithLp.ofLp x 1 + WithLp.ofLp x 2 = -1 := by
  rw [flatM, mem_mk'_ker_iff, sumL_apply, sumL_apply]
  simp [p₂, WithLp.ofLp_toLp]

/- ## Direction ranks -/

lemma rank_flatZ : Module.rank ℝ flatZ.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatZ, AffineSubspace.direction_mk']
  exact rank_ker_two _ p₅ (by rw [coordL_apply]; simp [p₅, WithLp.ofLp_toLp])

lemma rank_flatY : Module.rank ℝ flatY.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatY, AffineSubspace.direction_mk']
  exact rank_ker_two _ p₃ (by rw [coordL_apply]; simp [p₃, WithLp.ofLp_toLp])

lemma rank_sumL_ker : Module.rank ℝ (LinearMap.ker sumL) = ((2 : ℕ) : Cardinal) :=
  rank_ker_two _ p₁ (by rw [sumL_apply]; simp [p₁, WithLp.ofLp_toLp])

lemma rank_flatP : Module.rank ℝ flatP.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatP, AffineSubspace.direction_mk']
  exact rank_sumL_ker

lemma rank_flatM : Module.rank ℝ flatM.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatM, AffineSubspace.direction_mk']
  exact rank_sumL_ker

/- ## Vertex membership decisions -/

lemma hZ1 : p₁ ∈ flatZ := (mem_flatZ_iff p₁).mpr (by simp [p₁, WithLp.ofLp_toLp])
lemma hZ2 : p₂ ∈ flatZ := (mem_flatZ_iff p₂).mpr (by simp [p₂, WithLp.ofLp_toLp])
lemma hZ3 : p₃ ∈ flatZ := (mem_flatZ_iff p₃).mpr (by simp [p₃, WithLp.ofLp_toLp])
lemma hZ4 : p₄ ∈ flatZ := (mem_flatZ_iff p₄).mpr (by simp [p₄, WithLp.ofLp_toLp])
lemma hZ5 : p₅ ∉ flatZ := by
  rw [mem_flatZ_iff]; simp [p₅, WithLp.ofLp_toLp]
lemma hZ6 : p₆ ∉ flatZ := by
  rw [mem_flatZ_iff]; simp [p₆, WithLp.ofLp_toLp]

lemma hY1 : p₁ ∈ flatY := (mem_flatY_iff p₁).mpr (by simp [p₁, WithLp.ofLp_toLp])
lemma hY2 : p₂ ∈ flatY := (mem_flatY_iff p₂).mpr (by simp [p₂, WithLp.ofLp_toLp])
lemma hY3 : p₃ ∉ flatY := by
  rw [mem_flatY_iff]; simp [p₃, WithLp.ofLp_toLp]
lemma hY4 : p₄ ∉ flatY := by
  rw [mem_flatY_iff]; simp [p₄, WithLp.ofLp_toLp]
lemma hY5 : p₅ ∈ flatY := (mem_flatY_iff p₅).mpr (by simp [p₅, WithLp.ofLp_toLp])
lemma hY6 : p₆ ∈ flatY := (mem_flatY_iff p₆).mpr (by simp [p₆, WithLp.ofLp_toLp])

lemma hP1 : p₁ ∈ flatP := (mem_flatP_iff p₁).mpr (by simp [p₁, WithLp.ofLp_toLp])
lemma hP2 : p₂ ∉ flatP := by
  rw [mem_flatP_iff]; simp [p₂, WithLp.ofLp_toLp]; norm_num
lemma hP3 : p₃ ∈ flatP := (mem_flatP_iff p₃).mpr (by simp [p₃, WithLp.ofLp_toLp])
lemma hP4 : p₄ ∉ flatP := by
  rw [mem_flatP_iff]; simp [p₄, WithLp.ofLp_toLp]; norm_num
lemma hP5 : p₅ ∈ flatP := (mem_flatP_iff p₅).mpr (by simp [p₅, WithLp.ofLp_toLp])
lemma hP6 : p₆ ∉ flatP := by
  rw [mem_flatP_iff]; simp [p₆, WithLp.ofLp_toLp]; norm_num

lemma hM1 : p₁ ∉ flatM := by
  rw [mem_flatM_iff]; simp [p₁, WithLp.ofLp_toLp]; norm_num
lemma hM2 : p₂ ∈ flatM := (mem_flatM_iff p₂).mpr (by simp [p₂, WithLp.ofLp_toLp])
lemma hM3 : p₃ ∉ flatM := by
  rw [mem_flatM_iff]; simp [p₃, WithLp.ofLp_toLp]; norm_num
lemma hM4 : p₄ ∈ flatM := (mem_flatM_iff p₄).mpr (by simp [p₄, WithLp.ofLp_toLp])
lemma hM5 : p₅ ∉ flatM := by
  rw [mem_flatM_iff]; simp [p₅, WithLp.ofLp_toLp]; norm_num
lemma hM6 : p₆ ∈ flatM := (mem_flatM_iff p₆).mpr (by simp [p₆, WithLp.ofLp_toLp])

/- ## Filtered point sets of the four flats -/

lemma filter_flatZ : octaConfig.filter (· ∈ flatZ) = {p₁, p₂, p₃, p₄} := by
  rw [octaConfig]
  rw [Finset.filter_insert, if_pos hZ1, Finset.filter_insert, if_pos hZ2,
    Finset.filter_insert, if_pos hZ3, Finset.filter_insert, if_pos hZ4,
    Finset.filter_insert, if_neg hZ5, Finset.filter_singleton, if_neg hZ6]
  rfl

lemma filter_flatY : octaConfig.filter (· ∈ flatY) = {p₁, p₂, p₅, p₆} := by
  rw [octaConfig]
  rw [Finset.filter_insert, if_pos hY1, Finset.filter_insert, if_pos hY2,
    Finset.filter_insert, if_neg hY3, Finset.filter_insert, if_neg hY4,
    Finset.filter_insert, if_pos hY5, Finset.filter_singleton, if_pos hY6]

lemma filter_flatP : octaConfig.filter (· ∈ flatP) = {p₁, p₃, p₅} := by
  rw [octaConfig]
  rw [Finset.filter_insert, if_pos hP1, Finset.filter_insert, if_neg hP2,
    Finset.filter_insert, if_pos hP3, Finset.filter_insert, if_neg hP4,
    Finset.filter_insert, if_pos hP5, Finset.filter_singleton, if_neg hP6]
  rfl

lemma filter_flatM : octaConfig.filter (· ∈ flatM) = {p₂, p₄, p₆} := by
  rw [octaConfig]
  rw [Finset.filter_insert, if_neg hM1, Finset.filter_insert, if_pos hM2,
    Finset.filter_insert, if_neg hM3, Finset.filter_insert, if_pos hM4,
    Finset.filter_insert, if_neg hM5, Finset.filter_singleton, if_pos hM6]

/- Non-membership facts for insert-chain card/sum computations. -/

lemma n1Z : p₁ ∉ ({p₂, p₃, p₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p12, p13, p14]
lemma n2Z : p₂ ∉ ({p₃, p₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p23, p24]
lemma n3Z : p₃ ∉ ({p₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p34]

lemma n1Y : p₁ ∉ ({p₂, p₅, p₆} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p12, p15, p16]
lemma n2Y : p₂ ∉ ({p₅, p₆} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p25, p26]
lemma n5Y : p₅ ∉ ({p₆} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p56]

lemma n1P : p₁ ∉ ({p₃, p₅} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p13, p15]
lemma n3P : p₃ ∉ ({p₅} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p35]

lemma n2M : p₂ ∉ ({p₄, p₆} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p24, p26]
lemma n4M : p₄ ∉ ({p₆} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [p46]

/- ## The four flats as `ConfigKFlat 2 octaConfig` elements -/

lemma card_flatZ : (octaConfig.filter (· ∈ flatZ)).card ≥ 2 + 1 := by
  rw [filter_flatZ, Finset.card_insert_of_notMem n1Z,
    Finset.card_insert_of_notMem n2Z, Finset.card_insert_of_notMem n3Z,
    Finset.card_singleton]
  omega

lemma card_flatY : (octaConfig.filter (· ∈ flatY)).card ≥ 2 + 1 := by
  rw [filter_flatY, Finset.card_insert_of_notMem n1Y,
    Finset.card_insert_of_notMem n2Y, Finset.card_insert_of_notMem n5Y,
    Finset.card_singleton]
  omega

lemma card_flatP : (octaConfig.filter (· ∈ flatP)).card ≥ 2 + 1 := by
  rw [filter_flatP, Finset.card_insert_of_notMem n1P,
    Finset.card_insert_of_notMem n3P, Finset.card_singleton]

lemma card_flatM : (octaConfig.filter (· ∈ flatM)).card ≥ 2 + 1 := by
  rw [filter_flatM, Finset.card_insert_of_notMem n2M,
    Finset.card_insert_of_notMem n4M, Finset.card_singleton]

/- ## Main theorem -/

/-- **The regular octahedron is NOT 2-flat magic.**  The four flats `flatZ`,
    `flatY`, `flatP`, `flatM` force `a₁ + a₂ = 0` for any magic weighting,
    contradicting positivity.  (S6b ACT; refutes the S1 OBSERVE octahedron
    claim, complementing the S6a tetrahedron existence certificate.) -/
theorem octa_not_isKFlatMagic : ¬ IsKFlatMagic 2 octaConfig := by
  rintro ⟨w, c, hc, hmagic⟩
  -- canonical membership proofs (fixed once, so weight atoms are shared)
  have hp₁ : p₁ ∈ octaConfig := by simp [octaConfig]
  have hp₂ : p₂ ∈ octaConfig := by simp [octaConfig]
  have hp₃ : p₃ ∈ octaConfig := by simp [octaConfig]
  have hp₄ : p₄ ∈ octaConfig := by simp [octaConfig]
  have hp₅ : p₅ ∈ octaConfig := by simp [octaConfig]
  have hp₆ : p₆ ∈ octaConfig := by simp [octaConfig]
  -- the four flat-sum equations
  have eZ := hmagic ⟨flatZ, rank_flatZ, card_flatZ⟩
  have eY := hmagic ⟨flatY, rank_flatY, card_flatY⟩
  have eP := hmagic ⟨flatP, rank_flatP, card_flatP⟩
  have eM := hmagic ⟨flatM, rank_flatM, card_flatM⟩
  simp only [kFlatSum] at eZ eY eP eM
  rw [filter_flatZ, Finset.sum_insert n1Z, Finset.sum_insert n2Z,
    Finset.sum_insert n3Z, Finset.sum_singleton] at eZ
  rw [filter_flatY, Finset.sum_insert n1Y, Finset.sum_insert n2Y,
    Finset.sum_insert n5Y, Finset.sum_singleton] at eY
  rw [filter_flatP, Finset.sum_insert n1P, Finset.sum_insert n3P,
    Finset.sum_singleton] at eP
  rw [filter_flatM, Finset.sum_insert n2M, Finset.sum_insert n4M,
    Finset.sum_singleton] at eM
  simp only [dif_pos hp₁, dif_pos hp₂, dif_pos hp₃, dif_pos hp₄,
    dif_pos hp₅, dif_pos hp₆] at eZ eY eP eM
  -- positivity of the six weights
  have h1 := w.property ⟨p₁, hp₁⟩
  have h2 := w.property ⟨p₂, hp₂⟩
  -- (flatZ) + (flatY) − (flatP) − (flatM) gives a₁ + a₂ = 0; contradiction
  linarith

end Erdos735OQ04Octa
