/-
  Erdős Problem #735, Open Question #04 (oq-04) — S6d ACT (part ii):
  The regular dodecahedron is NOT a 2-flat-magic configuration in ℝ³.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).
  Sibling: `Proofs.Erdos735OQ04Octahedron` (S6b — octahedron refutation),
  whose generic helpers (`coordL`, `mem_mk'_ker_iff`, `rank_ker_two`,
  `ne_of_coord`) this file reuses, and
  `Proofs.Erdos735OQ04Icosahedron` (S6d part i), whose golden-ratio toolkit
  (`phi_sq`, `one_lt_phi`, `phi_lt_two`) is reproduced here in this file's
  namespace.

  This completes the S6d milestone (and with it the full Platonic-solid
  audit): the regular dodecahedron at the standard coordinates — the eight
  cube vertices `(±1, ±1, ±1)` together with the cyclic golden-ratio points
  `(0, ±1/φ, ±φ)`, `(±1/φ, ±φ, 0)`, `(±φ, 0, ±1/φ)`, where `φ = (1+√5)/2`
  and `1/φ = φ − 1` —

      c₁…c₈  = (±1, ±1, ±1)              (cube vertices)
      x₁…x₄  = (±(φ−1), ±φ, 0)
      y₁…y₄  = (0, ±(φ−1), ±φ)
      z₁…z₄  = (±φ, 0, ±(φ−1))

  is NOT 2-flat magic: no positive weighting gives all determined 2-flats the
  same weight-sum.  Of the five Platonic solids only the tetrahedron (a
  simplex, hence affinely independent) is 2-flat magic — consistent with the
  S6e general-position theorem.

  ## Proof architecture (8-flat linear-arithmetic route)

  Eight explicit 2-flats suffice; remarkably, the certificate never even
  invokes positivity of the individual weights — the eight equations already
  force the magic constant `c` itself to vanish:

    * four pentagonal **face planes** with normals `(±φ, ±1, 0)`:
        `flatG1` : φx + y =  φ+1   (c₁, c₂, x₁, z₁, z₂)
        `flatG2` : φx − y =  φ+1   (c₃, c₄, x₂, z₁, z₂)
        `flatG3` : φx − y = −(φ+1) (c₅, c₆, x₃, z₃, z₄)
        `flatG4` : φx + y = −(φ+1) (c₇, c₈, x₄, z₃, z₄)
      (the plane identities for the `x`- and `z`-vertices are exactly
      `φ² = φ + 1`);
    * two **cube-face planes** `flatX1 : x = 1` (c₁…c₄) and
      `flatX2 : x = −1` (c₅…c₈);
    * two **coordinate planes** `flatZ0 : z = 0` (x₁…x₄) and
      `flatY0 : y = 0` (z₁…z₄).

  If `w` were a magic weighting with constant `c > 0`, writing the flat-sum
  equations and combining

      (G1 + G2 + G3 + G4) − (X1 + X2) − Z0 − 2·Y0

  cancels every weight exactly (the four faces cover the cube vertices once,
  the `x`-vertices once, and the `z`-vertices twice), leaving `0 = −c` —
  contradicting `c > 0`.  `linarith` closes it.

  All golden-ratio arithmetic reduces to three facts proved once:
  `φ² = φ + 1`, `1 < φ`, `φ < 2` (the latter two from `2 < √5 < 3`).

  Counts: 0 axioms, 0 sorries.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Proofs.Erdos735OQ04
import Proofs.Erdos735OQ04Octahedron

namespace Erdos735OQ04Dodeca

open Erdos735OQ04 Erdos735OQ04Octa
open scoped Classical

/- ## The golden ratio and its three working facts -/

/-- The golden ratio `φ = (1+√5)/2`. -/
noncomputable def phi : ℝ := (1 + Real.sqrt 5) / 2

lemma sqrt5_sq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

lemma two_lt_sqrt5 : 2 < Real.sqrt 5 := by
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

lemma sqrt5_lt_three : Real.sqrt 5 < 3 := by
  nlinarith [sqrt5_sq, Real.sqrt_nonneg 5]

/-- The defining quadratic identity `φ² = φ + 1`. -/
lemma phi_sq : phi ^ 2 = phi + 1 := by
  rw [phi]
  linear_combination sqrt5_sq / 4

lemma one_lt_phi : 1 < phi := by
  rw [phi]; linarith [two_lt_sqrt5]

lemma phi_lt_two : phi < 2 := by
  rw [phi]; linarith [sqrt5_lt_three]

lemma phi_pos : 0 < phi := lt_trans one_pos one_lt_phi

lemma phi_ne_zero : phi ≠ 0 := ne_of_gt phi_pos

/- ## The twenty dodecahedron vertices

The reciprocal `1/φ` is written as `φ − 1` throughout (`φ·(φ−1) = 1` is
`φ² = φ + 1` rearranged), keeping every coordinate a linear expression in
`φ`. -/

noncomputable def c₁ : EuclideanSpace ℝ (Fin 3) := !₂[ 1,  1,  1]
noncomputable def c₂ : EuclideanSpace ℝ (Fin 3) := !₂[ 1,  1, -1]
noncomputable def c₃ : EuclideanSpace ℝ (Fin 3) := !₂[ 1, -1,  1]
noncomputable def c₄ : EuclideanSpace ℝ (Fin 3) := !₂[ 1, -1, -1]
noncomputable def c₅ : EuclideanSpace ℝ (Fin 3) := !₂[-1,  1,  1]
noncomputable def c₆ : EuclideanSpace ℝ (Fin 3) := !₂[-1,  1, -1]
noncomputable def c₇ : EuclideanSpace ℝ (Fin 3) := !₂[-1, -1,  1]
noncomputable def c₈ : EuclideanSpace ℝ (Fin 3) := !₂[-1, -1, -1]

noncomputable def x₁ : EuclideanSpace ℝ (Fin 3) := !₂[phi - 1,  phi, 0]
noncomputable def x₂ : EuclideanSpace ℝ (Fin 3) := !₂[phi - 1, -phi, 0]
noncomputable def x₃ : EuclideanSpace ℝ (Fin 3) := !₂[1 - phi,  phi, 0]
noncomputable def x₄ : EuclideanSpace ℝ (Fin 3) := !₂[1 - phi, -phi, 0]

noncomputable def y₁ : EuclideanSpace ℝ (Fin 3) := !₂[0, phi - 1,  phi]
noncomputable def y₂ : EuclideanSpace ℝ (Fin 3) := !₂[0, phi - 1, -phi]
noncomputable def y₃ : EuclideanSpace ℝ (Fin 3) := !₂[0, 1 - phi,  phi]
noncomputable def y₄ : EuclideanSpace ℝ (Fin 3) := !₂[0, 1 - phi, -phi]

noncomputable def z₁ : EuclideanSpace ℝ (Fin 3) := !₂[ phi, 0, phi - 1]
noncomputable def z₂ : EuclideanSpace ℝ (Fin 3) := !₂[ phi, 0, 1 - phi]
noncomputable def z₃ : EuclideanSpace ℝ (Fin 3) := !₂[-phi, 0, phi - 1]
noncomputable def z₄ : EuclideanSpace ℝ (Fin 3) := !₂[-phi, 0, 1 - phi]

/-- The dodecahedron configuration. -/
noncomputable def dodecaConfig : PointConfigD 3 :=
  {c₁, c₂, c₃, c₄, c₅, c₆, c₇, c₈, x₁, x₂, x₃, x₄, y₁, y₂, y₃, y₄, z₁, z₂, z₃, z₄}

/- ## Pairwise distinctness of the vertices used in the eight flats -/

lemma d_c₁c₂ : c₁ ≠ c₂ := ne_of_coord 2 (by norm_num [c₁, c₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₁c₃ : c₁ ≠ c₃ := ne_of_coord 1 (by norm_num [c₁, c₃, WithLp.ofLp_toLp])
lemma d_c₁c₄ : c₁ ≠ c₄ := ne_of_coord 1 (by norm_num [c₁, c₄, WithLp.ofLp_toLp])
lemma d_c₂c₃ : c₂ ≠ c₃ := ne_of_coord 1 (by norm_num [c₂, c₃, WithLp.ofLp_toLp])
lemma d_c₂c₄ : c₂ ≠ c₄ := ne_of_coord 1 (by norm_num [c₂, c₄, WithLp.ofLp_toLp])
lemma d_c₃c₄ : c₃ ≠ c₄ := ne_of_coord 2 (by norm_num [c₃, c₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma d_c₅c₆ : c₅ ≠ c₆ := ne_of_coord 2 (by norm_num [c₅, c₆, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₅c₇ : c₅ ≠ c₇ := ne_of_coord 1 (by norm_num [c₅, c₇, WithLp.ofLp_toLp])
lemma d_c₅c₈ : c₅ ≠ c₈ := ne_of_coord 1 (by norm_num [c₅, c₈, WithLp.ofLp_toLp])
lemma d_c₆c₇ : c₆ ≠ c₇ := ne_of_coord 1 (by norm_num [c₆, c₇, WithLp.ofLp_toLp])
lemma d_c₆c₈ : c₆ ≠ c₈ := ne_of_coord 1 (by norm_num [c₆, c₈, WithLp.ofLp_toLp])
lemma d_c₇c₈ : c₇ ≠ c₈ := ne_of_coord 2 (by norm_num [c₇, c₈, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

/- Cube vertex vs `x`-vertex: they differ in the third coordinate (±1 vs 0). -/
lemma d_c₁x₁ : c₁ ≠ x₁ := ne_of_coord 2 (by norm_num [c₁, x₁, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₂x₁ : c₂ ≠ x₁ := ne_of_coord 2 (by norm_num [c₂, x₁, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₃x₂ : c₃ ≠ x₂ := ne_of_coord 2 (by norm_num [c₃, x₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₄x₂ : c₄ ≠ x₂ := ne_of_coord 2 (by norm_num [c₄, x₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₅x₃ : c₅ ≠ x₃ := ne_of_coord 2 (by norm_num [c₅, x₃, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₆x₃ : c₆ ≠ x₃ := ne_of_coord 2 (by norm_num [c₆, x₃, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₇x₄ : c₇ ≠ x₄ := ne_of_coord 2 (by norm_num [c₇, x₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma d_c₈x₄ : c₈ ≠ x₄ := ne_of_coord 2 (by norm_num [c₈, x₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

/- Cube vertex vs `z`-vertex: they differ in the second coordinate (±1 vs 0). -/
lemma d_c₁z₁ : c₁ ≠ z₁ := ne_of_coord 1 (by norm_num [c₁, z₁, WithLp.ofLp_toLp])
lemma d_c₁z₂ : c₁ ≠ z₂ := ne_of_coord 1 (by norm_num [c₁, z₂, WithLp.ofLp_toLp])
lemma d_c₂z₁ : c₂ ≠ z₁ := ne_of_coord 1 (by norm_num [c₂, z₁, WithLp.ofLp_toLp])
lemma d_c₂z₂ : c₂ ≠ z₂ := ne_of_coord 1 (by norm_num [c₂, z₂, WithLp.ofLp_toLp])
lemma d_c₃z₁ : c₃ ≠ z₁ := ne_of_coord 1 (by norm_num [c₃, z₁, WithLp.ofLp_toLp])
lemma d_c₃z₂ : c₃ ≠ z₂ := ne_of_coord 1 (by norm_num [c₃, z₂, WithLp.ofLp_toLp])
lemma d_c₄z₁ : c₄ ≠ z₁ := ne_of_coord 1 (by norm_num [c₄, z₁, WithLp.ofLp_toLp])
lemma d_c₄z₂ : c₄ ≠ z₂ := ne_of_coord 1 (by norm_num [c₄, z₂, WithLp.ofLp_toLp])
lemma d_c₅z₃ : c₅ ≠ z₃ := ne_of_coord 1 (by norm_num [c₅, z₃, WithLp.ofLp_toLp])
lemma d_c₅z₄ : c₅ ≠ z₄ := ne_of_coord 1 (by norm_num [c₅, z₄, WithLp.ofLp_toLp])
lemma d_c₆z₃ : c₆ ≠ z₃ := ne_of_coord 1 (by norm_num [c₆, z₃, WithLp.ofLp_toLp])
lemma d_c₆z₄ : c₆ ≠ z₄ := ne_of_coord 1 (by norm_num [c₆, z₄, WithLp.ofLp_toLp])
lemma d_c₇z₃ : c₇ ≠ z₃ := ne_of_coord 1 (by norm_num [c₇, z₃, WithLp.ofLp_toLp])
lemma d_c₇z₄ : c₇ ≠ z₄ := ne_of_coord 1 (by norm_num [c₇, z₄, WithLp.ofLp_toLp])
lemma d_c₈z₃ : c₈ ≠ z₃ := ne_of_coord 1 (by norm_num [c₈, z₃, WithLp.ofLp_toLp])
lemma d_c₈z₄ : c₈ ≠ z₄ := ne_of_coord 1 (by norm_num [c₈, z₄, WithLp.ofLp_toLp])

/- `x`-vertex vs `z`-vertex: they differ in the second coordinate (±φ vs 0). -/
lemma d_x₁z₁ : x₁ ≠ z₁ := ne_of_coord 1 (by
  simp only [x₁, z₁, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact phi_ne_zero)
lemma d_x₁z₂ : x₁ ≠ z₂ := ne_of_coord 1 (by
  simp only [x₁, z₂, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact phi_ne_zero)
lemma d_x₂z₁ : x₂ ≠ z₁ := ne_of_coord 1 (by
  simp only [x₂, z₁, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; exact phi_ne_zero (by linarith)
  )
lemma d_x₂z₂ : x₂ ≠ z₂ := ne_of_coord 1 (by
  simp only [x₂, z₂, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; exact phi_ne_zero (by linarith))
lemma d_x₃z₃ : x₃ ≠ z₃ := ne_of_coord 1 (by
  simp only [x₃, z₃, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact phi_ne_zero)
lemma d_x₃z₄ : x₃ ≠ z₄ := ne_of_coord 1 (by
  simp only [x₃, z₄, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  exact phi_ne_zero)
lemma d_x₄z₃ : x₄ ≠ z₃ := ne_of_coord 1 (by
  simp only [x₄, z₃, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; exact phi_ne_zero (by linarith))
lemma d_x₄z₄ : x₄ ≠ z₄ := ne_of_coord 1 (by
  simp only [x₄, z₄, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; exact phi_ne_zero (by linarith))

/- Within the `x` family (second coordinate ±φ, first coordinate ±(φ−1)). -/
lemma d_x₁x₂ : x₁ ≠ x₂ := ne_of_coord 1 (by
  simp only [x₁, x₂, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])
lemma d_x₁x₃ : x₁ ≠ x₃ := ne_of_coord 0 (by
  simp only [x₁, x₃, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [one_lt_phi])
lemma d_x₁x₄ : x₁ ≠ x₄ := ne_of_coord 1 (by
  simp only [x₁, x₄, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])
lemma d_x₂x₃ : x₂ ≠ x₃ := ne_of_coord 1 (by
  simp only [x₂, x₃, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])
lemma d_x₂x₄ : x₂ ≠ x₄ := ne_of_coord 0 (by
  simp only [x₂, x₄, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [one_lt_phi])
lemma d_x₃x₄ : x₃ ≠ x₄ := ne_of_coord 1 (by
  simp only [x₃, x₄, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])

/- Within the `z` family (first coordinate ±φ, third coordinate ±(φ−1)). -/
lemma d_z₁z₂ : z₁ ≠ z₂ := ne_of_coord 2 (by
  simp only [z₁, z₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  intro h; linarith [one_lt_phi])
lemma d_z₁z₃ : z₁ ≠ z₃ := ne_of_coord 0 (by
  simp only [z₁, z₃, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])
lemma d_z₁z₄ : z₁ ≠ z₄ := ne_of_coord 0 (by
  simp only [z₁, z₄, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])
lemma d_z₂z₃ : z₂ ≠ z₃ := ne_of_coord 0 (by
  simp only [z₂, z₃, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])
lemma d_z₂z₄ : z₂ ≠ z₄ := ne_of_coord 0 (by
  simp only [z₂, z₄, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [phi_pos])
lemma d_z₃z₄ : z₃ ≠ z₄ := ne_of_coord 2 (by
  simp only [z₃, z₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons]
  intro h; linarith [one_lt_phi])

/- ## The two face functionals -/

/-- The face functional `x ↦ φ·x₀ + x₁` (normal `(φ, 1, 0)`). -/
noncomputable def faceP : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  phi • coordL 0 + coordL 1

lemma faceP_apply (x : EuclideanSpace ℝ (Fin 3)) :
    faceP x = phi * WithLp.ofLp x 0 + WithLp.ofLp x 1 := rfl

/-- The mirror face functional `x ↦ φ·x₀ − x₁` (normal `(φ, −1, 0)`). -/
noncomputable def faceM : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  phi • coordL 0 - coordL 1

lemma faceM_apply (x : EuclideanSpace ℝ (Fin 3)) :
    faceM x = phi * WithLp.ofLp x 0 - WithLp.ofLp x 1 := rfl

lemma faceP_z₁ : faceP z₁ = phi + 1 := by
  rw [faceP_apply]
  simp only [z₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  linear_combination phi_sq

lemma faceM_z₁ : faceM z₁ = phi + 1 := by
  rw [faceM_apply]
  simp only [z₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  linear_combination phi_sq

lemma faceM_z₃ : faceM z₃ = -(phi + 1) := by
  rw [faceM_apply]
  simp only [z₃, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  linear_combination -phi_sq

lemma faceP_z₃ : faceP z₃ = -(phi + 1) := by
  rw [faceP_apply]
  simp only [z₃, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
  linear_combination -phi_sq

/- ## The eight flats -/

/-- Face plane `φx + y = φ+1` (through c₁, c₂, x₁, z₁, z₂). -/
noncomputable def flatG1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' z₁ (LinearMap.ker faceP)

/-- Face plane `φx − y = φ+1` (through c₃, c₄, x₂, z₁, z₂). -/
noncomputable def flatG2 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' z₁ (LinearMap.ker faceM)

/-- Face plane `φx − y = −(φ+1)` (through c₅, c₆, x₃, z₃, z₄). -/
noncomputable def flatG3 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' z₃ (LinearMap.ker faceM)

/-- Face plane `φx + y = −(φ+1)` (through c₇, c₈, x₄, z₃, z₄). -/
noncomputable def flatG4 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' z₃ (LinearMap.ker faceP)

/-- Cube-face plane `x = 1` (through c₁, c₂, c₃, c₄). -/
noncomputable def flatX1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' c₁ (LinearMap.ker (coordL 0))

/-- Cube-face plane `x = −1` (through c₅, c₆, c₇, c₈). -/
noncomputable def flatX2 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' c₅ (LinearMap.ker (coordL 0))

/-- Coordinate plane `z = 0` (through x₁, x₂, x₃, x₄). -/
noncomputable def flatZ0 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' 0 (LinearMap.ker (coordL 2))

/-- Coordinate plane `y = 0` (through z₁, z₂, z₃, z₄). -/
noncomputable def flatY0 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' 0 (LinearMap.ker (coordL 1))

lemma mem_flatG1_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatG1 ↔ phi * WithLp.ofLp x 0 + WithLp.ofLp x 1 = phi + 1 := by
  rw [flatG1, mem_mk'_ker_iff, faceP_z₁, faceP_apply]

lemma mem_flatG2_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatG2 ↔ phi * WithLp.ofLp x 0 - WithLp.ofLp x 1 = phi + 1 := by
  rw [flatG2, mem_mk'_ker_iff, faceM_z₁, faceM_apply]

lemma mem_flatG3_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatG3 ↔ phi * WithLp.ofLp x 0 - WithLp.ofLp x 1 = -(phi + 1) := by
  rw [flatG3, mem_mk'_ker_iff, faceM_z₃, faceM_apply]

lemma mem_flatG4_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatG4 ↔ phi * WithLp.ofLp x 0 + WithLp.ofLp x 1 = -(phi + 1) := by
  rw [flatG4, mem_mk'_ker_iff, faceP_z₃, faceP_apply]

lemma mem_flatX1_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatX1 ↔ WithLp.ofLp x 0 = 1 := by
  rw [flatX1, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  norm_num [c₁, WithLp.ofLp_toLp]

lemma mem_flatX2_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatX2 ↔ WithLp.ofLp x 0 = -1 := by
  rw [flatX2, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  norm_num [c₅, WithLp.ofLp_toLp]

lemma mem_flatZ0_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatZ0 ↔ WithLp.ofLp x 2 = 0 := by
  rw [flatZ0, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp

lemma mem_flatY0_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatY0 ↔ WithLp.ofLp x 1 = 0 := by
  rw [flatY0, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp

/- ## Direction ranks -/

lemma rank_flatG1 : Module.rank ℝ flatG1.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatG1, AffineSubspace.direction_mk']
  exact rank_ker_two _ z₁ (by rw [faceP_z₁]; intro h; linarith [one_lt_phi])

lemma rank_flatG2 : Module.rank ℝ flatG2.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatG2, AffineSubspace.direction_mk']
  exact rank_ker_two _ z₁ (by rw [faceM_z₁]; intro h; linarith [one_lt_phi])

lemma rank_flatG3 : Module.rank ℝ flatG3.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatG3, AffineSubspace.direction_mk']
  exact rank_ker_two _ z₁ (by rw [faceM_z₁]; intro h; linarith [one_lt_phi])

lemma rank_flatG4 : Module.rank ℝ flatG4.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatG4, AffineSubspace.direction_mk']
  exact rank_ker_two _ z₁ (by rw [faceP_z₁]; intro h; linarith [one_lt_phi])

lemma rank_flatX1 : Module.rank ℝ flatX1.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatX1, AffineSubspace.direction_mk']
  exact rank_ker_two _ c₁ (by rw [coordL_apply]; norm_num [c₁, WithLp.ofLp_toLp])

lemma rank_flatX2 : Module.rank ℝ flatX2.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatX2, AffineSubspace.direction_mk']
  exact rank_ker_two _ c₁ (by rw [coordL_apply]; norm_num [c₁, WithLp.ofLp_toLp])

lemma rank_flatZ0 : Module.rank ℝ flatZ0.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatZ0, AffineSubspace.direction_mk']
  exact rank_ker_two _ c₁ (by rw [coordL_apply]; norm_num [c₁, WithLp.ofLp_toLp,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_flatY0 : Module.rank ℝ flatY0.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatY0, AffineSubspace.direction_mk']
  exact rank_ker_two _ c₁ (by rw [coordL_apply]; norm_num [c₁, WithLp.ofLp_toLp])

/- ## Vertex membership decisions

Below, each of the eight flats gets a full 20-vertex membership table.  Every
`∈`/`∉` reduces to linear arithmetic in `φ` over the three facts `φ² = φ+1`,
`1 < φ < 2` (the `x`/`z` face-plane identities via `linear_combination phi_sq`,
everything else via `linarith`/`nlinarith`). -/

section MembershipTables

-- Convenience: unfold a vertex's coordinates.
local macro "coords" x:term : tactic =>
  `(tactic| simp only [$x:term, WithLp.ofLp_toLp, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons])

/- flatG1 (φx + y = φ+1): in c₁, c₂, x₁, z₁, z₂; out the other fifteen. -/

lemma hG1c₁ : c₁ ∈ flatG1 := (mem_flatG1_iff c₁).mpr (by coords c₁; ring)
lemma hG1c₂ : c₂ ∈ flatG1 := (mem_flatG1_iff c₂).mpr (by coords c₂; ring)
lemma hG1c₃ : c₃ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords c₃; intro h; linarith [one_lt_phi]
lemma hG1c₄ : c₄ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords c₄; intro h; linarith [one_lt_phi]
lemma hG1c₅ : c₅ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords c₅; intro h; linarith [one_lt_phi]
lemma hG1c₆ : c₆ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords c₆; intro h; linarith [one_lt_phi]
lemma hG1c₇ : c₇ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords c₇; intro h; linarith [one_lt_phi]
lemma hG1c₈ : c₈ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords c₈; intro h; linarith [one_lt_phi]
lemma hG1x₁ : x₁ ∈ flatG1 := (mem_flatG1_iff x₁).mpr (by
  coords x₁; linear_combination phi_sq)
lemma hG1x₂ : x₂ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords x₂; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG1x₃ : x₃ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords x₃; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG1x₄ : x₄ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords x₄; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG1y₁ : y₁ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords y₁; intro h; linarith [one_lt_phi]
lemma hG1y₂ : y₂ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords y₂; intro h; linarith [one_lt_phi]
lemma hG1y₃ : y₃ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords y₃; intro h; linarith [one_lt_phi]
lemma hG1y₄ : y₄ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords y₄; intro h; linarith [one_lt_phi]
lemma hG1z₁ : z₁ ∈ flatG1 := (mem_flatG1_iff z₁).mpr (by
  coords z₁; linear_combination phi_sq)
lemma hG1z₂ : z₂ ∈ flatG1 := (mem_flatG1_iff z₂).mpr (by
  coords z₂; linear_combination phi_sq)
lemma hG1z₃ : z₃ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords z₃; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG1z₄ : z₄ ∉ flatG1 := by
  rw [mem_flatG1_iff]; coords z₄; intro h; nlinarith [phi_sq, one_lt_phi]

/- flatG2 (φx − y = φ+1): in c₃, c₄, x₂, z₁, z₂; out the rest. -/

lemma hG2c₁ : c₁ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords c₁; intro h; linarith [one_lt_phi]
lemma hG2c₂ : c₂ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords c₂; intro h; linarith [one_lt_phi]
lemma hG2c₃ : c₃ ∈ flatG2 := (mem_flatG2_iff c₃).mpr (by coords c₃; ring)
lemma hG2c₄ : c₄ ∈ flatG2 := (mem_flatG2_iff c₄).mpr (by coords c₄; ring)
lemma hG2c₅ : c₅ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords c₅; intro h; linarith [one_lt_phi]
lemma hG2c₆ : c₆ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords c₆; intro h; linarith [one_lt_phi]
lemma hG2c₇ : c₇ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords c₇; intro h; linarith [one_lt_phi]
lemma hG2c₈ : c₈ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords c₈; intro h; linarith [one_lt_phi]
lemma hG2x₁ : x₁ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords x₁; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG2x₂ : x₂ ∈ flatG2 := (mem_flatG2_iff x₂).mpr (by
  coords x₂; linear_combination phi_sq)
lemma hG2x₃ : x₃ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords x₃; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG2x₄ : x₄ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords x₄; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG2y₁ : y₁ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords y₁; intro h; linarith [one_lt_phi]
lemma hG2y₂ : y₂ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords y₂; intro h; linarith [one_lt_phi]
lemma hG2y₃ : y₃ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords y₃; intro h; linarith [one_lt_phi]
lemma hG2y₄ : y₄ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords y₄; intro h; linarith [one_lt_phi]
lemma hG2z₁ : z₁ ∈ flatG2 := (mem_flatG2_iff z₁).mpr (by
  coords z₁; linear_combination phi_sq)
lemma hG2z₂ : z₂ ∈ flatG2 := (mem_flatG2_iff z₂).mpr (by
  coords z₂; linear_combination phi_sq)
lemma hG2z₃ : z₃ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords z₃; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG2z₄ : z₄ ∉ flatG2 := by
  rw [mem_flatG2_iff]; coords z₄; intro h; nlinarith [phi_sq, one_lt_phi]

/- flatG3 (φx − y = −(φ+1)): in c₅, c₆, x₃, z₃, z₄; out the rest. -/

lemma hG3c₁ : c₁ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords c₁; intro h; linarith [one_lt_phi]
lemma hG3c₂ : c₂ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords c₂; intro h; linarith [one_lt_phi]
lemma hG3c₃ : c₃ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords c₃; intro h; linarith [one_lt_phi]
lemma hG3c₄ : c₄ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords c₄; intro h; linarith [one_lt_phi]
lemma hG3c₅ : c₅ ∈ flatG3 := (mem_flatG3_iff c₅).mpr (by coords c₅; ring)
lemma hG3c₆ : c₆ ∈ flatG3 := (mem_flatG3_iff c₆).mpr (by coords c₆; ring)
lemma hG3c₇ : c₇ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords c₇; intro h; linarith [one_lt_phi]
lemma hG3c₈ : c₈ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords c₈; intro h; linarith [one_lt_phi]
lemma hG3x₁ : x₁ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords x₁; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG3x₂ : x₂ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords x₂; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG3x₃ : x₃ ∈ flatG3 := (mem_flatG3_iff x₃).mpr (by
  coords x₃; linear_combination -phi_sq)
lemma hG3x₄ : x₄ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords x₄; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG3y₁ : y₁ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords y₁; intro h; linarith [one_lt_phi]
lemma hG3y₂ : y₂ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords y₂; intro h; linarith [one_lt_phi]
lemma hG3y₃ : y₃ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords y₃; intro h; linarith [one_lt_phi]
lemma hG3y₄ : y₄ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords y₄; intro h; linarith [one_lt_phi]
lemma hG3z₁ : z₁ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords z₁; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG3z₂ : z₂ ∉ flatG3 := by
  rw [mem_flatG3_iff]; coords z₂; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG3z₃ : z₃ ∈ flatG3 := (mem_flatG3_iff z₃).mpr (by
  coords z₃; linear_combination -phi_sq)
lemma hG3z₄ : z₄ ∈ flatG3 := (mem_flatG3_iff z₄).mpr (by
  coords z₄; linear_combination -phi_sq)

/- flatG4 (φx + y = −(φ+1)): in c₇, c₈, x₄, z₃, z₄; out the rest. -/

lemma hG4c₁ : c₁ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords c₁; intro h; linarith [one_lt_phi]
lemma hG4c₂ : c₂ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords c₂; intro h; linarith [one_lt_phi]
lemma hG4c₃ : c₃ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords c₃; intro h; linarith [one_lt_phi]
lemma hG4c₄ : c₄ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords c₄; intro h; linarith [one_lt_phi]
lemma hG4c₅ : c₅ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords c₅; intro h; linarith [one_lt_phi]
lemma hG4c₆ : c₆ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords c₆; intro h; linarith [one_lt_phi]
lemma hG4c₇ : c₇ ∈ flatG4 := (mem_flatG4_iff c₇).mpr (by coords c₇; ring)
lemma hG4c₈ : c₈ ∈ flatG4 := (mem_flatG4_iff c₈).mpr (by coords c₈; ring)
lemma hG4x₁ : x₁ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords x₁; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG4x₂ : x₂ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords x₂; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG4x₃ : x₃ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords x₃; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG4x₄ : x₄ ∈ flatG4 := (mem_flatG4_iff x₄).mpr (by
  coords x₄; linear_combination -phi_sq)
lemma hG4y₁ : y₁ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords y₁; intro h; linarith [one_lt_phi]
lemma hG4y₂ : y₂ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords y₂; intro h; linarith [one_lt_phi]
lemma hG4y₃ : y₃ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords y₃; intro h; linarith [one_lt_phi]
lemma hG4y₄ : y₄ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords y₄; intro h; linarith [one_lt_phi]
lemma hG4z₁ : z₁ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords z₁; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG4z₂ : z₂ ∉ flatG4 := by
  rw [mem_flatG4_iff]; coords z₂; intro h; nlinarith [phi_sq, one_lt_phi]
lemma hG4z₃ : z₃ ∈ flatG4 := (mem_flatG4_iff z₃).mpr (by
  coords z₃; linear_combination -phi_sq)
lemma hG4z₄ : z₄ ∈ flatG4 := (mem_flatG4_iff z₄).mpr (by
  coords z₄; linear_combination -phi_sq)

/- flatX1 (x = 1): in c₁…c₄; out the rest. -/

lemma hX1c₁ : c₁ ∈ flatX1 := (mem_flatX1_iff c₁).mpr (by coords c₁)
lemma hX1c₂ : c₂ ∈ flatX1 := (mem_flatX1_iff c₂).mpr (by coords c₂)
lemma hX1c₃ : c₃ ∈ flatX1 := (mem_flatX1_iff c₃).mpr (by coords c₃)
lemma hX1c₄ : c₄ ∈ flatX1 := (mem_flatX1_iff c₄).mpr (by coords c₄)
lemma hX1c₅ : c₅ ∉ flatX1 := by rw [mem_flatX1_iff]; coords c₅; norm_num
lemma hX1c₆ : c₆ ∉ flatX1 := by rw [mem_flatX1_iff]; coords c₆; norm_num
lemma hX1c₇ : c₇ ∉ flatX1 := by rw [mem_flatX1_iff]; coords c₇; norm_num
lemma hX1c₈ : c₈ ∉ flatX1 := by rw [mem_flatX1_iff]; coords c₈; norm_num
lemma hX1x₁ : x₁ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords x₁; intro h; linarith [phi_lt_two]
lemma hX1x₂ : x₂ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords x₂; intro h; linarith [phi_lt_two]
lemma hX1x₃ : x₃ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords x₃; intro h; linarith [one_lt_phi]
lemma hX1x₄ : x₄ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords x₄; intro h; linarith [one_lt_phi]
lemma hX1y₁ : y₁ ∉ flatX1 := by rw [mem_flatX1_iff]; coords y₁; norm_num
lemma hX1y₂ : y₂ ∉ flatX1 := by rw [mem_flatX1_iff]; coords y₂; norm_num
lemma hX1y₃ : y₃ ∉ flatX1 := by rw [mem_flatX1_iff]; coords y₃; norm_num
lemma hX1y₄ : y₄ ∉ flatX1 := by rw [mem_flatX1_iff]; coords y₄; norm_num
lemma hX1z₁ : z₁ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords z₁; intro h; linarith [one_lt_phi]
lemma hX1z₂ : z₂ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords z₂; intro h; linarith [one_lt_phi]
lemma hX1z₃ : z₃ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords z₃; intro h; linarith [one_lt_phi]
lemma hX1z₄ : z₄ ∉ flatX1 := by
  rw [mem_flatX1_iff]; coords z₄; intro h; linarith [one_lt_phi]

/- flatX2 (x = −1): in c₅…c₈; out the rest. -/

lemma hX2c₁ : c₁ ∉ flatX2 := by rw [mem_flatX2_iff]; coords c₁; norm_num
lemma hX2c₂ : c₂ ∉ flatX2 := by rw [mem_flatX2_iff]; coords c₂; norm_num
lemma hX2c₃ : c₃ ∉ flatX2 := by rw [mem_flatX2_iff]; coords c₃; norm_num
lemma hX2c₄ : c₄ ∉ flatX2 := by rw [mem_flatX2_iff]; coords c₄; norm_num
lemma hX2c₅ : c₅ ∈ flatX2 := (mem_flatX2_iff c₅).mpr (by coords c₅)
lemma hX2c₆ : c₆ ∈ flatX2 := (mem_flatX2_iff c₆).mpr (by coords c₆)
lemma hX2c₇ : c₇ ∈ flatX2 := (mem_flatX2_iff c₇).mpr (by coords c₇)
lemma hX2c₈ : c₈ ∈ flatX2 := (mem_flatX2_iff c₈).mpr (by coords c₈)
lemma hX2x₁ : x₁ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords x₁; intro h; linarith [one_lt_phi]
lemma hX2x₂ : x₂ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords x₂; intro h; linarith [one_lt_phi]
lemma hX2x₃ : x₃ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords x₃; intro h; linarith [phi_lt_two]
lemma hX2x₄ : x₄ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords x₄; intro h; linarith [phi_lt_two]
lemma hX2y₁ : y₁ ∉ flatX2 := by rw [mem_flatX2_iff]; coords y₁; norm_num
lemma hX2y₂ : y₂ ∉ flatX2 := by rw [mem_flatX2_iff]; coords y₂; norm_num
lemma hX2y₃ : y₃ ∉ flatX2 := by rw [mem_flatX2_iff]; coords y₃; norm_num
lemma hX2y₄ : y₄ ∉ flatX2 := by rw [mem_flatX2_iff]; coords y₄; norm_num
lemma hX2z₁ : z₁ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords z₁; intro h; linarith [one_lt_phi]
lemma hX2z₂ : z₂ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords z₂; intro h; linarith [one_lt_phi]
lemma hX2z₃ : z₃ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords z₃; intro h; linarith [one_lt_phi]
lemma hX2z₄ : z₄ ∉ flatX2 := by
  rw [mem_flatX2_iff]; coords z₄; intro h; linarith [one_lt_phi]

/- flatZ0 (z = 0): in x₁…x₄; out the rest. -/

lemma hZ0c₁ : c₁ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₁; norm_num
lemma hZ0c₂ : c₂ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₂; norm_num
lemma hZ0c₃ : c₃ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₃; norm_num
lemma hZ0c₄ : c₄ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₄; norm_num
lemma hZ0c₅ : c₅ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₅; norm_num
lemma hZ0c₆ : c₆ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₆; norm_num
lemma hZ0c₇ : c₇ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₇; norm_num
lemma hZ0c₈ : c₈ ∉ flatZ0 := by rw [mem_flatZ0_iff]; coords c₈; norm_num
lemma hZ0x₁ : x₁ ∈ flatZ0 := (mem_flatZ0_iff x₁).mpr (by coords x₁)
lemma hZ0x₂ : x₂ ∈ flatZ0 := (mem_flatZ0_iff x₂).mpr (by coords x₂)
lemma hZ0x₃ : x₃ ∈ flatZ0 := (mem_flatZ0_iff x₃).mpr (by coords x₃)
lemma hZ0x₄ : x₄ ∈ flatZ0 := (mem_flatZ0_iff x₄).mpr (by coords x₄)
lemma hZ0y₁ : y₁ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords y₁; exact phi_ne_zero
lemma hZ0y₂ : y₂ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords y₂; intro h; exact phi_ne_zero (by linarith)
lemma hZ0y₃ : y₃ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords y₃; exact phi_ne_zero
lemma hZ0y₄ : y₄ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords y₄; intro h; exact phi_ne_zero (by linarith)
lemma hZ0z₁ : z₁ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords z₁; intro h; linarith [one_lt_phi]
lemma hZ0z₂ : z₂ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords z₂; intro h; linarith [one_lt_phi]
lemma hZ0z₃ : z₃ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords z₃; intro h; linarith [one_lt_phi]
lemma hZ0z₄ : z₄ ∉ flatZ0 := by
  rw [mem_flatZ0_iff]; coords z₄; intro h; linarith [one_lt_phi]

/- flatY0 (y = 0): in z₁…z₄; out the rest. -/

lemma hY0c₁ : c₁ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₁; norm_num
lemma hY0c₂ : c₂ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₂; norm_num
lemma hY0c₃ : c₃ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₃; norm_num
lemma hY0c₄ : c₄ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₄; norm_num
lemma hY0c₅ : c₅ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₅; norm_num
lemma hY0c₆ : c₆ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₆; norm_num
lemma hY0c₇ : c₇ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₇; norm_num
lemma hY0c₈ : c₈ ∉ flatY0 := by rw [mem_flatY0_iff]; coords c₈; norm_num
lemma hY0x₁ : x₁ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords x₁; exact phi_ne_zero
lemma hY0x₂ : x₂ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords x₂; intro h; exact phi_ne_zero (by linarith)
lemma hY0x₃ : x₃ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords x₃; exact phi_ne_zero
lemma hY0x₄ : x₄ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords x₄; intro h; exact phi_ne_zero (by linarith)
lemma hY0y₁ : y₁ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords y₁; intro h; linarith [one_lt_phi]
lemma hY0y₂ : y₂ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords y₂; intro h; linarith [one_lt_phi]
lemma hY0y₃ : y₃ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords y₃; intro h; linarith [one_lt_phi]
lemma hY0y₄ : y₄ ∉ flatY0 := by
  rw [mem_flatY0_iff]; coords y₄; intro h; linarith [one_lt_phi]
lemma hY0z₁ : z₁ ∈ flatY0 := (mem_flatY0_iff z₁).mpr (by coords z₁)
lemma hY0z₂ : z₂ ∈ flatY0 := (mem_flatY0_iff z₂).mpr (by coords z₂)
lemma hY0z₃ : z₃ ∈ flatY0 := (mem_flatY0_iff z₃).mpr (by coords z₃)
lemma hY0z₄ : z₄ ∈ flatY0 := (mem_flatY0_iff z₄).mpr (by coords z₄)

end MembershipTables

/- ## Filtered point sets of the eight flats -/

lemma filter_flatG1 :
    dodecaConfig.filter (· ∈ flatG1) = {c₁, c₂, x₁, z₁, z₂} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_pos hG1c₁, Finset.filter_insert, if_pos hG1c₂,
    Finset.filter_insert, if_neg hG1c₃, Finset.filter_insert, if_neg hG1c₄,
    Finset.filter_insert, if_neg hG1c₅, Finset.filter_insert, if_neg hG1c₆,
    Finset.filter_insert, if_neg hG1c₇, Finset.filter_insert, if_neg hG1c₈,
    Finset.filter_insert, if_pos hG1x₁, Finset.filter_insert, if_neg hG1x₂,
    Finset.filter_insert, if_neg hG1x₃, Finset.filter_insert, if_neg hG1x₄,
    Finset.filter_insert, if_neg hG1y₁, Finset.filter_insert, if_neg hG1y₂,
    Finset.filter_insert, if_neg hG1y₃, Finset.filter_insert, if_neg hG1y₄,
    Finset.filter_insert, if_pos hG1z₁, Finset.filter_insert, if_pos hG1z₂,
    Finset.filter_insert, if_neg hG1z₃, Finset.filter_singleton, if_neg hG1z₄]
  rfl

lemma filter_flatG2 :
    dodecaConfig.filter (· ∈ flatG2) = {c₃, c₄, x₂, z₁, z₂} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_neg hG2c₁, Finset.filter_insert, if_neg hG2c₂,
    Finset.filter_insert, if_pos hG2c₃, Finset.filter_insert, if_pos hG2c₄,
    Finset.filter_insert, if_neg hG2c₅, Finset.filter_insert, if_neg hG2c₆,
    Finset.filter_insert, if_neg hG2c₇, Finset.filter_insert, if_neg hG2c₈,
    Finset.filter_insert, if_neg hG2x₁, Finset.filter_insert, if_pos hG2x₂,
    Finset.filter_insert, if_neg hG2x₃, Finset.filter_insert, if_neg hG2x₄,
    Finset.filter_insert, if_neg hG2y₁, Finset.filter_insert, if_neg hG2y₂,
    Finset.filter_insert, if_neg hG2y₃, Finset.filter_insert, if_neg hG2y₄,
    Finset.filter_insert, if_pos hG2z₁, Finset.filter_insert, if_pos hG2z₂,
    Finset.filter_insert, if_neg hG2z₃, Finset.filter_singleton, if_neg hG2z₄]
  rfl

lemma filter_flatG3 :
    dodecaConfig.filter (· ∈ flatG3) = {c₅, c₆, x₃, z₃, z₄} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_neg hG3c₁, Finset.filter_insert, if_neg hG3c₂,
    Finset.filter_insert, if_neg hG3c₃, Finset.filter_insert, if_neg hG3c₄,
    Finset.filter_insert, if_pos hG3c₅, Finset.filter_insert, if_pos hG3c₆,
    Finset.filter_insert, if_neg hG3c₇, Finset.filter_insert, if_neg hG3c₈,
    Finset.filter_insert, if_neg hG3x₁, Finset.filter_insert, if_neg hG3x₂,
    Finset.filter_insert, if_pos hG3x₃, Finset.filter_insert, if_neg hG3x₄,
    Finset.filter_insert, if_neg hG3y₁, Finset.filter_insert, if_neg hG3y₂,
    Finset.filter_insert, if_neg hG3y₃, Finset.filter_insert, if_neg hG3y₄,
    Finset.filter_insert, if_neg hG3z₁, Finset.filter_insert, if_neg hG3z₂,
    Finset.filter_insert, if_pos hG3z₃, Finset.filter_singleton, if_pos hG3z₄]

lemma filter_flatG4 :
    dodecaConfig.filter (· ∈ flatG4) = {c₇, c₈, x₄, z₃, z₄} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_neg hG4c₁, Finset.filter_insert, if_neg hG4c₂,
    Finset.filter_insert, if_neg hG4c₃, Finset.filter_insert, if_neg hG4c₄,
    Finset.filter_insert, if_neg hG4c₅, Finset.filter_insert, if_neg hG4c₆,
    Finset.filter_insert, if_pos hG4c₇, Finset.filter_insert, if_pos hG4c₈,
    Finset.filter_insert, if_neg hG4x₁, Finset.filter_insert, if_neg hG4x₂,
    Finset.filter_insert, if_neg hG4x₃, Finset.filter_insert, if_pos hG4x₄,
    Finset.filter_insert, if_neg hG4y₁, Finset.filter_insert, if_neg hG4y₂,
    Finset.filter_insert, if_neg hG4y₃, Finset.filter_insert, if_neg hG4y₄,
    Finset.filter_insert, if_neg hG4z₁, Finset.filter_insert, if_neg hG4z₂,
    Finset.filter_insert, if_pos hG4z₃, Finset.filter_singleton, if_pos hG4z₄]

lemma filter_flatX1 :
    dodecaConfig.filter (· ∈ flatX1) = {c₁, c₂, c₃, c₄} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_pos hX1c₁, Finset.filter_insert, if_pos hX1c₂,
    Finset.filter_insert, if_pos hX1c₃, Finset.filter_insert, if_pos hX1c₄,
    Finset.filter_insert, if_neg hX1c₅, Finset.filter_insert, if_neg hX1c₆,
    Finset.filter_insert, if_neg hX1c₇, Finset.filter_insert, if_neg hX1c₈,
    Finset.filter_insert, if_neg hX1x₁, Finset.filter_insert, if_neg hX1x₂,
    Finset.filter_insert, if_neg hX1x₃, Finset.filter_insert, if_neg hX1x₄,
    Finset.filter_insert, if_neg hX1y₁, Finset.filter_insert, if_neg hX1y₂,
    Finset.filter_insert, if_neg hX1y₃, Finset.filter_insert, if_neg hX1y₄,
    Finset.filter_insert, if_neg hX1z₁, Finset.filter_insert, if_neg hX1z₂,
    Finset.filter_insert, if_neg hX1z₃, Finset.filter_singleton, if_neg hX1z₄]
  rfl

lemma filter_flatX2 :
    dodecaConfig.filter (· ∈ flatX2) = {c₅, c₆, c₇, c₈} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_neg hX2c₁, Finset.filter_insert, if_neg hX2c₂,
    Finset.filter_insert, if_neg hX2c₃, Finset.filter_insert, if_neg hX2c₄,
    Finset.filter_insert, if_pos hX2c₅, Finset.filter_insert, if_pos hX2c₆,
    Finset.filter_insert, if_pos hX2c₇, Finset.filter_insert, if_pos hX2c₈,
    Finset.filter_insert, if_neg hX2x₁, Finset.filter_insert, if_neg hX2x₂,
    Finset.filter_insert, if_neg hX2x₃, Finset.filter_insert, if_neg hX2x₄,
    Finset.filter_insert, if_neg hX2y₁, Finset.filter_insert, if_neg hX2y₂,
    Finset.filter_insert, if_neg hX2y₃, Finset.filter_insert, if_neg hX2y₄,
    Finset.filter_insert, if_neg hX2z₁, Finset.filter_insert, if_neg hX2z₂,
    Finset.filter_insert, if_neg hX2z₃, Finset.filter_singleton, if_neg hX2z₄]
  rfl

lemma filter_flatZ0 :
    dodecaConfig.filter (· ∈ flatZ0) = {x₁, x₂, x₃, x₄} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_neg hZ0c₁, Finset.filter_insert, if_neg hZ0c₂,
    Finset.filter_insert, if_neg hZ0c₃, Finset.filter_insert, if_neg hZ0c₄,
    Finset.filter_insert, if_neg hZ0c₅, Finset.filter_insert, if_neg hZ0c₆,
    Finset.filter_insert, if_neg hZ0c₇, Finset.filter_insert, if_neg hZ0c₈,
    Finset.filter_insert, if_pos hZ0x₁, Finset.filter_insert, if_pos hZ0x₂,
    Finset.filter_insert, if_pos hZ0x₃, Finset.filter_insert, if_pos hZ0x₄,
    Finset.filter_insert, if_neg hZ0y₁, Finset.filter_insert, if_neg hZ0y₂,
    Finset.filter_insert, if_neg hZ0y₃, Finset.filter_insert, if_neg hZ0y₄,
    Finset.filter_insert, if_neg hZ0z₁, Finset.filter_insert, if_neg hZ0z₂,
    Finset.filter_insert, if_neg hZ0z₃, Finset.filter_singleton, if_neg hZ0z₄]
  rfl

lemma filter_flatY0 :
    dodecaConfig.filter (· ∈ flatY0) = {z₁, z₂, z₃, z₄} := by
  rw [dodecaConfig]
  rw [Finset.filter_insert, if_neg hY0c₁, Finset.filter_insert, if_neg hY0c₂,
    Finset.filter_insert, if_neg hY0c₃, Finset.filter_insert, if_neg hY0c₄,
    Finset.filter_insert, if_neg hY0c₅, Finset.filter_insert, if_neg hY0c₆,
    Finset.filter_insert, if_neg hY0c₇, Finset.filter_insert, if_neg hY0c₈,
    Finset.filter_insert, if_neg hY0x₁, Finset.filter_insert, if_neg hY0x₂,
    Finset.filter_insert, if_neg hY0x₃, Finset.filter_insert, if_neg hY0x₄,
    Finset.filter_insert, if_neg hY0y₁, Finset.filter_insert, if_neg hY0y₂,
    Finset.filter_insert, if_neg hY0y₃, Finset.filter_insert, if_neg hY0y₄,
    Finset.filter_insert, if_pos hY0z₁, Finset.filter_insert, if_pos hY0z₂,
    Finset.filter_insert, if_pos hY0z₃, Finset.filter_singleton, if_pos hY0z₄]

/- ## Non-membership facts for insert-chain card/sum computations -/

lemma nG1a : c₁ ∉ ({c₂, x₁, z₁, z₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₁c₂, d_c₁x₁, d_c₁z₁, d_c₁z₂]
lemma nG1b : c₂ ∉ ({x₁, z₁, z₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₂x₁, d_c₂z₁, d_c₂z₂]
lemma nG1c : x₁ ∉ ({z₁, z₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_x₁z₁, d_x₁z₂]
lemma nzz : z₁ ∉ ({z₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_z₁z₂]

lemma nG2a : c₃ ∉ ({c₄, x₂, z₁, z₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₃c₄, d_c₃x₂, d_c₃z₁, d_c₃z₂]
lemma nG2b : c₄ ∉ ({x₂, z₁, z₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₄x₂, d_c₄z₁, d_c₄z₂]
lemma nG2c : x₂ ∉ ({z₁, z₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_x₂z₁, d_x₂z₂]

lemma nG3a : c₅ ∉ ({c₆, x₃, z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₅c₆, d_c₅x₃, d_c₅z₃, d_c₅z₄]
lemma nG3b : c₆ ∉ ({x₃, z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₆x₃, d_c₆z₃, d_c₆z₄]
lemma nG3c : x₃ ∉ ({z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_x₃z₃, d_x₃z₄]
lemma nzz' : z₃ ∉ ({z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_z₃z₄]

lemma nG4a : c₇ ∉ ({c₈, x₄, z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₇c₈, d_c₇x₄, d_c₇z₃, d_c₇z₄]
lemma nG4b : c₈ ∉ ({x₄, z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₈x₄, d_c₈z₃, d_c₈z₄]
lemma nG4c : x₄ ∉ ({z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_x₄z₃, d_x₄z₄]

lemma nX1a : c₁ ∉ ({c₂, c₃, c₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₁c₂, d_c₁c₃, d_c₁c₄]
lemma nX1b : c₂ ∉ ({c₃, c₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₂c₃, d_c₂c₄]
lemma nX1c : c₃ ∉ ({c₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₃c₄]

lemma nX2a : c₅ ∉ ({c₆, c₇, c₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₅c₆, d_c₅c₇, d_c₅c₈]
lemma nX2b : c₆ ∉ ({c₇, c₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₆c₇, d_c₆c₈]
lemma nX2c : c₇ ∉ ({c₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_c₇c₈]

lemma nZ0a : x₁ ∉ ({x₂, x₃, x₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_x₁x₂, d_x₁x₃, d_x₁x₄]
lemma nZ0b : x₂ ∉ ({x₃, x₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_x₂x₃, d_x₂x₄]
lemma nZ0c : x₃ ∉ ({x₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_x₃x₄]

lemma nY0a : z₁ ∉ ({z₂, z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_z₁z₂, d_z₁z₃, d_z₁z₄]
lemma nY0b : z₂ ∉ ({z₃, z₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [d_z₂z₃, d_z₂z₄]

/- ## The eight flats as `ConfigKFlat 2 dodecaConfig` elements -/

lemma card_flatG1 : (dodecaConfig.filter (· ∈ flatG1)).card ≥ 2 + 1 := by
  rw [filter_flatG1, Finset.card_insert_of_notMem nG1a,
    Finset.card_insert_of_notMem nG1b, Finset.card_insert_of_notMem nG1c,
    Finset.card_insert_of_notMem nzz, Finset.card_singleton]
  omega

lemma card_flatG2 : (dodecaConfig.filter (· ∈ flatG2)).card ≥ 2 + 1 := by
  rw [filter_flatG2, Finset.card_insert_of_notMem nG2a,
    Finset.card_insert_of_notMem nG2b, Finset.card_insert_of_notMem nG2c,
    Finset.card_insert_of_notMem nzz, Finset.card_singleton]
  omega

lemma card_flatG3 : (dodecaConfig.filter (· ∈ flatG3)).card ≥ 2 + 1 := by
  rw [filter_flatG3, Finset.card_insert_of_notMem nG3a,
    Finset.card_insert_of_notMem nG3b, Finset.card_insert_of_notMem nG3c,
    Finset.card_insert_of_notMem nzz', Finset.card_singleton]
  omega

lemma card_flatG4 : (dodecaConfig.filter (· ∈ flatG4)).card ≥ 2 + 1 := by
  rw [filter_flatG4, Finset.card_insert_of_notMem nG4a,
    Finset.card_insert_of_notMem nG4b, Finset.card_insert_of_notMem nG4c,
    Finset.card_insert_of_notMem nzz', Finset.card_singleton]
  omega

lemma card_flatX1 : (dodecaConfig.filter (· ∈ flatX1)).card ≥ 2 + 1 := by
  rw [filter_flatX1, Finset.card_insert_of_notMem nX1a,
    Finset.card_insert_of_notMem nX1b, Finset.card_insert_of_notMem nX1c,
    Finset.card_singleton]
  omega

lemma card_flatX2 : (dodecaConfig.filter (· ∈ flatX2)).card ≥ 2 + 1 := by
  rw [filter_flatX2, Finset.card_insert_of_notMem nX2a,
    Finset.card_insert_of_notMem nX2b, Finset.card_insert_of_notMem nX2c,
    Finset.card_singleton]
  omega

lemma card_flatZ0 : (dodecaConfig.filter (· ∈ flatZ0)).card ≥ 2 + 1 := by
  rw [filter_flatZ0, Finset.card_insert_of_notMem nZ0a,
    Finset.card_insert_of_notMem nZ0b, Finset.card_insert_of_notMem nZ0c,
    Finset.card_singleton]
  omega

lemma card_flatY0 : (dodecaConfig.filter (· ∈ flatY0)).card ≥ 2 + 1 := by
  rw [filter_flatY0, Finset.card_insert_of_notMem nY0a,
    Finset.card_insert_of_notMem nY0b, Finset.card_insert_of_notMem nzz',
    Finset.card_singleton]
  omega

/- ## Main theorem -/

/-- **The regular dodecahedron is NOT 2-flat magic.**  The eight flat-sum
    equations combine as `(G1+G2+G3+G4) − (X1+X2) − Z0 − 2·Y0 = −c` with every
    weight cancelling, so the magic constant itself would have to vanish —
    contradicting `c > 0`.  (S6d ACT part ii; this completes the Platonic-solid
    audit: only the tetrahedron — a simplex — is 2-flat magic, as predicted by
    the S6e general-position theorem.) -/
theorem dodeca_not_isKFlatMagic : ¬ IsKFlatMagic 2 dodecaConfig := by
  rintro ⟨w, c, hc, hmagic⟩
  -- canonical membership proofs (fixed once, so weight atoms are shared)
  have m1 : c₁ ∈ dodecaConfig := by simp [dodecaConfig]
  have m2 : c₂ ∈ dodecaConfig := by simp [dodecaConfig]
  have m3 : c₃ ∈ dodecaConfig := by simp [dodecaConfig]
  have m4 : c₄ ∈ dodecaConfig := by simp [dodecaConfig]
  have m5 : c₅ ∈ dodecaConfig := by simp [dodecaConfig]
  have m6 : c₆ ∈ dodecaConfig := by simp [dodecaConfig]
  have m7 : c₇ ∈ dodecaConfig := by simp [dodecaConfig]
  have m8 : c₈ ∈ dodecaConfig := by simp [dodecaConfig]
  have mx1 : x₁ ∈ dodecaConfig := by simp [dodecaConfig]
  have mx2 : x₂ ∈ dodecaConfig := by simp [dodecaConfig]
  have mx3 : x₃ ∈ dodecaConfig := by simp [dodecaConfig]
  have mx4 : x₄ ∈ dodecaConfig := by simp [dodecaConfig]
  have mz1 : z₁ ∈ dodecaConfig := by simp [dodecaConfig]
  have mz2 : z₂ ∈ dodecaConfig := by simp [dodecaConfig]
  have mz3 : z₃ ∈ dodecaConfig := by simp [dodecaConfig]
  have mz4 : z₄ ∈ dodecaConfig := by simp [dodecaConfig]
  -- the eight flat-sum equations
  have eG1 := hmagic ⟨flatG1, rank_flatG1, card_flatG1⟩
  have eG2 := hmagic ⟨flatG2, rank_flatG2, card_flatG2⟩
  have eG3 := hmagic ⟨flatG3, rank_flatG3, card_flatG3⟩
  have eG4 := hmagic ⟨flatG4, rank_flatG4, card_flatG4⟩
  have eX1 := hmagic ⟨flatX1, rank_flatX1, card_flatX1⟩
  have eX2 := hmagic ⟨flatX2, rank_flatX2, card_flatX2⟩
  have eZ0 := hmagic ⟨flatZ0, rank_flatZ0, card_flatZ0⟩
  have eY0 := hmagic ⟨flatY0, rank_flatY0, card_flatY0⟩
  simp only [kFlatSum] at eG1 eG2 eG3 eG4 eX1 eX2 eZ0 eY0
  rw [filter_flatG1, Finset.sum_insert nG1a, Finset.sum_insert nG1b,
    Finset.sum_insert nG1c, Finset.sum_insert nzz, Finset.sum_singleton] at eG1
  rw [filter_flatG2, Finset.sum_insert nG2a, Finset.sum_insert nG2b,
    Finset.sum_insert nG2c, Finset.sum_insert nzz, Finset.sum_singleton] at eG2
  rw [filter_flatG3, Finset.sum_insert nG3a, Finset.sum_insert nG3b,
    Finset.sum_insert nG3c, Finset.sum_insert nzz', Finset.sum_singleton] at eG3
  rw [filter_flatG4, Finset.sum_insert nG4a, Finset.sum_insert nG4b,
    Finset.sum_insert nG4c, Finset.sum_insert nzz', Finset.sum_singleton] at eG4
  rw [filter_flatX1, Finset.sum_insert nX1a, Finset.sum_insert nX1b,
    Finset.sum_insert nX1c, Finset.sum_singleton] at eX1
  rw [filter_flatX2, Finset.sum_insert nX2a, Finset.sum_insert nX2b,
    Finset.sum_insert nX2c, Finset.sum_singleton] at eX2
  rw [filter_flatZ0, Finset.sum_insert nZ0a, Finset.sum_insert nZ0b,
    Finset.sum_insert nZ0c, Finset.sum_singleton] at eZ0
  rw [filter_flatY0, Finset.sum_insert nY0a, Finset.sum_insert nY0b,
    Finset.sum_insert nzz', Finset.sum_singleton] at eY0
  simp only [dif_pos m1, dif_pos m2, dif_pos m3, dif_pos m4, dif_pos m5,
    dif_pos m6, dif_pos m7, dif_pos m8, dif_pos mx1, dif_pos mx2, dif_pos mx3,
    dif_pos mx4, dif_pos mz1, dif_pos mz2, dif_pos mz3, dif_pos mz4]
    at eG1 eG2 eG3 eG4 eX1 eX2 eZ0 eY0
  -- (G1+G2+G3+G4) − (X1+X2) − Z0 − 2·Y0 : every weight cancels, leaving 0 = −c.
  linarith

end Erdos735OQ04Dodeca
