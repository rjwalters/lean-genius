/-
  Erdős Problem #735, Open Question #04 (oq-04) — S6d ACT (part i):
  The regular icosahedron is NOT a 2-flat-magic configuration in ℝ³.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).
  Sibling: `Proofs.Erdos735OQ04Octahedron` (S6b — octahedron refutation),
  whose generic helpers (`coordL`, `mem_mk'_ker_iff`, `rank_ker_two`,
  `ne_of_coord`) this file reuses.

  This file settles the first half of the S6d milestone (dodecahedron /
  icosahedron): the regular icosahedron at the standard golden-ratio
  coordinates — the cyclic permutations of `(0, ±1, ±φ)`, `φ = (1+√5)/2` —

      r₁  = ( 1,  φ, 0),  r₂  = ( 1, −φ, 0),  r₃  = (−1,  φ, 0),  r₄  = (−1, −φ, 0),
      r₅  = ( φ, 0,  1),  r₆  = ( φ, 0, −1),  r₇  = (−φ, 0,  1),  r₈  = (−φ, 0, −1),
      r₉  = (0,  1,  φ),  r₁₀ = (0,  1, −φ),  r₁₁ = (0, −1,  φ),  r₁₂ = (0, −1, −φ)

  is NOT 2-flat magic: no positive weighting gives all minimal-spanning
  2-flats the same weight-sum.  Together with the S6a tetrahedron witness and
  the S6b/c octahedron/cube refutations, this further pins the conjectured
  `k ≥ 2` magic family: of the Platonic solids checked so far only the
  tetrahedron (a simplex) is 2-flat magic — consistent with the S6e
  general-position theorem, which shows every affinely independent
  configuration is magic; the icosahedron, like the octahedron and cube, has
  determined 2-flats of unequal sizes (golden rectangles with 4 vertices vs
  triangular faces with 3), and that asymmetry kills magic.

  ## Proof architecture (4-flat linear-arithmetic route, as in S6b/c)

  Four explicit 2-flats suffice:

    * `flatIY` — the coordinate plane y = 0, a golden-rectangle plane
      containing r₅, r₆, r₇, r₈;
    * `flatIX` — the coordinate plane x = 0, containing r₉, r₁₀, r₁₁, r₁₂;
    * `flatF1` — the face plane x + (φ+1)·z = 2φ+1, containing r₅, r₉, r₁₁
      (the face {(φ,0,1), (0,1,φ), (0,−1,φ)}; the plane identity for r₉, r₁₁
      is exactly φ² = φ + 1);
    * `flatF2` — the mirror face plane x − (φ+1)·z = 2φ+1, containing
      r₆, r₁₀, r₁₂.

  If `w` were a magic weighting with constant `c`, writing `aᵢ` for the
  weight of `rᵢ`:

      (flatIY)  a₅ + a₆ + a₇ + a₈    = c
      (flatIX)  a₉ + a₁₀ + a₁₁ + a₁₂ = c
      (flatF1)  a₅ + a₉ + a₁₁        = c
      (flatF2)  a₆ + a₁₀ + a₁₂       = c

  Adding the first two and subtracting the last two gives `a₇ + a₈ = 0`,
  contradicting positivity.  `linarith` closes it.

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

namespace Erdos735OQ04Icosa

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

/- ## The twelve icosahedron vertices -/

noncomputable def r₁ : EuclideanSpace ℝ (Fin 3) := !₂[ 1,  phi, 0]
noncomputable def r₂ : EuclideanSpace ℝ (Fin 3) := !₂[ 1, -phi, 0]
noncomputable def r₃ : EuclideanSpace ℝ (Fin 3) := !₂[-1,  phi, 0]
noncomputable def r₄ : EuclideanSpace ℝ (Fin 3) := !₂[-1, -phi, 0]
noncomputable def r₅ : EuclideanSpace ℝ (Fin 3) := !₂[ phi, 0,  1]
noncomputable def r₆ : EuclideanSpace ℝ (Fin 3) := !₂[ phi, 0, -1]
noncomputable def r₇ : EuclideanSpace ℝ (Fin 3) := !₂[-phi, 0,  1]
noncomputable def r₈ : EuclideanSpace ℝ (Fin 3) := !₂[-phi, 0, -1]
noncomputable def r₉ : EuclideanSpace ℝ (Fin 3) := !₂[0,  1,  phi]
noncomputable def r₁₀ : EuclideanSpace ℝ (Fin 3) := !₂[0,  1, -phi]
noncomputable def r₁₁ : EuclideanSpace ℝ (Fin 3) := !₂[0, -1,  phi]
noncomputable def r₁₂ : EuclideanSpace ℝ (Fin 3) := !₂[0, -1, -phi]

/-- The icosahedron configuration. -/
noncomputable def icosaConfig : PointConfigD 3 :=
  {r₁, r₂, r₃, r₄, r₅, r₆, r₇, r₈, r₉, r₁₀, r₁₁, r₁₂}

/- ## Pairwise distinctness of the vertices used below

Rational coordinate pairs close by `norm_num`; the four `±φ` pairs reduce to
`φ ≠ 0` (`2φ ≠ 0` after `intro`). -/

lemma i56 : r₅ ≠ r₆ := ne_of_coord 2 (by
  norm_num [r₅, r₆, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma i57 : r₅ ≠ r₇ := ne_of_coord 0 (by
  simp only [r₅, r₇, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [one_lt_phi])
lemma i58 : r₅ ≠ r₈ := ne_of_coord 2 (by
  norm_num [r₅, r₈, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma i67 : r₆ ≠ r₇ := ne_of_coord 2 (by
  norm_num [r₆, r₇, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma i68 : r₆ ≠ r₈ := ne_of_coord 0 (by
  simp only [r₆, r₈, WithLp.ofLp_toLp, Matrix.cons_val_zero]
  intro h; linarith [one_lt_phi])
lemma i78 : r₇ ≠ r₈ := ne_of_coord 2 (by
  norm_num [r₇, r₈, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma i910 : r₉ ≠ r₁₀ := ne_of_coord 2 (by
  simp only [r₉, r₁₀, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi])
lemma i911 : r₉ ≠ r₁₁ := ne_of_coord 1 (by norm_num [r₉, r₁₁, WithLp.ofLp_toLp])
lemma i912 : r₉ ≠ r₁₂ := ne_of_coord 1 (by norm_num [r₉, r₁₂, WithLp.ofLp_toLp])
lemma i1011 : r₁₀ ≠ r₁₁ := ne_of_coord 1 (by norm_num [r₁₀, r₁₁, WithLp.ofLp_toLp])
lemma i1012 : r₁₀ ≠ r₁₂ := ne_of_coord 1 (by norm_num [r₁₀, r₁₂, WithLp.ofLp_toLp])
lemma i1112 : r₁₁ ≠ r₁₂ := ne_of_coord 2 (by
  simp only [r₁₁, r₁₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi])

lemma i59 : r₅ ≠ r₉ := ne_of_coord 1 (by norm_num [r₅, r₉, WithLp.ofLp_toLp])
lemma i511 : r₅ ≠ r₁₁ := ne_of_coord 1 (by norm_num [r₅, r₁₁, WithLp.ofLp_toLp])
lemma i610 : r₆ ≠ r₁₀ := ne_of_coord 1 (by norm_num [r₆, r₁₀, WithLp.ofLp_toLp])
lemma i612 : r₆ ≠ r₁₂ := ne_of_coord 1 (by norm_num [r₆, r₁₂, WithLp.ofLp_toLp])

/- ## The two face functionals -/

/-- The face functional `x ↦ x₀ + (φ+1)·x₂`. -/
noncomputable def faceLP : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  coordL 0 + (phi + 1) • coordL 2

lemma faceLP_apply (x : EuclideanSpace ℝ (Fin 3)) :
    faceLP x = WithLp.ofLp x 0 + (phi + 1) * WithLp.ofLp x 2 := rfl

/-- The mirror face functional `x ↦ x₀ − (φ+1)·x₂`. -/
noncomputable def faceLM : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] ℝ :=
  coordL 0 - (phi + 1) • coordL 2

lemma faceLM_apply (x : EuclideanSpace ℝ (Fin 3)) :
    faceLM x = WithLp.ofLp x 0 - (phi + 1) * WithLp.ofLp x 2 := rfl

/- ## The four flats -/

/-- The golden-rectangle plane `y = 0` (through r₅, r₆, r₇, r₈). -/
noncomputable def flatIY : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' 0 (LinearMap.ker (coordL 1))

/-- The golden-rectangle plane `x = 0` (through r₉, r₁₀, r₁₁, r₁₂). -/
noncomputable def flatIX : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' 0 (LinearMap.ker (coordL 0))

/-- The face plane `x + (φ+1)·z = 2φ+1` (through r₅, r₉, r₁₁). -/
noncomputable def flatF1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' r₅ (LinearMap.ker faceLP)

/-- The mirror face plane `x − (φ+1)·z = 2φ+1` (through r₆, r₁₀, r₁₂). -/
noncomputable def flatF2 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' r₆ (LinearMap.ker faceLM)

lemma mem_flatIY_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatIY ↔ WithLp.ofLp x 1 = 0 := by
  rw [flatIY, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp

lemma mem_flatIX_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatIX ↔ WithLp.ofLp x 0 = 0 := by
  rw [flatIX, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp

lemma faceLP_r₅ : faceLP r₅ = 2 * phi + 1 := by
  rw [faceLP_apply]
  simp only [r₅, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring

lemma faceLM_r₆ : faceLM r₆ = 2 * phi + 1 := by
  rw [faceLM_apply]
  simp only [r₆, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring

lemma mem_flatF1_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatF1 ↔ WithLp.ofLp x 0 + (phi + 1) * WithLp.ofLp x 2 = 2 * phi + 1 := by
  rw [flatF1, mem_mk'_ker_iff, faceLP_r₅, faceLP_apply]

lemma mem_flatF2_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatF2 ↔ WithLp.ofLp x 0 - (phi + 1) * WithLp.ofLp x 2 = 2 * phi + 1 := by
  rw [flatF2, mem_mk'_ker_iff, faceLM_r₆, faceLM_apply]

/- ## Direction ranks -/

lemma rank_flatIY : Module.rank ℝ flatIY.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatIY, AffineSubspace.direction_mk']
  exact rank_ker_two _ r₉ (by rw [coordL_apply]; norm_num [r₉, WithLp.ofLp_toLp])

lemma rank_flatIX : Module.rank ℝ flatIX.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatIX, AffineSubspace.direction_mk']
  exact rank_ker_two _ r₁ (by rw [coordL_apply]; norm_num [r₁, WithLp.ofLp_toLp])

lemma rank_flatF1 : Module.rank ℝ flatF1.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatF1, AffineSubspace.direction_mk']
  exact rank_ker_two _ r₅ (by rw [faceLP_r₅]; intro h; linarith [one_lt_phi])

lemma rank_flatF2 : Module.rank ℝ flatF2.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatF2, AffineSubspace.direction_mk']
  exact rank_ker_two _ r₆ (by rw [faceLM_r₆]; intro h; linarith [one_lt_phi])

/- ## Vertex membership decisions -/

/- flatIY (y = 0): in r₅ r₆ r₇ r₈; out r₁ r₂ r₃ r₄ (y = ±φ), r₉…r₁₂ (y = ±1). -/

lemma hIY1 : r₁ ∉ flatIY := by
  rw [mem_flatIY_iff]; simp [r₁, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIY2 : r₂ ∉ flatIY := by
  rw [mem_flatIY_iff]; simp [r₂, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIY3 : r₃ ∉ flatIY := by
  rw [mem_flatIY_iff]; simp [r₃, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIY4 : r₄ ∉ flatIY := by
  rw [mem_flatIY_iff]; simp [r₄, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIY5 : r₅ ∈ flatIY := (mem_flatIY_iff r₅).mpr (by simp [r₅, WithLp.ofLp_toLp])
lemma hIY6 : r₆ ∈ flatIY := (mem_flatIY_iff r₆).mpr (by simp [r₆, WithLp.ofLp_toLp])
lemma hIY7 : r₇ ∈ flatIY := (mem_flatIY_iff r₇).mpr (by simp [r₇, WithLp.ofLp_toLp])
lemma hIY8 : r₈ ∈ flatIY := (mem_flatIY_iff r₈).mpr (by simp [r₈, WithLp.ofLp_toLp])
lemma hIY9 : r₉ ∉ flatIY := by
  rw [mem_flatIY_iff]; norm_num [r₉, WithLp.ofLp_toLp]
lemma hIY10 : r₁₀ ∉ flatIY := by
  rw [mem_flatIY_iff]; norm_num [r₁₀, WithLp.ofLp_toLp]
lemma hIY11 : r₁₁ ∉ flatIY := by
  rw [mem_flatIY_iff]; norm_num [r₁₁, WithLp.ofLp_toLp]
lemma hIY12 : r₁₂ ∉ flatIY := by
  rw [mem_flatIY_iff]; norm_num [r₁₂, WithLp.ofLp_toLp]

/- flatIX (x = 0): in r₉…r₁₂; out r₁…r₄ (x = ±1), r₅…r₈ (x = ±φ). -/

lemma hIX1 : r₁ ∉ flatIX := by
  rw [mem_flatIX_iff]; norm_num [r₁, WithLp.ofLp_toLp]
lemma hIX2 : r₂ ∉ flatIX := by
  rw [mem_flatIX_iff]; norm_num [r₂, WithLp.ofLp_toLp]
lemma hIX3 : r₃ ∉ flatIX := by
  rw [mem_flatIX_iff]; norm_num [r₃, WithLp.ofLp_toLp]
lemma hIX4 : r₄ ∉ flatIX := by
  rw [mem_flatIX_iff]; norm_num [r₄, WithLp.ofLp_toLp]
lemma hIX5 : r₅ ∉ flatIX := by
  rw [mem_flatIX_iff]; simp [r₅, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIX6 : r₆ ∉ flatIX := by
  rw [mem_flatIX_iff]; simp [r₆, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIX7 : r₇ ∉ flatIX := by
  rw [mem_flatIX_iff]; simp [r₇, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIX8 : r₈ ∉ flatIX := by
  rw [mem_flatIX_iff]; simp [r₈, WithLp.ofLp_toLp]; exact phi_ne_zero
lemma hIX9 : r₉ ∈ flatIX := (mem_flatIX_iff r₉).mpr (by simp [r₉, WithLp.ofLp_toLp])
lemma hIX10 : r₁₀ ∈ flatIX := (mem_flatIX_iff r₁₀).mpr (by simp [r₁₀, WithLp.ofLp_toLp])
lemma hIX11 : r₁₁ ∈ flatIX := (mem_flatIX_iff r₁₁).mpr (by simp [r₁₁, WithLp.ofLp_toLp])
lemma hIX12 : r₁₂ ∈ flatIX := (mem_flatIX_iff r₁₂).mpr (by simp [r₁₂, WithLp.ofLp_toLp])

/- flatF1 (x + (φ+1)z = 2φ+1): in r₅, r₉, r₁₁ (via φ² = φ+1); out the rest. -/

lemma hF1_1 : r₁ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF1_2 : r₂ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₂, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF1_3 : r₃ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₃, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF1_4 : r₄ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₄, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF1_5 : r₅ ∈ flatF1 := (mem_flatF1_iff r₅).mpr (by
  simp only [r₅, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring)
lemma hF1_6 : r₆ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₆, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [one_lt_phi]
lemma hF1_7 : r₇ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₇, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [one_lt_phi]
lemma hF1_8 : r₈ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₈, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [one_lt_phi]
lemma hF1_9 : r₉ ∈ flatF1 := (mem_flatF1_iff r₉).mpr (by
  simp only [r₉, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination phi_sq)
lemma hF1_10 : r₁₀ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₁₀, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [phi_sq, one_lt_phi]
lemma hF1_11 : r₁₁ ∈ flatF1 := (mem_flatF1_iff r₁₁).mpr (by
  simp only [r₁₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination phi_sq)
lemma hF1_12 : r₁₂ ∉ flatF1 := by
  rw [mem_flatF1_iff]
  simp only [r₁₂, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [phi_sq, one_lt_phi]

/- flatF2 (x − (φ+1)z = 2φ+1): in r₆, r₁₀, r₁₂; out the rest. -/

lemma hF2_1 : r₁ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF2_2 : r₂ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₂, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF2_3 : r₃ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₃, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF2_4 : r₄ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₄, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; linarith [one_lt_phi]
lemma hF2_5 : r₅ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₅, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [one_lt_phi]
lemma hF2_6 : r₆ ∈ flatF2 := (mem_flatF2_iff r₆).mpr (by
  simp only [r₆, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  ring)
lemma hF2_7 : r₇ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₇, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [one_lt_phi]
lemma hF2_8 : r₈ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₈, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [one_lt_phi]
lemma hF2_9 : r₉ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₉, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [phi_sq, one_lt_phi]
lemma hF2_10 : r₁₀ ∈ flatF2 := (mem_flatF2_iff r₁₀).mpr (by
  simp only [r₁₀, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination phi_sq)
lemma hF2_11 : r₁₁ ∉ flatF2 := by
  rw [mem_flatF2_iff]
  simp only [r₁₁, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  intro h; nlinarith [phi_sq, one_lt_phi]
lemma hF2_12 : r₁₂ ∈ flatF2 := (mem_flatF2_iff r₁₂).mpr (by
  simp only [r₁₂, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.head_cons]
  linear_combination phi_sq)

/- ## Filtered point sets of the four flats -/

lemma filter_flatIY : icosaConfig.filter (· ∈ flatIY) = {r₅, r₆, r₇, r₈} := by
  rw [icosaConfig]
  rw [Finset.filter_insert, if_neg hIY1, Finset.filter_insert, if_neg hIY2,
    Finset.filter_insert, if_neg hIY3, Finset.filter_insert, if_neg hIY4,
    Finset.filter_insert, if_pos hIY5, Finset.filter_insert, if_pos hIY6,
    Finset.filter_insert, if_pos hIY7, Finset.filter_insert, if_pos hIY8,
    Finset.filter_insert, if_neg hIY9, Finset.filter_insert, if_neg hIY10,
    Finset.filter_insert, if_neg hIY11, Finset.filter_singleton, if_neg hIY12]
  rfl

lemma filter_flatIX : icosaConfig.filter (· ∈ flatIX) = {r₉, r₁₀, r₁₁, r₁₂} := by
  rw [icosaConfig]
  rw [Finset.filter_insert, if_neg hIX1, Finset.filter_insert, if_neg hIX2,
    Finset.filter_insert, if_neg hIX3, Finset.filter_insert, if_neg hIX4,
    Finset.filter_insert, if_neg hIX5, Finset.filter_insert, if_neg hIX6,
    Finset.filter_insert, if_neg hIX7, Finset.filter_insert, if_neg hIX8,
    Finset.filter_insert, if_pos hIX9, Finset.filter_insert, if_pos hIX10,
    Finset.filter_insert, if_pos hIX11, Finset.filter_singleton, if_pos hIX12]

lemma filter_flatF1 : icosaConfig.filter (· ∈ flatF1) = {r₅, r₉, r₁₁} := by
  rw [icosaConfig]
  rw [Finset.filter_insert, if_neg hF1_1, Finset.filter_insert, if_neg hF1_2,
    Finset.filter_insert, if_neg hF1_3, Finset.filter_insert, if_neg hF1_4,
    Finset.filter_insert, if_pos hF1_5, Finset.filter_insert, if_neg hF1_6,
    Finset.filter_insert, if_neg hF1_7, Finset.filter_insert, if_neg hF1_8,
    Finset.filter_insert, if_pos hF1_9, Finset.filter_insert, if_neg hF1_10,
    Finset.filter_insert, if_pos hF1_11, Finset.filter_singleton, if_neg hF1_12]
  rfl

lemma filter_flatF2 : icosaConfig.filter (· ∈ flatF2) = {r₆, r₁₀, r₁₂} := by
  rw [icosaConfig]
  rw [Finset.filter_insert, if_neg hF2_1, Finset.filter_insert, if_neg hF2_2,
    Finset.filter_insert, if_neg hF2_3, Finset.filter_insert, if_neg hF2_4,
    Finset.filter_insert, if_neg hF2_5, Finset.filter_insert, if_pos hF2_6,
    Finset.filter_insert, if_neg hF2_7, Finset.filter_insert, if_neg hF2_8,
    Finset.filter_insert, if_neg hF2_9, Finset.filter_insert, if_pos hF2_10,
    Finset.filter_insert, if_neg hF2_11, Finset.filter_singleton, if_pos hF2_12]

/- Non-membership facts for insert-chain card/sum computations. -/

lemma n5Y : r₅ ∉ ({r₆, r₇, r₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i56, i57, i58]
lemma n6Y : r₆ ∉ ({r₇, r₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i67, i68]
lemma n7Y : r₇ ∉ ({r₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i78]

lemma n9X : r₉ ∉ ({r₁₀, r₁₁, r₁₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i910, i911, i912]
lemma n10X : r₁₀ ∉ ({r₁₁, r₁₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i1011, i1012]
lemma n11X : r₁₁ ∉ ({r₁₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i1112]

lemma n5F1 : r₅ ∉ ({r₉, r₁₁} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i59, i511]
lemma n9F1 : r₉ ∉ ({r₁₁} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i911]

lemma n6F2 : r₆ ∉ ({r₁₀, r₁₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i610, i612]
lemma n10F2 : r₁₀ ∉ ({r₁₂} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [i1012]

/- ## The four flats as `ConfigKFlat 2 icosaConfig` elements -/

lemma card_flatIY : (icosaConfig.filter (· ∈ flatIY)).card ≥ 2 + 1 := by
  rw [filter_flatIY, Finset.card_insert_of_notMem n5Y,
    Finset.card_insert_of_notMem n6Y, Finset.card_insert_of_notMem n7Y,
    Finset.card_singleton]
  omega

lemma card_flatIX : (icosaConfig.filter (· ∈ flatIX)).card ≥ 2 + 1 := by
  rw [filter_flatIX, Finset.card_insert_of_notMem n9X,
    Finset.card_insert_of_notMem n10X, Finset.card_insert_of_notMem n11X,
    Finset.card_singleton]
  omega

lemma card_flatF1 : (icosaConfig.filter (· ∈ flatF1)).card ≥ 2 + 1 := by
  rw [filter_flatF1, Finset.card_insert_of_notMem n5F1,
    Finset.card_insert_of_notMem n9F1, Finset.card_singleton]

lemma card_flatF2 : (icosaConfig.filter (· ∈ flatF2)).card ≥ 2 + 1 := by
  rw [filter_flatF2, Finset.card_insert_of_notMem n6F2,
    Finset.card_insert_of_notMem n10F2, Finset.card_singleton]

/- ## Main theorem -/

/-- **The regular icosahedron is NOT 2-flat magic.**  The four flats
    `flatIY`, `flatIX`, `flatF1`, `flatF2` force `a₇ + a₈ = 0` for any magic
    weighting, contradicting positivity.  (S6d ACT part i; with S6a/b/c this
    makes the tetrahedron the only 2-flat-magic Platonic solid among the four
    checked so far.) -/
theorem icosa_not_isKFlatMagic : ¬ IsKFlatMagic 2 icosaConfig := by
  rintro ⟨w, c, hc, hmagic⟩
  -- canonical membership proofs (fixed once, so weight atoms are shared)
  have h5 : r₅ ∈ icosaConfig := by simp [icosaConfig]
  have h6 : r₆ ∈ icosaConfig := by simp [icosaConfig]
  have h7 : r₇ ∈ icosaConfig := by simp [icosaConfig]
  have h8 : r₈ ∈ icosaConfig := by simp [icosaConfig]
  have h9 : r₉ ∈ icosaConfig := by simp [icosaConfig]
  have h10 : r₁₀ ∈ icosaConfig := by simp [icosaConfig]
  have h11 : r₁₁ ∈ icosaConfig := by simp [icosaConfig]
  have h12 : r₁₂ ∈ icosaConfig := by simp [icosaConfig]
  -- the four flat-sum equations
  have eY := hmagic ⟨flatIY, rank_flatIY, card_flatIY⟩
  have eX := hmagic ⟨flatIX, rank_flatIX, card_flatIX⟩
  have eF1 := hmagic ⟨flatF1, rank_flatF1, card_flatF1⟩
  have eF2 := hmagic ⟨flatF2, rank_flatF2, card_flatF2⟩
  simp only [kFlatSum] at eY eX eF1 eF2
  rw [filter_flatIY, Finset.sum_insert n5Y, Finset.sum_insert n6Y,
    Finset.sum_insert n7Y, Finset.sum_singleton] at eY
  rw [filter_flatIX, Finset.sum_insert n9X, Finset.sum_insert n10X,
    Finset.sum_insert n11X, Finset.sum_singleton] at eX
  rw [filter_flatF1, Finset.sum_insert n5F1, Finset.sum_insert n9F1,
    Finset.sum_singleton] at eF1
  rw [filter_flatF2, Finset.sum_insert n6F2, Finset.sum_insert n10F2,
    Finset.sum_singleton] at eF2
  simp only [dif_pos h5, dif_pos h6, dif_pos h7, dif_pos h8,
    dif_pos h9, dif_pos h10, dif_pos h11, dif_pos h12] at eY eX eF1 eF2
  -- positivity of the two golden-rectangle weights outside the face planes
  have hw7 := w.property ⟨r₇, h7⟩
  have hw8 := w.property ⟨r₈, h8⟩
  -- (flatIY) + (flatIX) − (flatF1) − (flatF2) gives a₇ + a₈ = 0; contradiction
  linarith

end Erdos735OQ04Icosa
