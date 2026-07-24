/-
  Erdős Problem #735, Open Question #04 (oq-04) — S6c ACT:
  The cube is NOT a 2-flat-magic configuration in ℝ³.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).
  Sibling: `Proofs.Erdos735OQ04Octahedron` (S6b — octahedron refutation),
  whose generic helpers (`coordL`, `sumL`, `mem_mk'_ker_iff`, `rank_ker_two`,
  `ne_of_coord`) this file reuses.

  This completes the S6b/c refutation pair designed in the S6b PREP
  (sessions/2026-05-13-s6b-prep-octahedron-cube-not-2-flat-magic.md): the S1
  OBSERVE claim that the cube at vertices {±1}³ is 2-flat magic is FALSE.
  Of the three polytopes named by S1 OBSERVE (tetrahedron, octahedron, cube),
  only the tetrahedron is 2-flat magic (`Proofs.Erdos735OQ04Tetrahedron`).

  ## Proof architecture (4-flat linear-arithmetic route)

  Four explicit 2-flats suffice, with vertices

      q₁ = ( 1, 1, 1),  q₂ = ( 1, 1,-1),  q₃ = ( 1,-1, 1),  q₄ = ( 1,-1,-1),
      q₅ = (-1, 1, 1),  q₆ = (-1, 1,-1),  q₇ = (-1,-1, 1),  q₈ = (-1,-1,-1):

    * `flatX1` — the face plane x =  1, containing q₁, q₂, q₃, q₄;
    * `flatX2` — the face plane x = -1, containing q₅, q₆, q₇, q₈;
    * `flatCP` — the corner plane x + y + z =  1, containing q₂, q₃, q₅;
    * `flatCM` — the corner plane x + y + z = -1, containing q₄, q₆, q₇.

  If `w` were a magic weighting with constant `c`, writing `aᵢ` for the weight
  of `qᵢ`:

      (flatX1)  a₁ + a₂ + a₃ + a₄ = c
      (flatX2)  a₅ + a₆ + a₇ + a₈ = c
      (flatCP)  a₂ + a₃ + a₅      = c
      (flatCM)  a₄ + a₆ + a₇      = c

  Adding the first two and subtracting the last two gives `a₁ + a₈ = 0`,
  contradicting positivity. `linarith` closes it.

  Counts: 0 axioms, 0 sorries.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Proofs.Erdos735OQ04
import Proofs.Erdos735OQ04Octahedron

namespace Erdos735OQ04Cube

open Erdos735OQ04
open Erdos735OQ04Octa (ne_of_coord coordL coordL_apply sumL sumL_apply
  mem_mk'_ker_iff rank_ker_two)
open scoped Classical

/- ## The eight cube vertices -/

/-- Cube vertex `( 1, 1, 1)`. -/
noncomputable def q₁ : EuclideanSpace ℝ (Fin 3) := !₂[ 1,  1,  1]
/-- Cube vertex `( 1, 1,-1)`. -/
noncomputable def q₂ : EuclideanSpace ℝ (Fin 3) := !₂[ 1,  1, -1]
/-- Cube vertex `( 1,-1, 1)`. -/
noncomputable def q₃ : EuclideanSpace ℝ (Fin 3) := !₂[ 1, -1,  1]
/-- Cube vertex `( 1,-1,-1)`. -/
noncomputable def q₄ : EuclideanSpace ℝ (Fin 3) := !₂[ 1, -1, -1]
/-- Cube vertex `(-1, 1, 1)`. -/
noncomputable def q₅ : EuclideanSpace ℝ (Fin 3) := !₂[-1,  1,  1]
/-- Cube vertex `(-1, 1,-1)`. -/
noncomputable def q₆ : EuclideanSpace ℝ (Fin 3) := !₂[-1,  1, -1]
/-- Cube vertex `(-1,-1, 1)`. -/
noncomputable def q₇ : EuclideanSpace ℝ (Fin 3) := !₂[-1, -1,  1]
/-- Cube vertex `(-1,-1,-1)`. -/
noncomputable def q₈ : EuclideanSpace ℝ (Fin 3) := !₂[-1, -1, -1]

/-- The cube as a `PointConfigD 3`. -/
noncomputable def cubeConfig : PointConfigD 3 := {q₁, q₂, q₃, q₄, q₅, q₆, q₇, q₈}

/- Pairwise distinctness of the vertices used below. -/

lemma q12 : q₁ ≠ q₂ := ne_of_coord 2 (by
  norm_num [q₁, q₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma q13 : q₁ ≠ q₃ := ne_of_coord 1 (by norm_num [q₁, q₃, WithLp.ofLp_toLp])
lemma q14 : q₁ ≠ q₄ := ne_of_coord 1 (by norm_num [q₁, q₄, WithLp.ofLp_toLp])
lemma q23 : q₂ ≠ q₃ := ne_of_coord 1 (by norm_num [q₂, q₃, WithLp.ofLp_toLp])
lemma q24 : q₂ ≠ q₄ := ne_of_coord 1 (by norm_num [q₂, q₄, WithLp.ofLp_toLp])
lemma q25 : q₂ ≠ q₅ := ne_of_coord 0 (by norm_num [q₂, q₅, WithLp.ofLp_toLp])
lemma q34 : q₃ ≠ q₄ := ne_of_coord 2 (by
  norm_num [q₃, q₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma q35 : q₃ ≠ q₅ := ne_of_coord 0 (by norm_num [q₃, q₅, WithLp.ofLp_toLp])
lemma q46 : q₄ ≠ q₆ := ne_of_coord 0 (by norm_num [q₄, q₆, WithLp.ofLp_toLp])
lemma q47 : q₄ ≠ q₇ := ne_of_coord 0 (by norm_num [q₄, q₇, WithLp.ofLp_toLp])
lemma q56 : q₅ ≠ q₆ := ne_of_coord 2 (by
  norm_num [q₅, q₆, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma q57 : q₅ ≠ q₇ := ne_of_coord 1 (by norm_num [q₅, q₇, WithLp.ofLp_toLp])
lemma q58 : q₅ ≠ q₈ := ne_of_coord 1 (by norm_num [q₅, q₈, WithLp.ofLp_toLp])
lemma q67 : q₆ ≠ q₇ := ne_of_coord 1 (by norm_num [q₆, q₇, WithLp.ofLp_toLp])
lemma q68 : q₆ ≠ q₈ := ne_of_coord 1 (by norm_num [q₆, q₈, WithLp.ofLp_toLp])
lemma q78 : q₇ ≠ q₈ := ne_of_coord 2 (by
  norm_num [q₇, q₈, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

/- ## The four flats -/

/-- The face plane `x = 1`. -/
noncomputable def flatX1 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' q₁ (LinearMap.ker (coordL 0))

/-- The face plane `x = -1`. -/
noncomputable def flatX2 : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' q₅ (LinearMap.ker (coordL 0))

/-- The corner plane `x + y + z = 1`. -/
noncomputable def flatCP : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' q₂ (LinearMap.ker sumL)

/-- The corner plane `x + y + z = -1`. -/
noncomputable def flatCM : AffineSubspace ℝ (EuclideanSpace ℝ (Fin 3)) :=
  AffineSubspace.mk' q₄ (LinearMap.ker sumL)

lemma mem_flatX1_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatX1 ↔ WithLp.ofLp x 0 = 1 := by
  rw [flatX1, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp [q₁, WithLp.ofLp_toLp]

lemma mem_flatX2_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatX2 ↔ WithLp.ofLp x 0 = -1 := by
  rw [flatX2, mem_mk'_ker_iff, coordL_apply, coordL_apply]
  simp [q₅, WithLp.ofLp_toLp]

lemma mem_flatCP_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatCP ↔ WithLp.ofLp x 0 + WithLp.ofLp x 1 + WithLp.ofLp x 2 = 1 := by
  rw [flatCP, mem_mk'_ker_iff, sumL_apply, sumL_apply]
  norm_num [q₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

lemma mem_flatCM_iff (x : EuclideanSpace ℝ (Fin 3)) :
    x ∈ flatCM ↔ WithLp.ofLp x 0 + WithLp.ofLp x 1 + WithLp.ofLp x 2 = -1 := by
  rw [flatCM, mem_mk'_ker_iff, sumL_apply, sumL_apply]
  norm_num [q₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/- ## Direction ranks -/

lemma rank_flatX1 : Module.rank ℝ flatX1.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatX1, AffineSubspace.direction_mk']
  exact rank_ker_two _ q₁ (by rw [coordL_apply]; norm_num [q₁, WithLp.ofLp_toLp])

lemma rank_flatX2 : Module.rank ℝ flatX2.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatX2, AffineSubspace.direction_mk']
  exact rank_ker_two _ q₁ (by rw [coordL_apply]; norm_num [q₁, WithLp.ofLp_toLp])

lemma rank_sumL_ker' : Module.rank ℝ (LinearMap.ker sumL) = ((2 : ℕ) : Cardinal) :=
  rank_ker_two _ q₁ (by
    rw [sumL_apply]
    norm_num [q₁, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])

lemma rank_flatCP : Module.rank ℝ flatCP.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatCP, AffineSubspace.direction_mk']
  exact rank_sumL_ker'

lemma rank_flatCM : Module.rank ℝ flatCM.direction = ((2 : ℕ) : Cardinal) := by
  rw [flatCM, AffineSubspace.direction_mk']
  exact rank_sumL_ker'

/- ## Vertex membership decisions -/

lemma hX1q1 : q₁ ∈ flatX1 := (mem_flatX1_iff q₁).mpr (by norm_num [q₁, WithLp.ofLp_toLp])
lemma hX1q2 : q₂ ∈ flatX1 := (mem_flatX1_iff q₂).mpr (by norm_num [q₂, WithLp.ofLp_toLp])
lemma hX1q3 : q₃ ∈ flatX1 := (mem_flatX1_iff q₃).mpr (by norm_num [q₃, WithLp.ofLp_toLp])
lemma hX1q4 : q₄ ∈ flatX1 := (mem_flatX1_iff q₄).mpr (by norm_num [q₄, WithLp.ofLp_toLp])
lemma hX1q5 : q₅ ∉ flatX1 := by
  rw [mem_flatX1_iff]; norm_num [q₅, WithLp.ofLp_toLp]
lemma hX1q6 : q₆ ∉ flatX1 := by
  rw [mem_flatX1_iff]; norm_num [q₆, WithLp.ofLp_toLp]
lemma hX1q7 : q₇ ∉ flatX1 := by
  rw [mem_flatX1_iff]; norm_num [q₇, WithLp.ofLp_toLp]
lemma hX1q8 : q₈ ∉ flatX1 := by
  rw [mem_flatX1_iff]; norm_num [q₈, WithLp.ofLp_toLp]

lemma hX2q1 : q₁ ∉ flatX2 := by
  rw [mem_flatX2_iff]; norm_num [q₁, WithLp.ofLp_toLp]
lemma hX2q2 : q₂ ∉ flatX2 := by
  rw [mem_flatX2_iff]; norm_num [q₂, WithLp.ofLp_toLp]
lemma hX2q3 : q₃ ∉ flatX2 := by
  rw [mem_flatX2_iff]; norm_num [q₃, WithLp.ofLp_toLp]
lemma hX2q4 : q₄ ∉ flatX2 := by
  rw [mem_flatX2_iff]; norm_num [q₄, WithLp.ofLp_toLp]
lemma hX2q5 : q₅ ∈ flatX2 := (mem_flatX2_iff q₅).mpr (by norm_num [q₅, WithLp.ofLp_toLp])
lemma hX2q6 : q₆ ∈ flatX2 := (mem_flatX2_iff q₆).mpr (by norm_num [q₆, WithLp.ofLp_toLp])
lemma hX2q7 : q₇ ∈ flatX2 := (mem_flatX2_iff q₇).mpr (by norm_num [q₇, WithLp.ofLp_toLp])
lemma hX2q8 : q₈ ∈ flatX2 := (mem_flatX2_iff q₈).mpr (by norm_num [q₈, WithLp.ofLp_toLp])

lemma hCPq1 : q₁ ∉ flatCP := by
  rw [mem_flatCP_iff]
  norm_num [q₁, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCPq2 : q₂ ∈ flatCP := (mem_flatCP_iff q₂).mpr (by
  norm_num [q₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma hCPq3 : q₃ ∈ flatCP := (mem_flatCP_iff q₃).mpr (by
  norm_num [q₃, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma hCPq4 : q₄ ∉ flatCP := by
  rw [mem_flatCP_iff]
  norm_num [q₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCPq5 : q₅ ∈ flatCP := (mem_flatCP_iff q₅).mpr (by
  norm_num [q₅, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma hCPq6 : q₆ ∉ flatCP := by
  rw [mem_flatCP_iff]
  norm_num [q₆, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCPq7 : q₇ ∉ flatCP := by
  rw [mem_flatCP_iff]
  norm_num [q₇, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCPq8 : q₈ ∉ flatCP := by
  rw [mem_flatCP_iff]
  norm_num [q₈, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

lemma hCMq1 : q₁ ∉ flatCM := by
  rw [mem_flatCM_iff]
  norm_num [q₁, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCMq2 : q₂ ∉ flatCM := by
  rw [mem_flatCM_iff]
  norm_num [q₂, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCMq3 : q₃ ∉ flatCM := by
  rw [mem_flatCM_iff]
  norm_num [q₃, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCMq4 : q₄ ∈ flatCM := (mem_flatCM_iff q₄).mpr (by
  norm_num [q₄, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma hCMq5 : q₅ ∉ flatCM := by
  rw [mem_flatCM_iff]
  norm_num [q₅, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
lemma hCMq6 : q₆ ∈ flatCM := (mem_flatCM_iff q₆).mpr (by
  norm_num [q₆, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma hCMq7 : q₇ ∈ flatCM := (mem_flatCM_iff q₇).mpr (by
  norm_num [q₇, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons])
lemma hCMq8 : q₈ ∉ flatCM := by
  rw [mem_flatCM_iff]
  norm_num [q₈, WithLp.ofLp_toLp, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

/- ## Filtered point sets of the four flats -/

lemma filter_flatX1 : cubeConfig.filter (· ∈ flatX1) = {q₁, q₂, q₃, q₄} := by
  rw [cubeConfig]
  rw [Finset.filter_insert, if_pos hX1q1, Finset.filter_insert, if_pos hX1q2,
    Finset.filter_insert, if_pos hX1q3, Finset.filter_insert, if_pos hX1q4,
    Finset.filter_insert, if_neg hX1q5, Finset.filter_insert, if_neg hX1q6,
    Finset.filter_insert, if_neg hX1q7, Finset.filter_singleton, if_neg hX1q8]
  rfl

lemma filter_flatX2 : cubeConfig.filter (· ∈ flatX2) = {q₅, q₆, q₇, q₈} := by
  rw [cubeConfig]
  rw [Finset.filter_insert, if_neg hX2q1, Finset.filter_insert, if_neg hX2q2,
    Finset.filter_insert, if_neg hX2q3, Finset.filter_insert, if_neg hX2q4,
    Finset.filter_insert, if_pos hX2q5, Finset.filter_insert, if_pos hX2q6,
    Finset.filter_insert, if_pos hX2q7, Finset.filter_singleton, if_pos hX2q8]

lemma filter_flatCP : cubeConfig.filter (· ∈ flatCP) = {q₂, q₃, q₅} := by
  rw [cubeConfig]
  rw [Finset.filter_insert, if_neg hCPq1, Finset.filter_insert, if_pos hCPq2,
    Finset.filter_insert, if_pos hCPq3, Finset.filter_insert, if_neg hCPq4,
    Finset.filter_insert, if_pos hCPq5, Finset.filter_insert, if_neg hCPq6,
    Finset.filter_insert, if_neg hCPq7, Finset.filter_singleton, if_neg hCPq8]
  rfl

lemma filter_flatCM : cubeConfig.filter (· ∈ flatCM) = {q₄, q₆, q₇} := by
  rw [cubeConfig]
  rw [Finset.filter_insert, if_neg hCMq1, Finset.filter_insert, if_neg hCMq2,
    Finset.filter_insert, if_neg hCMq3, Finset.filter_insert, if_pos hCMq4,
    Finset.filter_insert, if_neg hCMq5, Finset.filter_insert, if_pos hCMq6,
    Finset.filter_insert, if_pos hCMq7, Finset.filter_singleton, if_neg hCMq8]
  rfl

/- Non-membership facts for insert-chain card/sum computations. -/

lemma n1X1 : q₁ ∉ ({q₂, q₃, q₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q12, q13, q14]
lemma n2X1 : q₂ ∉ ({q₃, q₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q23, q24]
lemma n3X1 : q₃ ∉ ({q₄} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q34]

lemma n5X2 : q₅ ∉ ({q₆, q₇, q₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q56, q57, q58]
lemma n6X2 : q₆ ∉ ({q₇, q₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q67, q68]
lemma n7X2 : q₇ ∉ ({q₈} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q78]

lemma n2CP : q₂ ∉ ({q₃, q₅} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q23, q25]
lemma n3CP : q₃ ∉ ({q₅} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q35]

lemma n4CM : q₄ ∉ ({q₆, q₇} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q46, q47]
lemma n6CM : q₆ ∉ ({q₇} : Finset (EuclideanSpace ℝ (Fin 3))) := by
  simp [q67]

/- ## The four flats as `ConfigKFlat 2 cubeConfig` elements -/

lemma card_flatX1 : (cubeConfig.filter (· ∈ flatX1)).card ≥ 2 + 1 := by
  rw [filter_flatX1, Finset.card_insert_of_notMem n1X1,
    Finset.card_insert_of_notMem n2X1, Finset.card_insert_of_notMem n3X1,
    Finset.card_singleton]
  omega

lemma card_flatX2 : (cubeConfig.filter (· ∈ flatX2)).card ≥ 2 + 1 := by
  rw [filter_flatX2, Finset.card_insert_of_notMem n5X2,
    Finset.card_insert_of_notMem n6X2, Finset.card_insert_of_notMem n7X2,
    Finset.card_singleton]
  omega

lemma card_flatCP : (cubeConfig.filter (· ∈ flatCP)).card ≥ 2 + 1 := by
  rw [filter_flatCP, Finset.card_insert_of_notMem n2CP,
    Finset.card_insert_of_notMem n3CP, Finset.card_singleton]

lemma card_flatCM : (cubeConfig.filter (· ∈ flatCM)).card ≥ 2 + 1 := by
  rw [filter_flatCM, Finset.card_insert_of_notMem n4CM,
    Finset.card_insert_of_notMem n6CM, Finset.card_singleton]

/- ## Main theorem -/

/-- **The cube is NOT 2-flat magic.**  The four flats `flatX1`, `flatX2`,
    `flatCP`, `flatCM` force `a₁ + a₈ = 0` for any magic weighting,
    contradicting positivity.  (S6c ACT; refutes the S1 OBSERVE cube claim.
    With S6a and S6b this settles all three polytopes named by S1 OBSERVE:
    only the tetrahedron is 2-flat magic.) -/
theorem cube_not_isKFlatMagic : ¬ IsKFlatMagic 2 cubeConfig := by
  rintro ⟨w, c, hc, hmagic⟩
  -- canonical membership proofs (fixed once, so weight atoms are shared)
  have hq₁ : q₁ ∈ cubeConfig := by simp [cubeConfig]
  have hq₂ : q₂ ∈ cubeConfig := by simp [cubeConfig]
  have hq₃ : q₃ ∈ cubeConfig := by simp [cubeConfig]
  have hq₄ : q₄ ∈ cubeConfig := by simp [cubeConfig]
  have hq₅ : q₅ ∈ cubeConfig := by simp [cubeConfig]
  have hq₆ : q₆ ∈ cubeConfig := by simp [cubeConfig]
  have hq₇ : q₇ ∈ cubeConfig := by simp [cubeConfig]
  have hq₈ : q₈ ∈ cubeConfig := by simp [cubeConfig]
  -- the four flat-sum equations
  have eX1 := hmagic ⟨flatX1, rank_flatX1, card_flatX1⟩
  have eX2 := hmagic ⟨flatX2, rank_flatX2, card_flatX2⟩
  have eCP := hmagic ⟨flatCP, rank_flatCP, card_flatCP⟩
  have eCM := hmagic ⟨flatCM, rank_flatCM, card_flatCM⟩
  simp only [kFlatSum] at eX1 eX2 eCP eCM
  rw [filter_flatX1, Finset.sum_insert n1X1, Finset.sum_insert n2X1,
    Finset.sum_insert n3X1, Finset.sum_singleton] at eX1
  rw [filter_flatX2, Finset.sum_insert n5X2, Finset.sum_insert n6X2,
    Finset.sum_insert n7X2, Finset.sum_singleton] at eX2
  rw [filter_flatCP, Finset.sum_insert n2CP, Finset.sum_insert n3CP,
    Finset.sum_singleton] at eCP
  rw [filter_flatCM, Finset.sum_insert n4CM, Finset.sum_insert n6CM,
    Finset.sum_singleton] at eCM
  simp only [dif_pos hq₁, dif_pos hq₂, dif_pos hq₃, dif_pos hq₄,
    dif_pos hq₅, dif_pos hq₆, dif_pos hq₇, dif_pos hq₈] at eX1 eX2 eCP eCM
  -- positivity of the two corner weights
  have h1 := w.property ⟨q₁, hq₁⟩
  have h8 := w.property ⟨q₈, hq₈⟩
  -- (flatX1) + (flatX2) − (flatCP) − (flatCM) gives a₁ + a₈ = 0; contradiction
  linarith

end Erdos735OQ04Cube
