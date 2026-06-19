/-
# Erdős–Mordell: oriented feet-angle building block (companion, cycle-34)

Cycle-34 diagnostic (researcher-9): the two residual geometric `sorry`s of the
pedal-feet chord identity (`chord_length_eq`, `angle_at_P` in
`ErdosMordellChordIdentity.lean`) were previously planned via
`InnerProductGeometry.angle_smul_left/right_of_pos` ("foot lies on the *positive*
ray from `X`"). That sub-approach is **false for obtuse triangles**: a numeric check
with `X=(0,0)`, `Y=(1,0)`, `Z=(-1,0.1)` (angle at `X` obtuse) and interior
`P=(0.7,0.01)` gives `⟨P-X, Z-X⟩ = -0.699 < 0`, so the foot `F_b = pedalFoot P Z X`
lands on the **negative** ray and `∠ F_b X F_c = π − ∠YXZ`, not `∠YXZ`. (The chord
identity itself stays true — `sin` is symmetric under `θ ↦ π−θ`, and the
supplementary-angle value of `angle_at_P` is *also* reached in the obtuse case via
the "same-segment" inscribed-angle relation rather than "opposite angles".)

The robust route that unifies the acute/obtuse cases is the **oriented doubled
angle** `2 • ∡`, which is invariant under reflecting a ray through its base point
(`2 • π ≡ 0` in `Real.Angle`). This file proves the universally-true building block

    2 • ∡ (pedalFoot P Z X) X (pedalFoot P X Y) = 2 • ∡ Z X Y,

i.e. twice the oriented angle subtended at `X` by the two pedal feet equals twice
the triangle's oriented angle at `X` — *no acute/obtuse case split, no positivity
hypothesis*. Each foot lies on the corresponding side line through `X`
(`orthogonalProjection_mem`), so `Collinear.two_zsmul_oangle_eq_left/right` swaps
`F_b ↦ Z` and `F_c ↦ Y` directly. Combined with the already-proved cospherical
identity `two_zsmul_oangle_pedalFeet_at_P_eq_at_X`
(`2 • ∡ F_b P F_c = 2 • ∡ F_b X F_c`) this pins
`2 • ∡ F_b P F_c = 2 • ∡ Z X Y`, leaving only the oriented→unoriented conversion as
the genuine remaining gap on the cosine side.

Self-contained (own `pedalFoot`, own oriented instances); does not touch the main
files and is not registered in `Proofs.lean`.
-/
import Mathlib

open EuclideanGeometry Metric

namespace ErdosMordellFeet

/-- The pedal foot: orthogonal projection of `P` onto line `XY`. The
`orthogonalProjection` needs a `[Nonempty ↥s]` instance, supplied here from
`X ∈ affineSpan ℝ {X, Y}`. -/
noncomputable def pedalFoot (P X Y : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  haveI : Nonempty (↥(affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))))) :=
    ⟨⟨X, subset_affineSpan ℝ {X, Y} (by simp)⟩⟩
  (orthogonalProjection (affineSpan ℝ {X, Y}) P : EuclideanSpace ℝ (Fin 2))

/-- `∡` on `EuclideanSpace ℝ (Fin 2)` needs a chosen orientation; register one from
the standard orthonormal basis (any fixed orientation works for a `2 • ∡` identity). -/
noncomputable instance instOrientedEuclideanFin2 :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2) :=
  ⟨(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation⟩

/-- `∡` also requires `Fact (finrank = 2)`; discharge via `finrank_euclideanSpace_fin`. -/
instance instFactFinrankEuclideanFin2 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2) :=
  ⟨finrank_euclideanSpace_fin⟩

/-- The pedal foot lies on the line it is projected onto. -/
theorem pedalFoot_mem_affineSpan (P X Y : EuclideanSpace ℝ (Fin 2)) :
    pedalFoot P X Y ∈ affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))) := by
  haveI : Nonempty (↥(affineSpan ℝ ({X, Y} : Set (EuclideanSpace ℝ (Fin 2))))) :=
    ⟨⟨X, subset_affineSpan ℝ {X, Y} (by simp)⟩⟩
  unfold pedalFoot
  exact orthogonalProjection_mem P

/-- The foot, together with the two points generating its line `{X, Y}`, is collinear
(generator order: `foot, X, Y`). Used for the right-hand swap `F_c ↦ Y`. -/
theorem collinear_pedalFoot (P X Y : EuclideanSpace ℝ (Fin 2)) :
    Collinear ℝ ({pedalFoot P X Y, X, Y} : Set (EuclideanSpace ℝ (Fin 2))) := by
  rw [collinear_insert_iff_of_mem_affineSpan (pedalFoot_mem_affineSpan P X Y)]
  exact collinear_pair ℝ X Y

/-- Same collinearity with the *second* generator placed in the middle
(`foot, B, A` for the foot onto line `{A, B}`). Used for the left-hand swap
`F_b ↦ Z` where the shared vertex `X` is the second generator of line `{Z, X}`. -/
theorem collinear_foot_vertex (P A B : EuclideanSpace ℝ (Fin 2)) :
    Collinear ℝ ({pedalFoot P A B, B, A} : Set (EuclideanSpace ℝ (Fin 2))) := by
  have h : pedalFoot P A B ∈ affineSpan ℝ ({B, A} : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [Set.pair_comm]; exact pedalFoot_mem_affineSpan P A B
  rw [collinear_insert_iff_of_mem_affineSpan h]
  exact collinear_pair ℝ B A

/-- **Oriented feet-angle at `X` (the case-free building block).**

Twice the oriented angle subtended at `X` by the two pedal feet
`F_b = pedalFoot P Z X`, `F_c = pedalFoot P X Y` equals twice the triangle's
oriented angle `∡ Z X Y`. Holds for *all* triangles (acute or obtuse at `X`) with
no positivity/betweenness hypothesis: each foot lies on its side line through `X`,
so `Collinear.two_zsmul_oangle_eq_left/right` swaps `F_b ↦ Z` and `F_c ↦ Y`, the
`2 • ∡` killing the ray-direction ambiguity (`2 • π ≡ 0`). The four `≠ X`
hypotheses (each foot distinct from `X`, and `Z, Y ≠ X`) are the only
nondegeneracy needed; for `P` interior to the nondegenerate triangle they all hold. -/
theorem two_zsmul_oangle_feet_at_X
    (P X Y Z : EuclideanSpace ℝ (Fin 2))
    (hbX : pedalFoot P Z X ≠ X) (hcX : pedalFoot P X Y ≠ X)
    (hZX : Z ≠ X) (hYX : Y ≠ X) :
    (2 : ℤ) • ∡ (pedalFoot P Z X) X (pedalFoot P X Y)
      = (2 : ℤ) • ∡ Z X Y := by
  have h1 : (2 : ℤ) • ∡ (pedalFoot P Z X) X (pedalFoot P X Y)
      = (2 : ℤ) • ∡ Z X (pedalFoot P X Y) :=
    (collinear_foot_vertex P Z X).two_zsmul_oangle_eq_left hbX hZX
  have h2 : (2 : ℤ) • ∡ Z X (pedalFoot P X Y) = (2 : ℤ) • ∡ Z X Y :=
    (collinear_pedalFoot P X Y).two_zsmul_oangle_eq_right hcX hYX
  rw [h1, h2]

end ErdosMordellFeet
