import Proofs.Erdos85OrderFortyNineT0NormalizationCore

/-!
# Two-cube certificate bridge for the `h = 7, t = 0` representative
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- Encoding soundness stated on the lightweight relation interface. -/
def SevenHighT0CubeCoreCnfSound : Prop :=
  ∀ cube edges,
    SevenHighT0CubeRelationCore cube (orderFortyNineBitAdj edges) →
    ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf cube).Sat assignment

/-- Lightweight exclusion statement, definitionally matching the `(0,0)`
canonical-representative exclusion used by the aggregate certificate bridge. -/
def SevenHighT0CoreExcluded : Prop :=
  ∀ edges : BitVec 1176,
    orderFortyNineBooleanConstraints 7 sevenHighT0Masks edges → False

/-- The global normalization and residual action reduce semantic coverage to
the two CNFs numbered zero and one. -/
theorem sevenHighT0_twoCubeSemanticCover
    (hsound : SevenHighT0CubeCoreCnfSound)
    (edges : BitVec 1176)
    (hedges : orderFortyNineBooleanConstraints 7 sevenHighT0Masks edges) :
    ∃ cube : Fin 2, ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf cube.val).Sat assignment := by
  obtain ⟨cube, normalizedEdges, hnormalized⟩ :=
    sevenHighT0_exists_normalized_relationCore_zero_or_one edges hedges
  obtain ⟨assignment, hsat⟩ :=
    hsound cube.val normalizedEdges hnormalized
  exact ⟨cube, assignment, hsat⟩

/-- Checked refutations of cubes zero and one exclude the canonical empty
triple-system representative. -/
theorem sevenHighT0_excluded_of_twoCube_lratChecks
    (hsound : SevenHighT0CubeCoreCnfSound)
    (hchecks : ∀ cube : Fin 2,
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedH7T0CubeSatCnf cube.val)) :
    SevenHighT0CoreExcluded := by
  intro edges hedges
  obtain ⟨cube, assignment, hsat⟩ :=
    sevenHighT0_twoCubeSemanticCover hsound edges hedges
  obtain ⟨proof, hcheck⟩ := hchecks cube
  have hunsat := LRAT.check_sound proof
    (orderFortyNineGeneratedH7T0CubeSatCnf cube.val) hcheck
  have hfalse := hunsat assignment
  rw [hsat] at hfalse
  contradiction

end Erdos85
