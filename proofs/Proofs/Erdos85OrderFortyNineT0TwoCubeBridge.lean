import Proofs.Erdos85OrderFortyNineT0NormalizationCore
import Proofs.Erdos85OrderFortyNineSevenHighCanonicalCapstone

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

/-- Cube zero is impossible without invoking its CNF: vertices `7` and `9`
would have the two distinct common neighbors `0` and `15`. -/
theorem sevenHighT0_relationCore_zero_false
    (adj : Fin 49 → Fin 49 → Bool)
    (hsymm : ∀ i j, adj i j = adj j i)
    (h : SevenHighT0CubeRelationCore 0 adj) : False := by
  rcases h with ⟨_, _, hn0, _, _, hm1, _, hc4, _, _, hcubes⟩
  have h07 : adj 0 7 = true := by simpa using hn0 7 (by omega)
  have h09 : adj 0 9 = true := by simpa using hn0 9 (by omega)
  have h715 : adj 7 15 = true := by
    have hm := hm1 7 15 (Or.inl rfl) (Or.inr ⟨by omega, by omega⟩)
      (by decide)
    simpa [sevenHighT0CubeMatching1] using hm
  have h915 : adj 9 15 = true := by
    have hu := hcubes 0
    simpa using hu
  let common := Finset.univ.filter fun w => adj 7 w && adj 9 w
  have hzero : (0 : Fin 49) ∈ common := by
    simp [common, (hsymm 7 0).trans h07,
      (hsymm 9 0).trans h09]
  have hfifteen : (15 : Fin 49) ∈ common := by
    simp [common, h715, h915]
  have heq := (Finset.card_le_one.mp
    (hc4 7 9 (by decide))) 0 hzero 15 hfifteen
  exact (by decide : (0 : Fin 49) ≠ 15) heq

/-- Only cube one needs an encoding-soundness proof. -/
def SevenHighT0CubeOneCnfSound : Prop :=
  ∀ edges,
    SevenHighT0CubeRelationCore 1 (orderFortyNineBitAdj edges) →
    ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf 1).Sat assignment

theorem sevenHighT0CubeOneCnfSound_of_core
    (hsound : SevenHighT0CubeCoreCnfSound) :
    SevenHighT0CubeOneCnfSound := by
  intro edges h
  exact hsound 1 edges h

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

/-- Final reduced bridge: cube zero is discharged structurally, so the only
external certificate and encoding theorem required are for cube one. -/
theorem sevenHighT0_excluded_of_cubeOne_lratCheck
    (hsound : SevenHighT0CubeOneCnfSound)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof
      (orderFortyNineGeneratedH7T0CubeSatCnf 1)) :
    SevenHighT0CoreExcluded := by
  intro edges hedges
  obtain ⟨cube, normalizedEdges, hnormalized⟩ :=
    sevenHighT0_exists_normalized_relationCore_zero_or_one edges hedges
  fin_cases cube
  · exact sevenHighT0_relationCore_zero_false
      (orderFortyNineBitAdj normalizedEdges)
      (orderFortyNineBitAdj_comm normalizedEdges) hnormalized
  · obtain ⟨assignment, hsat⟩ := hsound normalizedEdges hnormalized
    have hunsat := LRAT.check_sound proof
      (orderFortyNineGeneratedH7T0CubeSatCnf 1) hcheck
    have hfalse := hunsat assignment
    rw [hsat] at hfalse
    contradiction

theorem sevenHighT0CoreExcluded_to_canonical
    (h : SevenHighT0CoreExcluded) :
    SevenHighCanonicalRepresentativeExcluded 0 0 := by
  intro edges hedges
  apply h edges
  simpa [sevenHighT0Masks] using hedges

/-- Aggregate-facing one-certificate endpoint. -/
theorem sevenHighT0_canonicalExcluded_of_cubeOne_lratCheck
    (hsound : SevenHighT0CubeOneCnfSound)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof
      (orderFortyNineGeneratedH7T0CubeSatCnf 1)) :
    SevenHighCanonicalRepresentativeExcluded 0 0 :=
  sevenHighT0CoreExcluded_to_canonical
    (sevenHighT0_excluded_of_cubeOne_lratCheck hsound proof hcheck)

/-- Aggregate-facing endpoint when encoding soundness is available uniformly
for the lightweight relation interface. -/
theorem sevenHighT0_canonicalExcluded_of_coreSound_cubeOne_lratCheck
    (hsound : SevenHighT0CubeCoreCnfSound)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof
      (orderFortyNineGeneratedH7T0CubeSatCnf 1)) :
    SevenHighCanonicalRepresentativeExcluded 0 0 :=
  sevenHighT0_canonicalExcluded_of_cubeOne_lratCheck
    (sevenHighT0CubeOneCnfSound_of_core hsound) proof hcheck

end Erdos85
