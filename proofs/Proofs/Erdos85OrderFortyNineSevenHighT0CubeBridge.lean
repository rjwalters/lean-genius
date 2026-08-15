import Proofs.Erdos85OrderFortyNineSevenHighT0CubeCnf
import Proofs.Erdos85OrderFortyNineSevenHighCertificateBridge

/-!
# Certificate interface for the seven `h = 7, t = 0` cubes

The semantic-cover proposition isolates the remaining graph normalization:
every Boolean realization of the canonical empty triple system must satisfy
one of the seven symmetry-broken cube CNFs.  Checked LRAT refutations of all
seven cubes then discharge the canonical representative and hence, through
the aggregate certificate module, the complete seven-high stratum.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- Relation-level statement enforced by the symmetry-broken cube generator.
It deliberately mirrors the generator segments, before auxiliary-variable
reification is introduced. -/
def SevenHighT0CubeRelationConstraints (cube : Nat)
    (adj : Fin 49 → Fin 49 → Bool) : Prop :=
  cube < 7 ∧
  (∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j → adj i j = false) ∧
  (∀ x : Fin 49, 7 ≤ x.val →
    adj 0 x = decide (x.val < 15)) ∧
  (∀ a b : Fin 49, 7 ≤ a.val → a.val < 15 →
    7 ≤ b.val → b.val < 15 → a ≠ b →
    adj a b = sevenHighT0CubeMatching0 a.val b.val) ∧
  (∀ x : Fin 49, 7 ≤ x.val →
    adj 1 x = decide (x.val = 7 ∨ (15 ≤ x.val ∧ x.val < 22))) ∧
  (∀ a b : Fin 49,
    (a.val = 7 ∨ (15 ≤ a.val ∧ a.val < 22)) →
    (b.val = 7 ∨ (15 ≤ b.val ∧ b.val < 22)) → a ≠ b →
    adj a b = sevenHighT0CubeMatching1 a.val b.val) ∧
  (∀ i j : Fin 49, i.val < 7 → j.val < 7 → i ≠ j →
    ∃ w : Fin 49, 7 ≤ w.val ∧ adj i w = true ∧ adj j w = true) ∧
  (∀ i j : Fin 49, i ≠ j →
    (Finset.univ.filter fun w => adj i w && adj j w).card ≤ 1) ∧
  (∀ i : Fin 49,
    (Finset.univ.filter fun j => adj i j).card =
      if i.val < 7 then 8 else 7) ∧
  (∀ y : Fin 49, 7 ≤ y.val → ∀ high : Fin 2,
    ∃ x : Fin 49,
      x.val ∈ sevenHighT0CubePartitionNeighbors high.val ∧
      x ≠ y ∧ adj y x = true) ∧
  (∀ index : Fin 7,
    adj 9 ⟨index.val + 15, by omega⟩ = decide (index.val = cube))

/-- Pure graph/Boolean normalization obligation: a canonical t=0 realization
can be relabeled into one of the seven relation-level cubes. -/
def SevenHighT0CubeNormalizationCover : Prop :=
  ∀ edges : BitVec 1176,
    orderFortyNineBooleanConstraints 7
      (OrderFortyNineSevenHighCensus.representativeMasks 0 0) edges →
    ∃ cube, ∃ normalizedEdges : BitVec 1176,
      SevenHighT0CubeRelationConstraints cube
        (orderFortyNineBitAdj normalizedEdges)

/-- Encoding obligation: every relation-level cube extends to values of the
named common-neighbor and sequential-counter auxiliaries satisfying the exact
Lean-generated CNF. -/
def SevenHighT0CubeCnfSound : Prop :=
  ∀ cube edges,
    SevenHighT0CubeRelationConstraints cube (orderFortyNineBitAdj edges) →
    ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf cube).Sat assignment

def SevenHighT0CubeSemanticCover : Prop :=
  ∀ edges : BitVec 1176,
    orderFortyNineBooleanConstraints 7
      (OrderFortyNineSevenHighCensus.representativeMasks 0 0) edges →
    ∃ cube, cube < 7 ∧ ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf cube).Sat assignment

theorem sevenHighT0CubeSemanticCover_of_normalization_of_cnfSound
    (hnormalize : SevenHighT0CubeNormalizationCover)
    (hsound : SevenHighT0CubeCnfSound) :
    SevenHighT0CubeSemanticCover := by
  intro edges hedges
  obtain ⟨cube, normalizedEdges, hnormalized⟩ := hnormalize edges hedges
  exact ⟨cube, hnormalized.1, hsound cube normalizedEdges hnormalized⟩

theorem sevenHighT0_excluded_of_cube_lratChecks
    (hcover : SevenHighT0CubeSemanticCover)
    (hchecks : ∀ cube, cube < 7 →
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof (orderFortyNineGeneratedH7T0CubeSatCnf cube)) :
    SevenHighCanonicalRepresentativeExcluded 0 0 := by
  intro edges hedges
  obtain ⟨cube, hcube, assignment, hsat⟩ := hcover edges hedges
  obtain ⟨proof, hcheck⟩ := hchecks cube hcube
  have hunsat := LRAT.check_sound proof
    (orderFortyNineGeneratedH7T0CubeSatCnf cube) hcheck
  have hfalse := hunsat assignment
  rw [hsat] at hfalse
  contradiction

end Erdos85
