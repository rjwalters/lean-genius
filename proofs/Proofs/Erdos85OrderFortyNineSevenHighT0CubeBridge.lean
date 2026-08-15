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

def SevenHighT0CubeSemanticCover : Prop :=
  ∀ edges : BitVec 1176,
    orderFortyNineBooleanConstraints 7
      (OrderFortyNineSevenHighCensus.representativeMasks 0 0) edges →
    ∃ cube, cube < 7 ∧ ∃ assignment : Nat → Bool,
      (orderFortyNineGeneratedH7T0CubeSatCnf cube).Sat assignment

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
