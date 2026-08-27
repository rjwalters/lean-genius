import Proofs.Erdos85CnfCubeCover
import Proofs.Erdos85OrderFortyNineThreeHighScoutCnfSemantics

/-!
# Semantic consumer for individual three-high scout cubes

This bridge lets graph-level arguments use a checked positive two-literal cube
without assembling a syntactically exhaustive DIMACS grid.  It is the proof
interface needed by orbit reductions: relabel the graph semantically, rebuild
the standard scout valuation, and contradict the representative cube.
-/

namespace Erdos85

open Std Sat

theorem false_of_orderFortyNine_generated_h3_scout_cube_lrat
    {masks : Array Nat} {geometry : Array DimacsClause}
    {edges : BitVec 1176} {left right : Nat}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded (3 : Fin 50) masks)
    (hgeometryNonzero : ∀ clause ∈ geometry, DimacsClauseNonzero clause)
    (hgeometryBounded : dimacsFormulaBounded 1176 geometry)
    (hgeometrySat : dimacsFormulaSatisfied
      (orderFortyNineDimacsEdgeVal edges) geometry)
    (hleftBound : left < 1176) (hrightBound : right < 1176)
    (hleft : orderFortyNineDimacsEdgeVal edges (left + 1) = true)
    (hright : orderFortyNineDimacsEdgeVal edges (right + 1) = true)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (cnfWithUnits (orderFortyNineGeneratedThreeHighScoutCnf masks geometry)
        (positiveTwoCube left right))) : False := by
  obtain ⟨val, hsegments, hagree⟩ :=
    orderFortyNineVariableCnfSegments_satisfied (by omega) hc hexcluded
  have hgeometrySat' : dimacsFormulaSatisfied val geometry :=
    dimacsFormulaSatisfied_of_bounded_agree hgeometrySat hgeometryBounded
      (fun id hid => (hagree id hid).symm)
  have hbase := sat_of_orderFortyNineThreeHighScoutSegments hsegments
    hgeometrySat'
    (orderFortyNineGeneratedThreeHighScoutCnf_covered masks geometry
      hgeometryNonzero)
  have hcube :
      (cnfWithUnits (orderFortyNineGeneratedThreeHighScoutCnf masks geometry)
        (positiveTwoCube left right)).Sat (satAssignmentOfDimacs val) := by
    apply (sat_cnfWithUnits_iff _ _ _).2
    refine ⟨hbase, ?_⟩
    intro i hi
    have hi2 : i < 2 := by simpa [positiveTwoCube] using hi
    interval_cases i
    · simpa [positiveTwoCube, satAssignmentOfDimacs,
        hagree (left + 1) (by omega)] using hleft
    · simpa [positiveTwoCube, satAssignmentOfDimacs,
        hagree (right + 1) (by omega)] using hright
  have hunsat := Std.Tactic.BVDecide.LRAT.check_sound proof _ hcheck
  rw [CNF.unsat_def] at hunsat
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [CNF.sat_def] at hcube
  rw [hcube] at hfalse
  contradiction

end Erdos85
