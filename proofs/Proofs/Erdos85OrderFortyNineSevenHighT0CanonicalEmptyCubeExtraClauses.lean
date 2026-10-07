import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeSemanticExclusion
import Proofs.Erdos85CnfBinarySplit

/-!
# Base cube CNF plus Lean-proven extra clauses

Adapter for strengthened H7/T0 cube certificates.  An external solver may
prove `cube ∧ extra` UNSAT faster than `cube` alone when `extra` encodes
facts already proved in Lean (capacity bounds, forbidden pairs, lex-leader
symmetry breaking, ...).  This is sound for the *semantic* exclusion of the
cube as long as every graph-derived model of the base CNF also satisfies
`extra`.

* `SevenHighT0CanonicalExtraClausesSound F i extra` is that obligation, stated
  for every base model agreeing with a canonical completion graph on the 861
  edge variables.
* `sevenHighT0CanonicalExtraClausesSound_of_edgeOnly` reduces it, for clauses
  mentioning only edge variables (zero-based ids `< 861`), to a pure graph
  statement about `satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H)`.
  Clauses using auxiliary variables (comparators, cardinality encodings) must
  prove the general obligation directly, extending the valuation as needed.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

/-- The cube CNF strengthened by additional clauses. -/
def orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf
    (edgeCount typeIndex : Nat) (extra : CNF Nat) : CNF Nat :=
  orderFortyNineSevenHighT0CanonicalEmptyCubeSatCnf edgeCount typeIndex ++
    extra

/-- Soundness of extra clauses for one cube: every DIMACS model of the base
CNF that agrees with a canonical completion graph (whose empty-sector mask is
the cube's representative) on the edge variables satisfies `extra`. -/
def SevenHighT0CanonicalExtraClausesSound
    (edgeCount typeIndex : Nat) (extra : CNF Nat) : Prop :=
  ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
    SevenHighT0CanonicalCompletionSemantics H →
      sevenHighT0CanonicalEmptySemanticMask H =
        sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex →
      ∀ val : DimacsValuation,
        orderFortyNineSevenHighT0CanonicalSatCnf.Sat
          (satAssignmentOfDimacs val) →
        (∀ id, id ≤ 861 → val id = sevenHighT0CanonicalEdgeVal H id) →
        extra.Sat (satAssignmentOfDimacs val)

/-- Sound extra clauses plus UNSAT of the strengthened cube give the semantic
exclusion of the cube. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraUnsat
    {edgeCount typeIndex : Nat} {extra : CNF Nat}
    (hsound : SevenHighT0CanonicalExtraClausesSound
      edgeCount typeIndex extra)
    (hunsat : (orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf
      edgeCount typeIndex extra).Unsat) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex := by
  intro H _ semantics hmask
  obtain ⟨val, hbase, hagree⟩ := sevenHighT0CanonicalBaseSat H semantics
  have hcube := sevenHighT0CanonicalEmptyRepresentativeCube_sat
    H val edgeCount typeIndex hbase hagree hmask
  have hextra := hsound H inferInstance semantics hmask val hbase hagree
  have h := hunsat (satAssignmentOfDimacs val)
  rw [orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf,
    CNF.eval_append] at h
  rw [CNF.sat_def] at hcube hextra
  rw [hcube, hextra] at h
  simp at h

/-- Checked LRAT evidence for the strengthened cube. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraLrat
    {edgeCount typeIndex : Nat} {extra : CNF Nat}
    (hsound : SevenHighT0CanonicalExtraClausesSound
      edgeCount typeIndex extra)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof
      (orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf
        edgeCount typeIndex extra)) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex :=
  sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraUnsat hsound
    (LRAT.check_sound proof _ hcheck)

/-- Cube-and-conquer binary-tree evidence for the strengthened cube. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraTree
    {edgeCount typeIndex : Nat} {extra : CNF Nat}
    (hsound : SevenHighT0CanonicalExtraClausesSound
      edgeCount typeIndex extra)
    (tree : CnfBinaryCheckedTree
      (orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf
        edgeCount typeIndex extra)) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex :=
  sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraUnsat hsound
    tree.unsat

/-- Edge-only extra clauses: soundness reduces to the graph assignment.
Zero-based SAT variable `v` is DIMACS id `v + 1`; edge ids are `1..861`. -/
theorem sevenHighT0CanonicalExtraClausesSound_of_edgeOnly
    {edgeCount typeIndex : Nat} {extra : CNF Nat}
    (hedgeOnly : ∀ v, CNF.VarMem v extra → v < 861)
    (hgraph : ∀ (H : SimpleGraph SevenHighT0CanonicalIndex)
      (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H →
        sevenHighT0CanonicalEmptySemanticMask H =
          sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex →
        extra.Sat
          (satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H))) :
    SevenHighT0CanonicalExtraClausesSound edgeCount typeIndex extra := by
  intro H _ semantics hmask val _ hagree
  have hcongr := CNF.eval_congr (satAssignmentOfDimacs val)
    (satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H)) extra
    (fun v hv => by
      unfold satAssignmentOfDimacs
      exact hagree (v + 1) (by have := hedgeOnly v hv; omega))
  rw [CNF.sat_def, hcongr]
  exact hgraph H inferInstance semantics hmask

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraUnsat
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraLrat
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_extraTree
#print axioms Erdos85.sevenHighT0CanonicalExtraClausesSound_of_edgeOnly
