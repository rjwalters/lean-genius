import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyCubeExtraClauses

/-!
# Orbit-representative adapter for strengthened H7/T0 cube certificates

`SevenHighT0CanonicalExtraClausesSound` demands that *every* base valuation
agreeing with *every* completion graph of the cube satisfies the extra
clauses.  That covers clauses entailed by the graph semantics (capacity,
forbidden pairs) but neither symmetry-breaking clauses (true only for a
chosen orbit representative) nor clauses over fresh auxiliary variables
(true only for a suitable extension of the valuation).

The weaker obligation here is the exact one a strengthened UNSAT certificate
needs: every completion graph in the cube yields *some* model of
`cube ++ extra`.  The witness may be the valuation of a different graph in
the same symmetry orbit and may set auxiliary variables freely.
-/

namespace Erdos85

open Std Sat

/-- Every completion graph pinned to the cube's mask yields some model of the
strengthened cube CNF. -/
def SevenHighT0CanonicalExtraClausesOrbitSound
    (edgeCount typeIndex : Nat) (extra : CNF Nat) : Prop :=
  ∀ (H : SimpleGraph SevenHighT0CanonicalIndex) (_ : DecidableRel H.Adj),
    SevenHighT0CanonicalCompletionSemantics H →
      sevenHighT0CanonicalEmptySemanticMask H =
        sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex →
      ∃ assignment : Nat → Bool,
        (orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf
          edgeCount typeIndex extra).Sat assignment

/-- Orbit-sound extra clauses plus UNSAT of the strengthened cube give the
semantic exclusion of the cube. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_orbitExtraUnsat
    {edgeCount typeIndex : Nat} {extra : CNF Nat}
    (hsound : SevenHighT0CanonicalExtraClausesOrbitSound
      edgeCount typeIndex extra)
    (hunsat : (orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf
      edgeCount typeIndex extra).Unsat) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex := by
  intro H _ semantics hmask
  obtain ⟨assignment, hsat⟩ := hsound H inferInstance semantics hmask
  have h := hunsat assignment
  rw [CNF.sat_def] at hsat
  rw [hsat] at h
  simp at h

/-- Edge-only extra clauses: it suffices to exhibit, for every completion
graph of the cube, a (possibly relabelled) completion graph of the same cube
whose edge valuation satisfies them.  This is the entry point for
lex-leader / stabilizer-chain symmetry breaking. -/
theorem sevenHighT0CanonicalExtraClausesOrbitSound_of_edgeOnly_representative
    {edgeCount typeIndex : Nat} {extra : CNF Nat}
    (hedgeOnly : ∀ v, CNF.VarMem v extra → v < 861)
    (hrep : ∀ (H : SimpleGraph SevenHighT0CanonicalIndex)
      (_ : DecidableRel H.Adj),
      SevenHighT0CanonicalCompletionSemantics H →
        sevenHighT0CanonicalEmptySemanticMask H =
          sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex →
        ∃ (H' : SimpleGraph SevenHighT0CanonicalIndex)
          (_ : DecidableRel H'.Adj),
          SevenHighT0CanonicalCompletionSemantics H' ∧
          sevenHighT0CanonicalEmptySemanticMask H' =
            sevenHighT0CanonicalEmptyRepresentativeMask
              edgeCount typeIndex ∧
          extra.Sat
            (satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H'))) :
    SevenHighT0CanonicalExtraClausesOrbitSound edgeCount typeIndex extra := by
  intro H _ semantics hmask
  obtain ⟨H', _, semantics', hmask', hextra⟩ :=
    hrep H inferInstance semantics hmask
  obtain ⟨val, hbase, hagree⟩ := sevenHighT0CanonicalBaseSat H' semantics'
  have hcube := sevenHighT0CanonicalEmptyRepresentativeCube_sat
    H' val edgeCount typeIndex hbase hagree hmask'
  have hcongr := CNF.eval_congr (satAssignmentOfDimacs val)
    (satAssignmentOfDimacs (sevenHighT0CanonicalEdgeVal H')) extra
    (fun v hv => by
      unfold satAssignmentOfDimacs
      exact hagree (v + 1) (by have := hedgeOnly v hv; omega))
  refine ⟨satAssignmentOfDimacs val, ?_⟩
  rw [CNF.sat_def] at hcube hextra ⊢
  rw [orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf,
    CNF.eval_append, hcube, hcongr, hextra]
  rfl

/-- The strong (every-valuation) obligation implies the orbit obligation. -/
theorem sevenHighT0CanonicalExtraClausesOrbitSound_of_sound
    {edgeCount typeIndex : Nat} {extra : CNF Nat}
    (hsound : SevenHighT0CanonicalExtraClausesSound
      edgeCount typeIndex extra) :
    SevenHighT0CanonicalExtraClausesOrbitSound edgeCount typeIndex extra := by
  intro H _ semantics hmask
  obtain ⟨val, hbase, hagree⟩ := sevenHighT0CanonicalBaseSat H semantics
  have hcube := sevenHighT0CanonicalEmptyRepresentativeCube_sat
    H val edgeCount typeIndex hbase hagree hmask
  have hextra := hsound H inferInstance semantics hmask val hbase hagree
  refine ⟨satAssignmentOfDimacs val, ?_⟩
  rw [CNF.sat_def] at hcube hextra ⊢
  rw [orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf,
    CNF.eval_append, hcube, hextra]
  rfl

/-- Cube-and-conquer over assumption sets, entirely on the SAT side: if the
formula is UNSAT under each listed extension and also UNSAT together with the
remaining "none of the listed cases" clauses, it is UNSAT. -/
theorem cnf_unsat_of_case_split
    (formula cover : CNF Nat) (cases : List (CNF Nat))
    (hcases : ∀ c ∈ cases, (formula ++ c).Unsat)
    (hcover : (formula ++ cover).Unsat)
    (hsplit : ∀ assignment : Nat → Bool,
      cover.eval assignment = true ∨
        ∃ c ∈ cases, c.eval assignment = true) :
    formula.Unsat := by
  intro assignment
  by_contra hne
  have hformula : formula.eval assignment = true := by simpa using hne
  rcases hsplit assignment with hcov | ⟨c, hc, hceval⟩
  · have h := hcover assignment
    rw [CNF.eval_append, hformula, hcov] at h
    simp at h
  · have h := hcases c hc assignment
    rw [CNF.eval_append, hformula, hceval] at h
    simp at h

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_orbitExtraUnsat
#print axioms Erdos85.sevenHighT0CanonicalExtraClausesOrbitSound_of_edgeOnly_representative
#print axioms Erdos85.sevenHighT0CanonicalExtraClausesOrbitSound_of_sound
#print axioms Erdos85.cnf_unsat_of_case_split
