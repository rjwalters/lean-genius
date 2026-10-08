import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalHsbSound

/-! # Cube-and-conquer over `hsb` leaves

`cube ∧ hsb<depth>` is split along the leaves of the stabilizer-chain
recursion (exact rows of the first `depth` empty vertices).  Per leaf, an
external checker certifies UNSAT of `cube ∧ hsb ∧ (positive row units)`; one
more certificate (the *cover* CNF: `cube ∧ hsb ∧` one blocking clause per
leaf) shows that the leaves exhaust the models.  Both kinds of certificate
are hypotheses here, as for the other strata; the composition is proved for
an arbitrary list of blocking clauses, so nothing about the leaf enumeration
is trusted beyond the checked cover CNF.
-/

namespace Erdos85

open Std Sat

/-- The assumption cube blocked by a clause: one unit per negated literal. -/
def cnfClauseNegUnits (c : CNF.Clause Nat) : CNF Nat :=
  cnfUnitClauses (c.map fun l => (l.1, !l.2)).toArray

/-- The CNF of a list of clauses. -/
def cnfOfClauseList (cs : List (CNF.Clause Nat)) : CNF Nat := ⟨cs.toArray⟩

private theorem beq_not_of_beq_false :
    ∀ b n : Bool, (b == n) = false → (b == !n) = true := by
  decide

/-- If `formula` is UNSAT together with the negation of each blocking clause,
and UNSAT together with all blocking clauses, then it is UNSAT. -/
theorem cnf_unsat_of_blocking_clauses
    (formula : CNF Nat) (blocking : List (CNF.Clause Nat))
    (hleaf : ∀ c ∈ blocking, (formula ++ cnfClauseNegUnits c).Unsat)
    (hcover : (formula ++ cnfOfClauseList blocking).Unsat) :
    formula.Unsat := by
  apply cnf_unsat_of_case_split formula (cnfOfClauseList blocking)
    (blocking.map cnfClauseNegUnits)
  · intro c hc
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    exact hleaf b hb
  · exact hcover
  · intro assignment
    by_cases hcov : CNF.eval assignment (cnfOfClauseList blocking) = true
    · exact Or.inl hcov
    · right
      have hex : ∃ c ∈ blocking, CNF.Clause.eval assignment c = false := by
        by_contra hno
        apply hcov
        unfold CNF.eval cnfOfClauseList
        show blocking.toArray.all _ = true
        rw [List.all_toArray, List.all_eq_true]
        intro c hc
        by_contra hne
        exact hno ⟨c, hc, Bool.eq_false_iff.mpr hne⟩
      obtain ⟨c, hc, hfalse⟩ := hex
      refine ⟨cnfClauseNegUnits c, List.mem_map.mpr ⟨c, hc, rfl⟩, ?_⟩
      unfold cnfClauseNegUnits
      rw [eval_cnfUnitClauses, List.all_toArray, List.all_map,
        List.all_eq_true]
      intro l hl
      obtain ⟨i, n⟩ := l
      show (assignment i == !n) = true
      apply beq_not_of_beq_false
      apply Bool.eq_false_iff.mpr
      intro htrue
      have hc_true : CNF.Clause.eval assignment c = true := by
        unfold CNF.Clause.eval
        rw [List.any_eq_true]
        exact ⟨(i, n), hl, htrue⟩
      rw [hfalse] at hc_true
      exact Bool.false_ne_true hc_true

open SevenHighT0Hsb

/-- The strengthened cube `cube ∧ hsb<depth>`. -/
def orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf
    (depth edgeCount typeIndex : Nat) : CNF Nat :=
  orderFortyNineSevenHighT0CanonicalEmptyCubeExtraSatCnf edgeCount typeIndex
    (SevenHighT0Hsb.cnf depth
      (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex))

/-- Certificate-facing proposition for one leaf: `cube ∧ hsb ∧` the positive
units of the leaf's rows (`rows[j]` = outside neighbours of empty `7 + j`). -/
def SevenHighT0CanonicalHsbLeafChecked
    (depth edgeCount typeIndex : Nat) (rows : List (List Nat)) : Prop :=
  (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf depth edgeCount typeIndex ++
    cnfClauseNegUnits (SevenHighT0Hsb.clause rows)).Unsat

/-- Certificate-facing proposition for the cover CNF of a leaf list:
`cube ∧ hsb ∧` one blocking clause per leaf. -/
def SevenHighT0CanonicalHsbCoverChecked
    (depth edgeCount typeIndex : Nat) (leafRows : List (List (List Nat))) :
    Prop :=
  (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf depth edgeCount typeIndex ++
    cnfOfClauseList (leafRows.map SevenHighT0Hsb.clause)).Unsat

/-- Checked leaves plus the checked cover give UNSAT of `cube ∧ hsb`. -/
theorem orderFortyNineSevenHighT0CanonicalHsbCube_unsat_of_leaves
    (depth edgeCount typeIndex : Nat) (leafRows : List (List (List Nat)))
    (hleaf : ∀ rows ∈ leafRows,
      SevenHighT0CanonicalHsbLeafChecked depth edgeCount typeIndex rows)
    (hcover : SevenHighT0CanonicalHsbCoverChecked
      depth edgeCount typeIndex leafRows) :
    (orderFortyNineSevenHighT0CanonicalHsbCubeSatCnf
      depth edgeCount typeIndex).Unsat := by
  apply cnf_unsat_of_blocking_clauses _
    (leafRows.map SevenHighT0Hsb.clause) _ hcover
  intro c hc
  obtain ⟨rows, hrows, rfl⟩ := List.mem_map.mp hc
  exact hleaf rows hrows

/-- Checked leaves plus the checked cover give the semantic exclusion of the
cube.  `leafRows` is arbitrary; the intended list is
`SevenHighT0Hsb.leaves depth mask`. -/
theorem sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbLeaves
    (depth edgeCount typeIndex : Nat) (leafRows : List (List (List Nat)))
    (hleaf : ∀ rows ∈ leafRows,
      SevenHighT0CanonicalHsbLeafChecked depth edgeCount typeIndex rows)
    (hcover : SevenHighT0CanonicalHsbCoverChecked
      depth edgeCount typeIndex leafRows) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex :=
  sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbUnsat
    depth edgeCount typeIndex
    (orderFortyNineSevenHighT0CanonicalHsbCube_unsat_of_leaves
      depth edgeCount typeIndex leafRows hleaf hcover)

/-- Complete external evidence for one cube along the generated leaves of
`hsb<depth>`: one checked cover CNF and one checked CNF per leaf. -/
structure SevenHighT0CanonicalHsbEvidence
    (depth edgeCount typeIndex : Nat) : Prop where
  cover : SevenHighT0CanonicalHsbCoverChecked depth edgeCount typeIndex
    (SevenHighT0Hsb.leaves depth
      (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex))
  leaf : ∀ rows ∈ SevenHighT0Hsb.leaves depth
      (sevenHighT0CanonicalEmptyRepresentativeMask edgeCount typeIndex),
    SevenHighT0CanonicalHsbLeafChecked depth edgeCount typeIndex rows

theorem SevenHighT0CanonicalHsbEvidence.semanticExclusion
    {depth edgeCount typeIndex : Nat}
    (h : SevenHighT0CanonicalHsbEvidence depth edgeCount typeIndex) :
    SevenHighT0CanonicalEmptyCubeSemanticExclusion edgeCount typeIndex :=
  sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbLeaves
    depth edgeCount typeIndex _ h.leaf h.cover

/-- The cover CNF's extra clauses are the generator's `coverClauses`. -/
theorem sevenHighT0CanonicalHsbCover_clauses (depth mask : Nat) :
    (cnfOfClauseList ((SevenHighT0Hsb.leaves depth mask).map
      SevenHighT0Hsb.clause)).clauses =
      (SevenHighT0Hsb.coverClauses depth mask).toArray := rfl

end Erdos85

#print axioms Erdos85.cnf_unsat_of_blocking_clauses
#print axioms Erdos85.sevenHighT0CanonicalEmptyCubeSemanticExclusion_of_hsbLeaves
#print axioms Erdos85.SevenHighT0CanonicalHsbEvidence.semanticExclusion
