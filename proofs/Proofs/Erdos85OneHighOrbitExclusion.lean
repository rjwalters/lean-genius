import Proofs.Erdos85OneHighOrbitCnf
import Proofs.Erdos85OrderFortyNineStrataCapstone

/-!
# Certificate-facing orbit cover for the one-high stratum

This is the terminal used by the per-table fleet route.  It keeps coverage
and UNSAT evidence separate: a finite list must cover every graph-induced
miss table, and each listed table must carry a checked LRAT refutation.
-/

namespace Erdos85

open Std.Tactic.BVDecide

structure OneHighTableCheckedUnsat
    (a : Nat) (table : OneHighMissTable) : Prop where
  nonzero : ∀ clause ∈ (oneHighFamilyTableClauses a table).clauses,
    DimacsClauseNonzero clause
  unsat : ∀ assignment : Nat → Bool,
    ¬(oneHighFamilyTableSatCnf a table).Sat assignment

theorem oneHighTableCheckedUnsat_of_lrat
    {a : Nat} {table : OneHighMissTable}
    (hnz : ∀ clause ∈ (oneHighFamilyTableClauses a table).clauses,
      DimacsClauseNonzero clause)
    (proof : Array LRAT.IntAction)
    (hcheck : LRAT.check proof (oneHighFamilyTableSatCnf a table)) :
    OneHighTableCheckedUnsat a table where
  nonzero := hnz
  unsat := by
    intro assignment hsat
    rw [Std.Sat.CNF.sat_def] at hsat
    have hu := LRAT.check_sound proof (oneHighFamilyTableSatCnf a table)
      hcheck assignment
    rw [hsat] at hu
    contradiction

/-- A finite table list covers a family when every semantic family graph has
its induced miss table equal to a listed entry.  The forthcoming enumerator
verification and orbit-witness table discharge exactly this predicate. -/
def OneHighFamilyTableCover (a : Nat) (tables : List OneHighMissTable) : Prop :=
  ∀ (R : SimpleGraph (Fin 40)) (_ : DecidableRel R.Adj),
    OneHighPureFamilyCnfConstraints a R →
      ∃ table ∈ tables, oneHighFamilyGraphTable R a = table

theorem oneHighPureFamilyExcluded_of_tableCover
    {a : Nat} {tables : List OneHighMissTable}
    (hcover : OneHighFamilyTableCover a tables)
    (hchecked : ∀ table ∈ tables, OneHighTableCheckedUnsat a table) :
    OneHighPureFamilyExcluded a := by
  intro R _ hc
  rcases hcover R inferInstance hc with ⟨table, hmem, htable⟩
  have hcert := hchecked table hmem
  have hnz : ∀ clause ∈ (oneHighFamilyTableClauses a
      (oneHighFamilyGraphTable R a)).clauses,
      DimacsClauseNonzero clause := by
    simpa [htable] using hcert.nonzero
  rcases oneHighFamilyTableSatCnf_sat_of_constraints R a hc hnz with
    ⟨assignment, hsat⟩
  apply hcert.unsat assignment
  simpa [htable] using hsat

/-- Five independently covered and certificate-closed profile lists exclude
the complete one-high order-49 stratum. -/
theorem orderFortyNineStratumExcluded_one_of_tableCovers
    {tables0 tables1 tables2 tables3 tables4 : List OneHighMissTable}
    (hcover0 : OneHighFamilyTableCover 0 tables0)
    (hcover1 : OneHighFamilyTableCover 1 tables1)
    (hcover2 : OneHighFamilyTableCover 2 tables2)
    (hcover3 : OneHighFamilyTableCover 3 tables3)
    (hcover4 : OneHighFamilyTableCover 4 tables4)
    (hchecked0 : ∀ table ∈ tables0, OneHighTableCheckedUnsat 0 table)
    (hchecked1 : ∀ table ∈ tables1, OneHighTableCheckedUnsat 1 table)
    (hchecked2 : ∀ table ∈ tables2, OneHighTableCheckedUnsat 2 table)
    (hchecked3 : ∀ table ∈ tables3, OneHighTableCheckedUnsat 3 table)
    (hchecked4 : ∀ table ∈ tables4, OneHighTableCheckedUnsat 4 table) :
    OrderFortyNineStratumExcluded 1 := by
  apply orderFortyNineStratumExcluded_one_of_pureFamilies
  · exact oneHighPureFamilyExcluded_of_tableCover hcover0 hchecked0
  · exact oneHighPureFamilyExcluded_of_tableCover hcover1 hchecked1
  · exact oneHighPureFamilyExcluded_of_tableCover hcover2 hchecked2
  · exact oneHighPureFamilyExcluded_of_tableCover hcover3 hchecked3
  · exact oneHighPureFamilyExcluded_of_tableCover hcover4 hchecked4

end Erdos85
