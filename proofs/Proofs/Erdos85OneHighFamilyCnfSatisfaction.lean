import Proofs.Erdos85OneHighFamilyCnfGenerator
import Proofs.Erdos85DimacsSatBridge

/-!
# Satisfaction adapter for the one-high family CNF

The generated DIMACS valuation has two layers.  Named `IDPool` atoms receive
their graph-semantic values here; sequential-counter auxiliaries are layered
above it by `seqCounterEqualsVal`.
-/

namespace Erdos85

def oneHighFamilyLookupId (id : Nat) :
    List (OneHighFamilyAtom × Nat) → Option OneHighFamilyAtom
  | [] => none
  | entry :: rest =>
      if entry.2 = id then some entry.1 else oneHighFamilyLookupId id rest

theorem oneHighFamilyLookupId_of_mem
    {atom : OneHighFamilyAtom} {id : Nat}
    {ids : List (OneHighFamilyAtom × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (atom, id) ∈ ids) :
    oneHighFamilyLookupId id ids = some atom := by
  induction ids with
  | nil => simp at hmem
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnodup
      rcases hnodup with ⟨hidFresh, hrest⟩
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [oneHighFamilyLookupId]
      · have hne : entry.2 ≠ id := by
          intro heq
          apply hidFresh
          exact List.mem_map.mpr ⟨(atom, id), hmem, by simpa [heq]⟩
        simp [oneHighFamilyLookupId, hne, ih hrest hmem]

noncomputable def oneHighFamilyAtomValue (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] : OneHighFamilyAtom → Bool
  | .edge i j =>
      if hi : i < 40 then if hj : j < 40 then
        decide (R.Adj ⟨i, hi⟩ ⟨j, hj⟩) else false else false
  | .miss w b =>
      if hw : w < 40 then if hb : b < 8 then
        @decide (oneHighFamilyMissesBlock R ⟨w, hw⟩ ⟨b, hb⟩)
          (Classical.propDecidable _)
      else false else false
  | .midpoint x w z =>
      if hx : x < 40 then if hw : w < 40 then if hz : z < 40 then
        @decide (oneHighFamilyTAtom R ⟨x, hx⟩ ⟨w, hw⟩ ⟨z, hz⟩)
          (Classical.propDecidable _)
      else false else false else false
  | .common x z =>
      if hx : x < 40 then if hz : z < 40 then
        decide ((R.neighborFinset ⟨x, hx⟩ ∩
          R.neighborFinset ⟨z, hz⟩).card = 1)
      else false else false

noncomputable def oneHighFamilyNamedVal (R : SimpleGraph (Fin 40))
    [DecidableRel R.Adj] (ids : List (OneHighFamilyAtom × Nat)) :
    DimacsValuation := fun id =>
  match oneHighFamilyLookupId id ids with
  | some atom => oneHighFamilyAtomValue R atom
  | none => false

theorem oneHighFamilyNamedVal_of_mem
    (R : SimpleGraph (Fin 40)) [DecidableRel R.Adj]
    {atom : OneHighFamilyAtom} {id : Nat}
    {ids : List (OneHighFamilyAtom × Nat)}
    (hnodup : (ids.map Prod.snd).Nodup)
    (hmem : (atom, id) ∈ ids) :
    oneHighFamilyNamedVal R ids id = oneHighFamilyAtomValue R atom := by
  rw [oneHighFamilyNamedVal, oneHighFamilyLookupId_of_mem hnodup hmem]

end Erdos85
