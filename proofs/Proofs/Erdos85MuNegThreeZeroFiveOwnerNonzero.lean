import Proofs.Erdos85MuNegThreeZeroFiveFiniteTerminal
import Proofs.Erdos85MuNegOneOneFourOwnerNonzero

/-! # Structural nonzero-literal proof for the h305 owner CNFs -/

namespace Erdos85

open Std Sat

private theorem mem_lit_of_mem_exactlyTwo {lits clause : List Int} {lit : Int}
    (hc : clause ∈ muNegOneExactlyTwo lits) (hl : lit ∈ clause) :
    lit ∈ lits ∨ -lit ∈ lits := by
  simp only [muNegOneExactlyTwo, List.mem_append, List.mem_map,
    List.mem_flatMap, List.mem_filter, List.mem_range] at hc
  rcases hc with ⟨x, hx, rfl⟩ | ⟨i, hi, j, ⟨hj, hij⟩, k, ⟨hk, hjk⟩, rfl⟩
  · exact Or.inl (List.mem_of_mem_filter hl)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · right
      simp only [neg_neg]
      rw [getElem!_pos lits i hi]
      exact List.getElem_mem _
    · right
      simp only [neg_neg]
      rw [getElem!_pos lits j hj]
      exact List.getElem_mem _
    · right
      simp only [neg_neg]
      rw [getElem!_pos lits k hk]
      exact List.getElem_mem _

private theorem mem_lit_of_mem_exactlyThree {lits clause : List Int} {lit : Int}
    (hc : clause ∈ muNegThreeExactlyThree lits) (hl : lit ∈ clause) :
    lit ∈ lits ∨ -lit ∈ lits := by
  simp only [muNegThreeExactlyThree, List.mem_append, List.mem_flatMap,
    List.mem_filter, List.mem_range, List.mem_map, List.mem_singleton] at hc
  rcases hc with ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ | rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · left
      rw [getElem!_pos lits i hi]
      exact List.getElem_mem _
    · left
      rw [getElem!_pos lits j hj]
      exact List.getElem_mem _
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hl
    exact Or.inr (by simpa using hx)

private theorem dvar_map_nonzero (js : List Nat) (f g : Nat → Nat) :
    ∀ lit ∈ (js.map fun j => Int.ofNat (muNegOneDVar (f j) (g j))),
      lit ≠ 0 := by
  intro lit hlit
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hlit
  apply Int.ofNat_ne_zero.mpr
  unfold muNegOneDVar
  omega

private theorem crossRow_nonzero (sigma : Bool) :
    ∀ clause ∈ muNegThreeZeroFiveCrossRowClauses sigma,
      DimacsClauseNonzero clause := by
  intro clause hc lit hlit
  simp only [muNegThreeZeroFiveCrossRowClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hc
  obtain ⟨i, hi, hc | hc⟩ := hc
  · rcases mem_lit_of_mem_exactlyTwo hc hlit with h | h
    · exact dvar_map_nonzero _ (fun _ => i) id lit h
    · intro hz
      exact dvar_map_nonzero _ (fun _ => i) id (-lit) h (by omega)
  · rcases mem_lit_of_mem_exactlyThree hc hlit with h | h
    · exact dvar_map_nonzero _ (fun _ => i) id lit h
    · intro hz
      exact dvar_map_nonzero _ (fun _ => i) id (-lit) h (by omega)

private theorem crossCol_nonzero (sigma : Bool) :
    ∀ clause ∈ muNegThreeZeroFiveCrossColClauses sigma,
      DimacsClauseNonzero clause := by
  intro clause hc lit hlit
  simp only [muNegThreeZeroFiveCrossColClauses, List.mem_flatMap,
    List.mem_range, List.mem_append] at hc
  obtain ⟨j, hj, hc | hc⟩ := hc
  · rcases mem_lit_of_mem_exactlyTwo hc hlit with h | h
    · exact dvar_map_nonzero _ id (fun _ => j) lit h
    · intro hz
      exact dvar_map_nonzero _ id (fun _ => j) (-lit) h (by omega)
  · rcases mem_lit_of_mem_exactlyThree hc hlit with h | h
    · exact dvar_map_nonzero _ id (fun _ => j) lit h
    · intro hz
      exact dvar_map_nonzero _ id (fun _ => j) (-lit) h (by omega)

theorem muNegThreeZeroFiveOwnerDimacsClauses_nonzero_of_mem
    (uTri vTri sigma : Bool)
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true)) :
    ∀ clause ∈ muNegThreeZeroFiveOwnerDimacsClauses uTri vTri sigma,
      DimacsClauseNonzero clause := by
  intro clause hc
  simp only [muNegThreeZeroFiveOwnerDimacsClauses, List.mem_toArray,
    List.mem_append] at hc
  rcases hc with ((((hrow | hcol) | hintertwine) | hactivity) | hservice) | hc4
  · exact crossRow_nonzero sigma clause hrow
  · exact crossCol_nonzero sigma clause hcol
  · apply muNegOneOneFourOwnerDimacsClauses_nonzero_of_mem
      uTri vTri sigma hcanon clause
    simp only [muNegOneOneFourOwnerDimacsClauses, List.mem_toArray,
      List.mem_append]
    exact Or.inl (Or.inl (Or.inl (Or.inr hintertwine)))
  · apply muNegOneOneFourOwnerDimacsClauses_nonzero_of_mem
      uTri vTri sigma hcanon clause
    simp only [muNegOneOneFourOwnerDimacsClauses, List.mem_toArray,
      List.mem_append]
    exact Or.inl (Or.inl (Or.inr hactivity))
  · apply muNegOneOneFourOwnerDimacsClauses_nonzero_of_mem
      uTri vTri sigma hcanon clause
    simp only [muNegOneOneFourOwnerDimacsClauses, List.mem_toArray,
      List.mem_append]
    exact Or.inl (Or.inr hservice)
  · apply muNegOneOneFourOwnerDimacsClauses_nonzero_of_mem
      uTri vTri sigma hcanon clause
    simp only [muNegOneOneFourOwnerDimacsClauses, List.mem_toArray,
      List.mem_append]
    exact Or.inr hc4

theorem muNegThreeZeroFiveOwnerConstraintSemantics_false'
    {uTri vTri sigma : Bool} {val : DimacsValuation}
    (hcanon : (uTri = false ∧ vTri = false) ∨
      (uTri = false ∧ vTri = true) ∨ (uTri = true ∧ vTri = true))
    (hsem : MuNegThreeZeroFiveOwnerConstraintSemantics
      uTri vTri sigma val)
    (hcount : (if sigma then [val 1, val 3, val 5, val 7]
      else [val 2, val 4, val 6, val 8]).count true = 3) : False :=
  muNegThreeZeroFiveOwnerConstraintSemantics_false hcanon
    (muNegThreeZeroFiveOwnerDimacsClauses_nonzero_of_mem
      uTri vTri sigma hcanon) hsem hcount

end Erdos85

#print axioms Erdos85.muNegThreeZeroFiveOwnerDimacsClauses_nonzero_of_mem
#print axioms Erdos85.muNegThreeZeroFiveOwnerConstraintSemantics_false'
