import Proofs.Erdos85OrderFortyNineGraphPrefixNormalization

/-!
# Semantic interface for the order-49 witness rows

The generated tables are checked by Boolean functions.  This file extracts
ordinary propositions from those checks, beginning with the representative
lookup, the nine-point permutation list, and the setwise system equality.
-/

namespace Erdos85
namespace OrderFortyNineWitnessTable

theorem rowValid_spec
    (reps : Array OrderFortyNineH9System) (row : Row)
    (hvalid : rowValid reps row = true) :
    ∃ rep,
      reps[row.2.1]? = some rep ∧
      row.2.2.length = 9 ∧
      (∀ i < 9, i ∈ row.2.2) ∧
      systemSetEqB (row.1.map (applyPermTriple row.2.2))
        (h9SystemTriples rep) = true := by
  unfold rowValid at hvalid
  split at hvalid
  next rep heq =>
    refine ⟨rep, heq, ?_⟩
    rcases (by simpa [Bool.and_eq_true] using hvalid) with
      ⟨⟨hlen, hall⟩, hsys⟩
    exact ⟨hlen, hall, hsys⟩
  next heq => simp at hvalid

theorem rowValid_perm_length
    (reps : Array OrderFortyNineH9System) (row : Row)
    (hvalid : rowValid reps row = true) : row.2.2.length = 9 :=
  (rowValid_spec reps row hvalid).choose_spec.2.1

theorem rowValid_perm_contains
    (reps : Array OrderFortyNineH9System) (row : Row)
    (hvalid : rowValid reps row = true) {i : Nat} (hi : i < 9) :
    i ∈ row.2.2 := by
  exact (rowValid_spec reps row hvalid).choose_spec.2.2.1 i hi

theorem rowValid_perm_toFinset
    (reps : Array OrderFortyNineH9System) (row : Row)
    (hvalid : rowValid reps row = true) :
    row.2.2.toFinset = (Finset.range 9) := by
  have hsub : Finset.range 9 ⊆ row.2.2.toFinset := by
    intro i hi
    simp only [Finset.mem_range] at hi
    simpa using rowValid_perm_contains reps row hvalid hi
  have hcardLower : 9 ≤ row.2.2.toFinset.card := by
    simpa using Finset.card_le_card hsub
  have hcardUpper : row.2.2.toFinset.card ≤ 9 := by
    rw [← rowValid_perm_length reps row hvalid]
    exact List.toFinset_card_le (l := row.2.2)
  have hcards : row.2.2.toFinset.card ≤ (Finset.range 9).card := by
    simpa using hcardUpper
  exact (Finset.eq_of_subset_of_card_le hsub hcards).symm

theorem rowValid_perm_nodup
    (reps : Array OrderFortyNineH9System) (row : Row)
    (hvalid : rowValid reps row = true) : row.2.2.Nodup := by
  have hm : ((↑row.2.2 : Multiset Nat).toFinset).card =
      (↑row.2.2 : Multiset Nat).card := by
    change row.2.2.toFinset.card = row.2.2.length
    rw [rowValid_perm_toFinset reps row hvalid,
      rowValid_perm_length reps row hvalid]
    simp
  simpa using (Multiset.toFinset_card_eq_card_iff_nodup.mp hm)

/-- The witness list in a valid row is the value list of an actual
permutation of `Fin 9`. -/
theorem exists_rowPerm
    (reps : Array OrderFortyNineH9System) (row : Row)
    (hvalid : rowValid reps row = true) :
    ∃ σ : Equiv.Perm (Fin 9),
      ∀ i : Fin 9, (σ i).val = row.2.2.getD i.val 0 := by
  let f : Fin 9 → Fin 9 := fun i =>
    let hi : i.val < row.2.2.length := by
      rw [rowValid_perm_length reps row hvalid]
      exact i.isLt
    ⟨row.2.2[i.val], by
      have hmem : row.2.2[i.val] ∈ row.2.2 := List.getElem_mem hi
      have hrange : row.2.2[i.val] ∈ Finset.range 9 := by
        rw [← rowValid_perm_toFinset reps row hvalid]
        simpa using hmem
      simpa using hrange⟩
  have hf : Function.Injective f := by
    intro i j hij
    have hlen := rowValid_perm_length reps row hvalid
    let ii : Fin row.2.2.length := ⟨i.val, by simpa [hlen] using i.isLt⟩
    let jj : Fin row.2.2.length := ⟨j.val, by simpa [hlen] using j.isLt⟩
    have hvals : row.2.2[ii] = row.2.2[jj] := congrArg Fin.val hij
    have hidx : ii = jj :=
      (List.nodup_iff_injective_getElem.mp
        (rowValid_perm_nodup reps row hvalid)) hvals
    have hv : i.val = j.val :=
      congrArg (fun k : Fin row.2.2.length => k.val) hidx
    exact Fin.ext hv
  have hsurj : Function.Surjective f :=
    Finite.injective_iff_surjective.mp hf
  let σ : Equiv.Perm (Fin 9) := Equiv.ofBijective f ⟨hf, hsurj⟩
  refine ⟨σ, fun i => ?_⟩
  change (f i).val = row.2.2.getD i.val 0
  have hi : i.val < row.2.2.length := by
    rw [rowValid_perm_length reps row hvalid]
    exact i.isLt
  have hget : row.2.2.getD i.val 0 = row.2.2[i.val] :=
    List.getD_eq_getElem row.2.2 0 hi
  rw [hget]

/-- Propositional meaning of the Boolean equality test for triples. -/
theorem tripleSetEqB_eq_true_iff (S T : List Nat) :
    tripleSetEqB S T = true ↔
      S.length = T.length ∧ S.toFinset = T.toFinset := by
  constructor
  · intro h
    simp only [tripleSetEqB, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hlen, hST⟩, hTS⟩
    refine ⟨hlen, Finset.ext fun x => ?_⟩
    constructor
    · intro hx
      have hxS : x ∈ S := by simpa using hx
      have := List.all_eq_true.mp hST x hxS
      simpa using this
    · intro hx
      have hxT : x ∈ T := by simpa using hx
      have := List.all_eq_true.mp hTS x hxT
      simpa using this
  · rintro ⟨hlen, hset⟩
    simp only [tripleSetEqB, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨hlen, List.all_eq_true.mpr fun x hx => ?_⟩,
      List.all_eq_true.mpr fun x hx => ?_⟩
    · have : x ∈ T.toFinset := by
        rw [← hset]
        simpa using hx
      simpa using this
    · have : x ∈ S.toFinset := by
        rw [hset]
        simpa using hx
      simpa using this

/-- Propositional meaning of the Boolean equality test for systems of
triples.  The systems are compared as collections, while each triple is
compared by length and underlying set. -/
theorem systemSetEqB_eq_true_iff (A B : List (List Nat)) :
    systemSetEqB A B = true ↔
      A.length = B.length ∧
      (∀ S ∈ A, ∃ T ∈ B, S.length = T.length ∧ S.toFinset = T.toFinset) ∧
      (∀ T ∈ B, ∃ S ∈ A, S.length = T.length ∧ S.toFinset = T.toFinset) := by
  constructor
  · intro h
    simp only [systemSetEqB, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hlen, hAB⟩, hBA⟩
    refine ⟨hlen, ?_, ?_⟩
    · intro S hS
      have hAny := List.all_eq_true.mp hAB S hS
      obtain ⟨T, hT, hEq⟩ := List.any_eq_true.mp hAny
      exact ⟨T, hT, (tripleSetEqB_eq_true_iff S T).mp hEq⟩
    · intro T hT
      have hAny := List.all_eq_true.mp hBA T hT
      obtain ⟨S, hS, hEq⟩ := List.any_eq_true.mp hAny
      have hSem := (tripleSetEqB_eq_true_iff T S).mp hEq
      exact ⟨S, hS, hSem.1.symm, hSem.2.symm⟩
  · rintro ⟨hlen, hAB, hBA⟩
    simp only [systemSetEqB, Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨hlen, List.all_eq_true.mpr fun S hS => ?_⟩,
      List.all_eq_true.mpr fun T hT => ?_⟩
    · obtain ⟨T, hT, hEq⟩ := hAB S hS
      exact List.any_eq_true.mpr
        ⟨T, hT, (tripleSetEqB_eq_true_iff S T).mpr hEq⟩
    · obtain ⟨S, hS, hEq⟩ := hBA T hT
      exact List.any_eq_true.mpr
        ⟨S, hS, (tripleSetEqB_eq_true_iff T S).mpr
          ⟨hEq.1.symm, hEq.2.symm⟩⟩

/-- Complete semantic payload of a valid row: a selected representative, an
actual permutation of the nine labels agreeing with the stored value list,
and setwise equality of the permuted raw system with that representative. -/
theorem exists_rep_rowPerm_systemSpec
    (reps : Array OrderFortyNineH9System) (row : Row)
    (hvalid : rowValid reps row = true) :
    ∃ rep, ∃ σ : Equiv.Perm (Fin 9),
      reps[row.2.1]? = some rep ∧
      (∀ i : Fin 9, (σ i).val = row.2.2.getD i.val 0) ∧
      (row.1.map (applyPermTriple row.2.2)).length =
        (h9SystemTriples rep).length ∧
      (∀ S ∈ row.1.map (applyPermTriple row.2.2),
        ∃ T ∈ h9SystemTriples rep,
          S.length = T.length ∧ S.toFinset = T.toFinset) ∧
      (∀ T ∈ h9SystemTriples rep,
        ∃ S ∈ row.1.map (applyPermTriple row.2.2),
          S.length = T.length ∧ S.toFinset = T.toFinset) := by
  obtain ⟨rep, hrep, hlen, hall, hsys⟩ := rowValid_spec reps row hvalid
  obtain ⟨σ, hσ⟩ := exists_rowPerm reps row hvalid
  have hsem := (systemSetEqB_eq_true_iff _ _).mp hsys
  exact ⟨rep, σ, hrep, hσ, hsem.1, hsem.2.1, hsem.2.2⟩

end OrderFortyNineWitnessTable
end Erdos85
