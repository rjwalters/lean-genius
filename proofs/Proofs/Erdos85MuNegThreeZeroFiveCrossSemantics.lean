import Proofs.Erdos85MuNegThreeZeroFiveOwnerNonzero
import Proofs.Erdos85MuNegOneOneFourFiniteSemantics

/-! # Exact-three semantic transport for h305 cross blocks -/

namespace Erdos85

open Std Sat

set_option maxHeartbeats 0 in
theorem muNegThreeExactlyThreeSemantics_of_count_three
    {val : DimacsValuation} {lits : List Int}
    (hlen : lits.length = 4)
    (hpos : ∀ lit ∈ lits, 0 < lit)
    (hcount : (lits.countP fun lit => dimacsLitValue val lit) = 3) :
    MuNegThreeExactlyThreeSemantics val lits := by
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp hlen
  have ha : 0 < a := hpos a (by simp)
  have hb : 0 < b := hpos b (by simp)
  have hc : 0 < c := hpos c (by simp)
  have hd : 0 < d := hpos d (by simp)
  constructor
  intro clause hclause
  norm_num [muNegThreeExactlyThree] at hclause
  rcases hclause with hpairs | hneg
  · obtain ⟨i, hi, j, ⟨hj, hij⟩, rfl⟩ := hpairs
    interval_cases i <;> interval_cases j <;> norm_num at hij ⊢ <;>
      simp only [List.countP_cons, List.countP_nil] at hcount <;>
      simp only [dimacsClauseSatisfied, List.mem_cons, List.mem_singleton] <;>
      by_cases hva : dimacsLitValue val a = true <;>
      by_cases hvb : dimacsLitValue val b = true <;>
      by_cases hvc : dimacsLitValue val c = true <;>
      by_cases hvd : dimacsLitValue val d = true <;>
      simp_all [dimacsLitValue, ha, hb, hc, hd] <;> omega
  · subst clause
    simp only [List.countP_cons, List.countP_nil] at hcount
    simp only [dimacsClauseSatisfied, List.mem_cons, List.mem_singleton]
    by_cases hva : dimacsLitValue val a = true <;>
    by_cases hvb : dimacsLitValue val b = true <;>
    by_cases hvc : dimacsLitValue val c = true <;>
    by_cases hvd : dimacsLitValue val d = true <;>
      simp_all [dimacsLitValue, ha, hb, hc, hd] <;> omega

private theorem exactlyTwo_of_countP
    {uTri vTri : Bool} {D X : Nat → Nat → Bool}
    (Dv : Nat → Bool) (f : Nat → Nat)
    (hf : ∀ x y, f x = f y → x = y) (hfpos : ∀ j, 0 < f j)
    (js : List Nat) (hnd : js.Nodup)
    (hval : ∀ j ∈ js,
      muNegOneValOfRelations uTri vTri D X (f j) = Dv j)
    (hcount : (js.countP fun j => Dv j) = 2) :
    MuNegOneExactlyTwoSemantics
      (muNegOneValOfRelations uTri vTri D X)
      (js.map fun j => Int.ofNat (f j)) := by
  apply muNegOneExactlyTwoSemantics_of_two
  · exact hnd.map fun x y h => hf x y (Int.ofNat.inj h)
  · intro lit hlit
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hlit
    exact Int.natCast_pos.mpr (hfpos j)
  · rw [List.countP_map, ← hcount]
    apply List.countP_congr
    intro j hj
    simp only [Function.comp_apply]
    have hp : 0 < Int.ofNat (f j) := Int.natCast_pos.mpr (hfpos j)
    simp only [dimacsLitValue, if_pos hp]
    change muNegOneValOfRelations uTri vTri D X (f j) = true ↔ Dv j = true
    rw [hval j hj]

private theorem exactlyThree_of_countP
    {uTri vTri : Bool} {D X : Nat → Nat → Bool}
    (Dv : Nat → Bool) (f : Nat → Nat)
    (hfpos : ∀ j, 0 < f j) (js : List Nat) (hlen : js.length = 4)
    (hval : ∀ j ∈ js,
      muNegOneValOfRelations uTri vTri D X (f j) = Dv j)
    (hcount : (js.countP fun j => Dv j) = 3) :
    MuNegThreeExactlyThreeSemantics
      (muNegOneValOfRelations uTri vTri D X)
      (js.map fun j => Int.ofNat (f j)) := by
  apply muNegThreeExactlyThreeSemantics_of_count_three
  · simpa using hlen
  · intro lit hlit
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hlit
    exact Int.natCast_pos.mpr (hfpos j)
  · rw [List.countP_map, ← hcount]
    apply List.countP_congr
    intro j hj
    simp only [Function.comp_apply]
    have hp : 0 < Int.ofNat (f j) := Int.natCast_pos.mpr (hfpos j)
    simp only [dimacsLitValue, if_pos hp]
    change muNegOneValOfRelations uTri vTri D X (f j) = true ↔ Dv j = true
    rw [hval j hj]

private theorem same_filter_length_four (sigma : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j =>
      muNegOneSign sigma i == muNegOneSign sigma (8 + j)).length = 4 := by
  interval_cases i <;> cases sigma <;> decide

private theorem opp_filter_length_four (sigma : Bool) (i : Nat) (hi : i < 8) :
    ((List.range 8).filter fun j =>
      !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).length = 4 := by
  interval_cases i <;> cases sigma <;> decide

theorem muNegThreeZeroFiveCrossRowClauses_satisfied_of_counts
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsame : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun j => D i j) = 2)
    (hopp : ∀ i, i < 8 →
      (((List.range 8).filter fun j =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun j => D i j) = 3) :
    ∀ clause ∈ muNegThreeZeroFiveCrossRowClauses sigma,
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X) clause := by
  apply muNegThreeZeroFiveCrossRowClauses_satisfied
  · intro i hi
    refine exactlyTwo_of_countP (Dv := fun j => D i j)
      (fun j => muNegOneDVar i j) (fun x y h => ?_) (fun j => ?_)
      _ (List.nodup_range.filter _) (fun j hj => ?_) (hsame i hi)
    · unfold muNegOneDVar at h; omega
    · unfold muNegOneDVar; omega
    · exact muNegOneValOfRelations_dvar uTri vTri D X hi
        (List.mem_range.mp (List.mem_of_mem_filter hj))
  · intro i hi
    refine exactlyThree_of_countP (Dv := fun j => D i j)
      (fun j => muNegOneDVar i j) (fun j => ?_) _
      (opp_filter_length_four sigma i hi) (fun j hj => ?_) (hopp i hi)
    · unfold muNegOneDVar; omega
    · exact muNegOneValOfRelations_dvar uTri vTri D X hi
        (List.mem_range.mp (List.mem_of_mem_filter hj))

theorem muNegThreeZeroFiveCrossColClauses_satisfied_of_counts
    {uTri vTri sigma : Bool} {D X : Nat → Nat → Bool}
    (hsame : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        muNegOneSign sigma i == muNegOneSign sigma (8 + j)).countP
          fun i => D i j) = 2)
    (hopp : ∀ j, j < 8 →
      (((List.range 8).filter fun i =>
        !(muNegOneSign sigma i == muNegOneSign sigma (8 + j))).countP
          fun i => D i j) = 3) :
    ∀ clause ∈ muNegThreeZeroFiveCrossColClauses sigma,
      dimacsClauseSatisfied (muNegOneValOfRelations uTri vTri D X) clause := by
  apply muNegThreeZeroFiveCrossColClauses_satisfied
  · intro j hj
    refine exactlyTwo_of_countP (Dv := fun i => D i j)
      (fun i => muNegOneDVar i j) (fun x y h => ?_) (fun i => ?_)
      _ (List.nodup_range.filter _) (fun i hi => ?_) (hsame j hj)
    · unfold muNegOneDVar at h; omega
    · unfold muNegOneDVar; omega
    · exact muNegOneValOfRelations_dvar uTri vTri D X
        (List.mem_range.mp (List.mem_of_mem_filter hi)) hj
  · intro j hj
    refine exactlyThree_of_countP (Dv := fun i => D i j)
      (fun i => muNegOneDVar i j) (fun i => ?_) _ ?_ (fun i hi => ?_)
      (hopp j hj)
    · unfold muNegOneDVar; omega
    · -- Swapping the two alternating shores preserves four opposite signs.
      interval_cases j <;> cases sigma <;> decide
    · exact muNegOneValOfRelations_dvar uTri vTri D X
        (List.mem_range.mp (List.mem_of_mem_filter hi)) hj

end Erdos85

#print axioms Erdos85.muNegThreeExactlyThreeSemantics_of_count_three
#print axioms Erdos85.muNegThreeZeroFiveCrossRowClauses_satisfied_of_counts
#print axioms Erdos85.muNegThreeZeroFiveCrossColClauses_satisfied_of_counts
