import Mathlib

/-!
# Occupancy step for the H1 CUBE25 CNF cover

These lemmas concern arbitrary truth assignments. A reverse sequential-counter
argument supplies the lower bound on true inputs; pair clauses supply the
at-most-one hypotheses. No DIMACS containment or cube UNSAT is asserted here.
-/

namespace Erdos85

/-- If each block contains at most one selected item and there are at least as
many selected items as blocks, every block is occupied. -/
theorem block_occupied_of_total_ge
    {n m : Nat} (selected : Fin n → Fin m → Prop)
    [∀ b, DecidablePred (selected b)]
    (unique : ∀ b i j, selected b i → selected b j → i = j)
    (total : n ≤ ∑ b : Fin n, (Finset.univ.filter (selected b)).card)
    (b : Fin n) : ∃ i, selected b i := by
  classical
  have bound : ∀ c : Fin n, (Finset.univ.filter (selected c)).card ≤ 1 := by
    intro c
    apply Finset.card_le_one.mpr
    intro i hi j hj
    exact unique c i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  by_contra empty
  have zero : (Finset.univ.filter (selected b)).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    exact empty ⟨i, (Finset.mem_filter.mp hi).2⟩
  have strict : (∑ c : Fin n, (Finset.univ.filter (selected c)).card) <
      ∑ _c : Fin n, (1 : Nat) := by
    apply Finset.sum_lt_sum
    · intro c _
      exact bound c
    · exact ⟨b, Finset.mem_univ b, by omega⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    mul_one] at strict
  omega

/-- Two six-block rows, each with at least six true inputs and at most one per
block, choose one of the 25 pairs in any two designated five-item blocks. -/
theorem oneHighCube25_assignment_cover
    (left right : Fin 6 → Fin 5 → Prop)
    [∀ b, DecidablePred (left b)] [∀ b, DecidablePred (right b)]
    (left_unique : ∀ b i j, left b i → left b j → i = j)
    (right_unique : ∀ b i j, right b i → right b j → i = j)
    (left_total : 6 ≤ ∑ b : Fin 6, (Finset.univ.filter (left b)).card)
    (right_total : 6 ≤ ∑ b : Fin 6, (Finset.univ.filter (right b)).card)
    (left_block right_block : Fin 6) :
    ∃ i j : Fin 5, left left_block i ∧ right right_block j := by
  classical
  obtain ⟨i, hi⟩ := block_occupied_of_total_ge left left_unique left_total left_block
  obtain ⟨j, hj⟩ := block_occupied_of_total_ge right right_unique right_total right_block
  exact ⟨i, j, hi, hj⟩

/-- The complemented lower counter allows at most 24 false inputs in a row
of 30, hence at least six true inputs. -/
theorem oneHighCube25_true_total_of_false_bound
    (selected : Fin 6 → Fin 5 → Prop) [∀ b, DecidablePred (selected b)]
    (false_bound :
      (∑ b : Fin 6, (Finset.univ.filter (fun i => ¬ selected b i)).card) ≤ 24) :
    6 ≤ ∑ b : Fin 6, (Finset.univ.filter (selected b)).card := by
  have partition : ∀ b : Fin 6,
      (Finset.univ.filter (selected b)).card +
      (Finset.univ.filter (fun i => ¬ selected b i)).card = 5 := by
    intro b
    simpa using Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 5))) (p := selected b)
  have total := congrArg (fun f : Fin 6 → Nat => ∑ b, f b) (funext partition)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul] at total
  omega

/-- Clause-level premises for the two-row cover: each negative pair clause
forbids two true inputs in a block, and each lower counter bounds false inputs.
The caller must establish these premises from its actual emitted clauses. -/
theorem oneHighCube25_cover_of_pair_clauses_and_false_bounds
    (left right : Fin 6 → Fin 5 → Prop)
    [∀ b, DecidablePred (left b)] [∀ b, DecidablePred (right b)]
    (left_pairs : ∀ b i j, i ≠ j → ¬ left b i ∨ ¬ left b j)
    (right_pairs : ∀ b i j, i ≠ j → ¬ right b i ∨ ¬ right b j)
    (left_false :
      (∑ b : Fin 6, (Finset.univ.filter (fun i => ¬ left b i)).card) ≤ 24)
    (right_false :
      (∑ b : Fin 6, (Finset.univ.filter (fun i => ¬ right b i)).card) ≤ 24)
    (left_block right_block : Fin 6) :
    ∃ i j : Fin 5, left left_block i ∧ right right_block j := by
  apply oneHighCube25_assignment_cover left right
  · intro b i j hi hj
    by_contra different
    exact (left_pairs b i j different).elim (fun h => h hi) (fun h => h hj)
  · intro b i j hi hj
    by_contra different
    exact (right_pairs b i j different).elim (fun h => h hi) (fun h => h hj)
  · exact oneHighCube25_true_total_of_false_bound left left_false
  · exact oneHighCube25_true_total_of_false_bound right right_false

end Erdos85

#print axioms Erdos85.block_occupied_of_total_ge
#print axioms Erdos85.oneHighCube25_assignment_cover
#print axioms Erdos85.oneHighCube25_true_total_of_false_bound
#print axioms Erdos85.oneHighCube25_cover_of_pair_clauses_and_false_bounds
