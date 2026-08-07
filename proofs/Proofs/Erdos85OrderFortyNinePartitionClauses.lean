import Proofs.Erdos85OrderFortyNineC4Clauses

/-!
# Partition-law clauses for the certified order-49 instances

These are the final 40 × 9 clauses in the production CNF.  For each low
vertex `y` and high point `w`, the clause lists the edges from `y` to the
other lows whose prescribed support contains `w`.
-/

namespace Erdos85

def orderFortyNinePartitionNeighbors (masks : Array Nat) (w : Fin 9) :
    List (Fin 49) :=
  ((List.finRange 40).map orderFortyNineLowVertex).filter fun x =>
    (orderFortyNineSupportMask masks x).getLsbD w.val

def orderFortyNinePartitionClause
    (masks : Array Nat) (y : Fin 40) (w : Fin 9) : DimacsClause :=
  ((orderFortyNinePartitionNeighbors masks w).filter fun x =>
      x ≠ orderFortyNineLowVertex y).map fun x =>
    orderFortyNineEdgeLiteral (orderFortyNineLowVertex y) x

def orderFortyNinePartitionClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 40).flatMap fun y =>
    (List.finRange 9).map fun w =>
      orderFortyNinePartitionClause masks y w).toArray

theorem orderFortyNineLowVertex_injective :
    Function.Injective orderFortyNineLowVertex := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp [orderFortyNineLowVertex] at hval
  omega

theorem orderFortyNineLowVertex_surjective
    (k : Fin 49) (hk : 9 ≤ k.val) :
    ∃ y : Fin 40, orderFortyNineLowVertex y = k := by
  refine ⟨⟨k.val - 9, by omega⟩, ?_⟩
  apply Fin.ext
  simp [orderFortyNineLowVertex]
  omega

theorem orderFortyNinePartitionClause_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks)
    (y : Fin 40) (w : Fin 9) :
    dimacsClauseSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNinePartitionClause masks y w) := by
  let vy := orderFortyNineLowVertex y
  let candidates := Finset.univ.filter fun k =>
    orderFortyNineBitAdj edges vy k &&
      (orderFortyNineSupportMask masks k).getLsbD w.val
  have hcard : candidates.card = 1 := by
    exact hc.2.2.2.2.2 vy (by simp [vy, orderFortyNineLowVertex]) w (by omega)
  have hpos : 0 < candidates.card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  have hkand := (Finset.mem_filter.mp hk).2
  simp only [Bool.and_eq_true] at hkand
  have hadj : orderFortyNineBitAdj edges vy k = true :=
    hkand.1
  have hsupport :
      (orderFortyNineSupportMask masks k).getLsbD w.val = true :=
    hkand.2
  have hkLow : 9 ≤ k.val := by
    by_contra hnot
    have hkHigh : k.val < 9 := by omega
    let a : Fin 9 := ⟨k.val, hkHigh⟩
    have hka : orderFortyNineHighVertex a = k := by
      apply Fin.ext
      rfl
    have hz := hzero a w
    rw [hka] at hz
    rw [hz] at hsupport
    contradiction
  obtain ⟨x, rfl⟩ := orderFortyNineLowVertex_surjective k hkLow
  have hxy : x ≠ y := by
    intro heq
    subst x
    simp [vy, orderFortyNineBitAdj] at hadj
  have hxmem : orderFortyNineLowVertex x ∈
      orderFortyNinePartitionNeighbors masks w := by
    simp only [orderFortyNinePartitionNeighbors, List.mem_filter,
      List.mem_map, List.mem_finRange, true_and]
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact hsupport
  refine ⟨orderFortyNineEdgeLiteral vy (orderFortyNineLowVertex x), ?_, ?_⟩
  · simp only [orderFortyNinePartitionClause, List.mem_map, List.mem_filter]
    have hneLow : orderFortyNineLowVertex x ≠ orderFortyNineLowVertex y :=
      fun heq => hxy (orderFortyNineLowVertex_injective heq)
    exact ⟨orderFortyNineLowVertex x, ⟨hxmem, by
      simpa only [decide_eq_true_eq] using hneLow⟩, rfl⟩
  · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges vy
      (orderFortyNineLowVertex x) (by
        exact fun heq => hxy (orderFortyNineLowVertex_injective heq.symm))]
    exact hadj

theorem orderFortyNinePartitionClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNinePartitionClauses masks) := by
  intro clause hclause
  simp only [orderFortyNinePartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  exact orderFortyNinePartitionClause_satisfied hc hzero y w

theorem orderFortyNinePartitionClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176 (orderFortyNinePartitionClauses masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNinePartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNinePartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  have hxyDec := (List.mem_filter.mp hx).2
  have hxy : x ≠ orderFortyNineLowVertex y :=
    of_decide_eq_true hxyDec
  exact orderFortyNineEdgeLiteral_bounded _ _ hxy.symm

end Erdos85
