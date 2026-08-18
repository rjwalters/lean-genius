import Proofs.Erdos85OrderFortyNineCanonicalCnf

/-! # Semantic bridge for the exact h=3 order-49 CNF -/

namespace Erdos85

open Std Sat

def orderFortyNineH3HighVertex (w : Fin 3) : Fin 49 := ⟨w.val, by omega⟩

def orderFortyNineH3LowVertex (y : Fin 46) : Fin 49 := ⟨y.val + 3, by omega⟩

def orderFortyNineH3HighPairs : List (Fin 3 × Fin 3) :=
  (List.finRange 3).flatMap fun a =>
    ((List.finRange 3).filter fun b => a.val < b.val).map fun b => (a, b)

def orderFortyNineH3HighHighFixedClauses : Array DimacsClause :=
  (orderFortyNineH3HighPairs.map fun ab =>
    [-orderFortyNineEdgeLiteral
      (orderFortyNineH3HighVertex ab.1) (orderFortyNineH3HighVertex ab.2)]).toArray

def orderFortyNineH3SupportUnitLiteral
    (masks : Array Nat) (y : Fin 46) (w : Fin 3) : Int :=
  let edge := orderFortyNineEdgeLiteral
    (orderFortyNineH3LowVertex y) (orderFortyNineH3HighVertex w)
  if (orderFortyNineSupportMask masks (orderFortyNineH3LowVertex y)).getLsbD w.val
    then edge else -edge

def orderFortyNineH3HighLowFixedClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 46).flatMap fun y =>
    (List.finRange 3).map fun w =>
      [orderFortyNineH3SupportUnitLiteral masks y w]).toArray

def orderFortyNineH3FixedClauses (masks : Array Nat) : Array DimacsClause :=
  orderFortyNineH3HighHighFixedClauses ++
    orderFortyNineH3HighLowFixedClauses masks

def orderFortyNineH3PartitionNeighbors (masks : Array Nat) (w : Fin 3) :
    List (Fin 49) :=
  ((List.finRange 46).map orderFortyNineH3LowVertex).filter fun x =>
    (orderFortyNineSupportMask masks x).getLsbD w.val

def orderFortyNineH3PartitionClause
    (masks : Array Nat) (y : Fin 46) (w : Fin 3) : DimacsClause :=
  ((orderFortyNineH3PartitionNeighbors masks w).filter fun x =>
      x ≠ orderFortyNineH3LowVertex y).map fun x =>
    orderFortyNineEdgeLiteral (orderFortyNineH3LowVertex y) x

def orderFortyNineH3PartitionClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 46).flatMap fun y =>
    (List.finRange 3).map fun w =>
      orderFortyNineH3PartitionClause masks y w).toArray

def orderFortyNineGeneratedH3SatCnf (masks : Array Nat) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (orderFortyNineH3FixedClauses masks) ++
    dimacsFormulaToSatClauses orderFortyNineC4Clauses ++
    dimacsFormulaToSatClauses (orderFortyNineDegreeBlocks 3).clauses ++
    dimacsFormulaToSatClauses (orderFortyNineH3PartitionClauses masks)

theorem orderFortyNineGeneratedH3SatCnf_eq_canonical (masks : Array Nat) :
    orderFortyNineGeneratedH3SatCnf masks =
      orderFortyNineGeneratedCanonicalSatCnf 3 masks := by
  rfl

def OrderFortyNineH3HighMasksZero (masks : Array Nat) : Prop :=
  ∀ a w : Fin 3,
    (orderFortyNineSupportMask masks
      (orderFortyNineH3HighVertex a)).getLsbD w.val = false

theorem orderFortyNineH3HighVertex_injective :
    Function.Injective orderFortyNineH3HighVertex := by
  intro a b hab
  apply Fin.ext
  simpa [orderFortyNineH3HighVertex] using congrArg Fin.val hab

theorem orderFortyNineH3LowVertex_ne_highVertex (y : Fin 46) (w : Fin 3) :
    orderFortyNineH3LowVertex y ≠ orderFortyNineH3HighVertex w := by
  intro heq
  have := congrArg Fin.val heq
  simp [orderFortyNineH3LowVertex, orderFortyNineH3HighVertex] at this
  omega

theorem orderFortyNineH3HighPairs_ne (ab : Fin 3 × Fin 3)
    (hab : ab ∈ orderFortyNineH3HighPairs) : ab.1 ≠ ab.2 := by
  native_decide +revert

theorem orderFortyNineH3HighHighFixedClauses_satisfied
    (edges : BitVec 1176)
    (hhigh : ∀ a b : Fin 3, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH3HighVertex a)
        (orderFortyNineH3HighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineH3HighHighFixedClauses := by
  intro clause hclause
  simp only [orderFortyNineH3HighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  rcases ab with ⟨a, b⟩
  have hab' : a ≠ b := orderFortyNineH3HighPairs_ne (a, b) hab
  have hne : orderFortyNineH3HighVertex a ≠ orderFortyNineH3HighVertex b := by
    exact fun heq => hab' (orderFortyNineH3HighVertex_injective heq)
  refine ⟨-orderFortyNineEdgeLiteral
      (orderFortyNineH3HighVertex a) (orderFortyNineH3HighVertex b), by simp, ?_⟩
  rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
    hhigh a b hab']
  rfl

theorem orderFortyNineH3HighHigh_independent_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hzero : OrderFortyNineH3HighMasksZero masks) :
    ∀ a b : Fin 3, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH3HighVertex a)
        (orderFortyNineH3HighVertex b) = false := by
  intro a b hab
  let b9 : Fin 9 := Fin.castLE (by omega) b
  have hb9 : b9.val < 3 := by simp [b9]
  have hsupp := hc.2.2.2.2.1 (orderFortyNineH3HighVertex a) b9 hb9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineH3HighVertex a)
          (orderFortyNineH3HighVertex b) =
        (orderFortyNineSupportMask masks
          (orderFortyNineH3HighVertex a)).getLsbD b.val := by
    simpa [b9, orderFortyNineH3HighVertex] using hsupp
  rw [hsupp', hzero a b]

theorem orderFortyNineH3HighLowFixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH3HighLowFixedClauses masks) := by
  intro clause hclause
  simp only [orderFortyNineH3HighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  have hne := orderFortyNineH3LowVertex_ne_highVertex y w
  let w9 : Fin 9 := Fin.castLE (by omega) w
  have hw9 : w9.val < 3 := by simp [w9]
  have hsupp := hc.2.2.2.2.1 (orderFortyNineH3LowVertex y) w9 hw9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineH3LowVertex y)
          (orderFortyNineH3HighVertex w) =
        (orderFortyNineSupportMask masks (orderFortyNineH3LowVertex y)).getLsbD
          w.val := by
    simpa [w9, orderFortyNineH3HighVertex] using hsupp
  by_cases hbit :
      (orderFortyNineSupportMask masks (orderFortyNineH3LowVertex y)).getLsbD
        w.val = true
  · refine ⟨orderFortyNineEdgeLiteral
        (orderFortyNineH3LowVertex y) (orderFortyNineH3HighVertex w), ?_, ?_⟩
    · simp [orderFortyNineH3SupportUnitLiteral, hbit]
    · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne, hsupp', hbit]
  · have hbitFalse :
        (orderFortyNineSupportMask masks (orderFortyNineH3LowVertex y)).getLsbD
          w.val = false := Bool.eq_false_of_not_eq_true hbit
    refine ⟨-orderFortyNineEdgeLiteral
        (orderFortyNineH3LowVertex y) (orderFortyNineH3HighVertex w), ?_, ?_⟩
    · simp only [orderFortyNineH3SupportUnitLiteral]
      rw [if_neg hbit]
      simp
    · rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
        hsupp', hbitFalse]
      rfl

theorem orderFortyNineH3HighHighFixedClauses_bounded :
    dimacsFormulaBounded 1176 orderFortyNineH3HighHighFixedClauses := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH3HighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  exact orderFortyNineNegEdgeLiteral_bounded _ _
    (fun heq => orderFortyNineH3HighPairs_ne ab hab
      (orderFortyNineH3HighVertex_injective heq))

theorem orderFortyNineH3HighLowFixedClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176
      (orderFortyNineH3HighLowFixedClauses masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH3HighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  unfold orderFortyNineH3SupportUnitLiteral
  split
  · exact orderFortyNineEdgeLiteral_bounded _ _
      (orderFortyNineH3LowVertex_ne_highVertex y w)
  · exact orderFortyNineNegEdgeLiteral_bounded _ _
      (orderFortyNineH3LowVertex_ne_highVertex y w)

theorem orderFortyNineH3FixedClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176 (orderFortyNineH3FixedClauses masks) :=
  dimacsFormulaBounded_append orderFortyNineH3HighHighFixedClauses_bounded
    (orderFortyNineH3HighLowFixedClauses_bounded masks)

theorem orderFortyNineH3FixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hhigh : ∀ a b : Fin 3, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH3HighVertex a)
        (orderFortyNineH3HighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH3FixedClauses masks) :=
  dimacsFormulaSatisfied_append
    (orderFortyNineH3HighHighFixedClauses_satisfied edges hhigh)
    (orderFortyNineH3HighLowFixedClauses_satisfied hc)

theorem orderFortyNineH3FixedClauses_satisfied_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hzero : OrderFortyNineH3HighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH3FixedClauses masks) :=
  orderFortyNineH3FixedClauses_satisfied hc
    (orderFortyNineH3HighHigh_independent_of_zero_masks hc hzero)

theorem orderFortyNineH3LowVertex_injective :
    Function.Injective orderFortyNineH3LowVertex := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp [orderFortyNineH3LowVertex] at hval
  omega

theorem orderFortyNineH3LowVertex_surjective
    (k : Fin 49) (hk : 3 ≤ k.val) :
    ∃ y : Fin 46, orderFortyNineH3LowVertex y = k := by
  refine ⟨⟨k.val - 3, by omega⟩, ?_⟩
  apply Fin.ext
  simp [orderFortyNineH3LowVertex]
  omega

theorem orderFortyNineH3PartitionClause_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hzero : OrderFortyNineH3HighMasksZero masks)
    (y : Fin 46) (w : Fin 3) :
    dimacsClauseSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH3PartitionClause masks y w) := by
  let vy := orderFortyNineH3LowVertex y
  let candidates := Finset.univ.filter fun k =>
    orderFortyNineBitAdj edges vy k &&
      (orderFortyNineSupportMask masks k).getLsbD w.val
  have hcard : candidates.card = 1 := by
    let w9 : Fin 9 := Fin.castLE (by omega) w
    have hw9 : w9.val < 3 := by simp [w9]
    simpa [candidates, w9] using
      hc.2.2.2.2.2 vy (by simp [vy, orderFortyNineH3LowVertex]) w9 hw9
  have hpos : 0 < candidates.card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  have hkand := (Finset.mem_filter.mp hk).2
  simp only [Bool.and_eq_true] at hkand
  have hadj : orderFortyNineBitAdj edges vy k = true :=
    hkand.1
  have hsupport :
      (orderFortyNineSupportMask masks k).getLsbD w.val = true :=
    hkand.2
  have hkLow : 3 ≤ k.val := by
    by_contra hnot
    have hkHigh : k.val < 3 := by omega
    let a : Fin 3 := ⟨k.val, hkHigh⟩
    have hka : orderFortyNineH3HighVertex a = k := by
      apply Fin.ext
      rfl
    have hz := hzero a w
    rw [hka] at hz
    rw [hz] at hsupport
    contradiction
  obtain ⟨x, rfl⟩ := orderFortyNineH3LowVertex_surjective k hkLow
  have hxy : x ≠ y := by
    intro heq
    subst x
    simp [vy, orderFortyNineBitAdj] at hadj
  have hxmem : orderFortyNineH3LowVertex x ∈
      orderFortyNineH3PartitionNeighbors masks w := by
    simp only [orderFortyNineH3PartitionNeighbors, List.mem_filter,
      List.mem_map, List.mem_finRange, true_and]
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact hsupport
  refine ⟨orderFortyNineEdgeLiteral vy (orderFortyNineH3LowVertex x), ?_, ?_⟩
  · simp only [orderFortyNineH3PartitionClause, List.mem_map, List.mem_filter]
    have hneLow : orderFortyNineH3LowVertex x ≠ orderFortyNineH3LowVertex y :=
      fun heq => hxy (orderFortyNineH3LowVertex_injective heq)
    exact ⟨orderFortyNineH3LowVertex x, ⟨hxmem, by
      simpa only [decide_eq_true_eq] using hneLow⟩, rfl⟩
  · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges vy
      (orderFortyNineH3LowVertex x) (by
        exact fun heq => hxy (orderFortyNineH3LowVertex_injective heq.symm))]
    exact hadj

theorem orderFortyNineH3PartitionClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hzero : OrderFortyNineH3HighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH3PartitionClauses masks) := by
  intro clause hclause
  simp only [orderFortyNineH3PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  exact orderFortyNineH3PartitionClause_satisfied hc hzero y w

theorem orderFortyNineH3PartitionClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176 (orderFortyNineH3PartitionClauses masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH3PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineH3PartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  have hxyDec := (List.mem_filter.mp hx).2
  have hxy : x ≠ orderFortyNineH3LowVertex y :=
    of_decide_eq_true hxyDec
  exact orderFortyNineEdgeLiteral_bounded _ _ hxy.symm

theorem orderFortyNineH3C4Clauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineC4Clauses := by
  intro clause hclause
  simp only [orderFortyNineC4Clauses, List.mem_toArray, List.mem_map] at hclause
  obtain ⟨q, hq, rfl⟩ := hclause
  exact orderFortyNineC4Clause_satisfied hc.2.2.2.1 q hq

structure OrderFortyNineH3CnfSegmentsSatisfied
    (masks : Array Nat) (val : DimacsValuation) : Prop where
  fixed : dimacsFormulaSatisfied val (orderFortyNineH3FixedClauses masks)
  c4 : dimacsFormulaSatisfied val orderFortyNineC4Clauses
  degree : dimacsFormulaSatisfied val (orderFortyNineDegreeBlocks 3).clauses
  partition : dimacsFormulaSatisfied val (orderFortyNineH3PartitionClauses masks)

theorem orderFortyNineH3CnfSegments_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hzero : OrderFortyNineH3HighMasksZero masks) :
    ∃ val : DimacsValuation,
      OrderFortyNineH3CnfSegmentsSatisfied masks val ∧
      ∀ id, id ≤ 1176 → val id = orderFortyNineDimacsEdgeVal edges id := by
  obtain ⟨val, hdegreeSat, hdegreeBounded, htop, hagree⟩ :=
    orderFortyNineDegreeBlocks_invariant hc
  refine ⟨val, ?_, hagree⟩
  constructor
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH3FixedClauses_satisfied_of_zero_masks hc hzero)
      (orderFortyNineH3FixedClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH3C4Clauses_satisfied hc)
      orderFortyNineC4Clauses_bounded
      (fun id hid => (hagree id hid).symm)
  · exact hdegreeSat
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH3PartitionClauses_satisfied hc hzero)
      (orderFortyNineH3PartitionClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)

theorem orderFortyNineH3FixedClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineH3FixedClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH3FixedClauses, Array.mem_append] at hclause
  rcases hclause with hhigh | hlow
  · simp only [orderFortyNineH3HighHighFixedClauses, List.mem_toArray,
      List.mem_map] at hhigh
    obtain ⟨ab, hab, rfl⟩ := hhigh
    simp only [List.mem_singleton] at hlit
    subst lit
    simp [orderFortyNineEdgeLiteral] <;> omega
  · simp only [orderFortyNineH3HighLowFixedClauses, List.mem_toArray,
      List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hlow
    obtain ⟨y, w, rfl⟩ := hlow
    simp only [List.mem_singleton] at hlit
    subst lit
    unfold orderFortyNineH3SupportUnitLiteral
    split <;> simp [orderFortyNineEdgeLiteral] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem orderFortyNineDegreeBlocks_three_nonzero :
    ∀ clause ∈ (orderFortyNineDegreeBlocks 3).clauses,
      DimacsClauseNonzero clause := by
  have hcheck :
      (orderFortyNineDegreeBlocks 3).clauses.all fun clause =>
        clause.all fun lit => lit != 0 := by
    native_decide
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

theorem orderFortyNineH3PartitionClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineH3PartitionClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH3PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineH3PartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  simp [orderFortyNineEdgeLiteral] <;> omega

structure OrderFortyNineH3CnfCoveredBySegments
    (masks : Array Nat) (cnf : CNF Nat) : Prop where
  covered : ∀ clause ∈ cnf.clauses,
    (∃ source ∈ orderFortyNineH3FixedClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineC4Clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ (orderFortyNineDegreeBlocks 3).clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineH3PartitionClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source)

theorem orderFortyNineGeneratedH3SatCnf_covered (masks : Array Nat) :
    OrderFortyNineH3CnfCoveredBySegments masks
      (orderFortyNineGeneratedH3SatCnf masks) := by
  constructor
  intro clause hclause
  simp only [orderFortyNineGeneratedH3SatCnf, Array.mem_append,
    dimacsFormulaToSatClauses, Array.mem_map] at hclause
  rcases hclause with ((hfixed | hc4) | hdegree) | hpartition
  · obtain ⟨source, hsource, rfl⟩ := hfixed
    exact Or.inl ⟨source, hsource,
      orderFortyNineH3FixedClauses_nonzero masks source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hc4
    exact Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineC4Clauses_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hdegree
    exact Or.inr <| Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineDegreeBlocks_three_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hpartition
    exact Or.inr <| Or.inr <| Or.inr ⟨source, hsource,
      orderFortyNineH3PartitionClauses_nonzero masks source hsource, rfl⟩

theorem sat_of_orderFortyNineH3CnfSegmentsSatisfied_of_covered
    {masks : Array Nat} {cnf : CNF Nat} {val : DimacsValuation}
    (hsat : OrderFortyNineH3CnfSegmentsSatisfied masks val)
    (hcovered : OrderFortyNineH3CnfCoveredBySegments masks cnf) :
    cnf.Sat (satAssignmentOfDimacs val) := by
  rw [CNF.sat_def, CNF.eval, Array.all_eq_true]
  intro i hi
  rcases hcovered.covered cnf.clauses[i] (Array.getElem_mem hi) with
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩ |
      ⟨source, hsource, hnz, heq⟩
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.fixed source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.c4 source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.degree source hsource)
  · rw [heq]
    exact satClause_of_dimacsClauseSatisfied hnz (hsat.partition source hsource)

theorem false_of_orderFortyNine_generated_h3_lrat
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 3 masks edges)
    (hzero : OrderFortyNineH3HighMasksZero masks)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedH3SatCnf masks)) : False := by
  obtain ⟨val, hsegments, _⟩ := orderFortyNineH3CnfSegments_satisfied hc hzero
  have hsat := sat_of_orderFortyNineH3CnfSegmentsSatisfied_of_covered
    hsegments (orderFortyNineGeneratedH3SatCnf_covered masks)
  have hunsat := Std.Tactic.BVDecide.LRAT.check_sound proof _ hcheck
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85
