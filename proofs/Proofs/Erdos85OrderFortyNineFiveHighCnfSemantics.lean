import Proofs.Erdos85OrderFortyNineCanonicalCnf

/-! # Semantic bridge for the exact h=5 order-49 CNF -/

namespace Erdos85

open Std Sat

def orderFortyNineH5HighVertex (w : Fin 5) : Fin 49 := ⟨w.val, by omega⟩

def orderFortyNineH5LowVertex (y : Fin 44) : Fin 49 := ⟨y.val + 5, by omega⟩

def orderFortyNineH5HighPairs : List (Fin 5 × Fin 5) :=
  (List.finRange 5).flatMap fun a =>
    ((List.finRange 5).filter fun b => a.val < b.val).map fun b => (a, b)

def orderFortyNineH5HighHighFixedClauses : Array DimacsClause :=
  (orderFortyNineH5HighPairs.map fun ab =>
    [-orderFortyNineEdgeLiteral
      (orderFortyNineH5HighVertex ab.1) (orderFortyNineH5HighVertex ab.2)]).toArray

def orderFortyNineH5SupportUnitLiteral
    (masks : Array Nat) (y : Fin 44) (w : Fin 5) : Int :=
  let edge := orderFortyNineEdgeLiteral
    (orderFortyNineH5LowVertex y) (orderFortyNineH5HighVertex w)
  if (orderFortyNineSupportMask masks (orderFortyNineH5LowVertex y)).getLsbD w.val
    then edge else -edge

def orderFortyNineH5HighLowFixedClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 44).flatMap fun y =>
    (List.finRange 5).map fun w =>
      [orderFortyNineH5SupportUnitLiteral masks y w]).toArray

def orderFortyNineH5FixedClauses (masks : Array Nat) : Array DimacsClause :=
  orderFortyNineH5HighHighFixedClauses ++
    orderFortyNineH5HighLowFixedClauses masks

def orderFortyNineH5PartitionNeighbors (masks : Array Nat) (w : Fin 5) :
    List (Fin 49) :=
  ((List.finRange 44).map orderFortyNineH5LowVertex).filter fun x =>
    (orderFortyNineSupportMask masks x).getLsbD w.val

def orderFortyNineH5PartitionClause
    (masks : Array Nat) (y : Fin 44) (w : Fin 5) : DimacsClause :=
  ((orderFortyNineH5PartitionNeighbors masks w).filter fun x =>
      x ≠ orderFortyNineH5LowVertex y).map fun x =>
    orderFortyNineEdgeLiteral (orderFortyNineH5LowVertex y) x

def orderFortyNineH5PartitionClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 44).flatMap fun y =>
    (List.finRange 5).map fun w =>
      orderFortyNineH5PartitionClause masks y w).toArray

def orderFortyNineGeneratedH5SatCnf (masks : Array Nat) : CNF Nat where
  clauses :=
    dimacsFormulaToSatClauses (orderFortyNineH5FixedClauses masks) ++
    dimacsFormulaToSatClauses orderFortyNineC4Clauses ++
    dimacsFormulaToSatClauses (orderFortyNineDegreeBlocks 5).clauses ++
    dimacsFormulaToSatClauses (orderFortyNineH5PartitionClauses masks)

theorem orderFortyNineGeneratedH5SatCnf_eq_canonical (masks : Array Nat) :
    orderFortyNineGeneratedH5SatCnf masks =
      orderFortyNineGeneratedCanonicalSatCnf 5 masks := by
  rfl

def OrderFortyNineH5HighMasksZero (masks : Array Nat) : Prop :=
  ∀ a w : Fin 5,
    (orderFortyNineSupportMask masks
      (orderFortyNineH5HighVertex a)).getLsbD w.val = false

theorem orderFortyNineH5HighVertex_injective :
    Function.Injective orderFortyNineH5HighVertex := by
  intro a b hab
  apply Fin.ext
  simpa [orderFortyNineH5HighVertex] using congrArg Fin.val hab

theorem orderFortyNineH5LowVertex_ne_highVertex (y : Fin 44) (w : Fin 5) :
    orderFortyNineH5LowVertex y ≠ orderFortyNineH5HighVertex w := by
  intro heq
  have := congrArg Fin.val heq
  simp [orderFortyNineH5LowVertex, orderFortyNineH5HighVertex] at this
  omega

theorem orderFortyNineH5HighPairs_ne (ab : Fin 5 × Fin 5)
    (hab : ab ∈ orderFortyNineH5HighPairs) : ab.1 ≠ ab.2 := by
  native_decide +revert

theorem orderFortyNineH5HighHighFixedClauses_satisfied
    (edges : BitVec 1176)
    (hhigh : ∀ a b : Fin 5, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH5HighVertex a)
        (orderFortyNineH5HighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineH5HighHighFixedClauses := by
  intro clause hclause
  simp only [orderFortyNineH5HighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  rcases ab with ⟨a, b⟩
  have hab' : a ≠ b := orderFortyNineH5HighPairs_ne (a, b) hab
  have hne : orderFortyNineH5HighVertex a ≠ orderFortyNineH5HighVertex b := by
    exact fun heq => hab' (orderFortyNineH5HighVertex_injective heq)
  refine ⟨-orderFortyNineEdgeLiteral
      (orderFortyNineH5HighVertex a) (orderFortyNineH5HighVertex b), by simp, ?_⟩
  rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
    hhigh a b hab']
  rfl

theorem orderFortyNineH5HighHigh_independent_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hzero : OrderFortyNineH5HighMasksZero masks) :
    ∀ a b : Fin 5, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH5HighVertex a)
        (orderFortyNineH5HighVertex b) = false := by
  intro a b hab
  let b9 : Fin 9 := Fin.castLE (by omega) b
  have hb9 : b9.val < 5 := by simp [b9]
  have hsupp := hc.2.2.2.2.1 (orderFortyNineH5HighVertex a) b9 hb9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineH5HighVertex a)
          (orderFortyNineH5HighVertex b) =
        (orderFortyNineSupportMask masks
          (orderFortyNineH5HighVertex a)).getLsbD b.val := by
    simpa [b9, orderFortyNineH5HighVertex] using hsupp
  rw [hsupp', hzero a b]

theorem orderFortyNineH5HighLowFixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH5HighLowFixedClauses masks) := by
  intro clause hclause
  simp only [orderFortyNineH5HighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  have hne := orderFortyNineH5LowVertex_ne_highVertex y w
  let w9 : Fin 9 := Fin.castLE (by omega) w
  have hw9 : w9.val < 5 := by simp [w9]
  have hsupp := hc.2.2.2.2.1 (orderFortyNineH5LowVertex y) w9 hw9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineH5LowVertex y)
          (orderFortyNineH5HighVertex w) =
        (orderFortyNineSupportMask masks (orderFortyNineH5LowVertex y)).getLsbD
          w.val := by
    simpa [w9, orderFortyNineH5HighVertex] using hsupp
  by_cases hbit :
      (orderFortyNineSupportMask masks (orderFortyNineH5LowVertex y)).getLsbD
        w.val = true
  · refine ⟨orderFortyNineEdgeLiteral
        (orderFortyNineH5LowVertex y) (orderFortyNineH5HighVertex w), ?_, ?_⟩
    · simp [orderFortyNineH5SupportUnitLiteral, hbit]
    · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne, hsupp', hbit]
  · have hbitFalse :
        (orderFortyNineSupportMask masks (orderFortyNineH5LowVertex y)).getLsbD
          w.val = false := Bool.eq_false_of_not_eq_true hbit
    refine ⟨-orderFortyNineEdgeLiteral
        (orderFortyNineH5LowVertex y) (orderFortyNineH5HighVertex w), ?_, ?_⟩
    · simp only [orderFortyNineH5SupportUnitLiteral]
      rw [if_neg hbit]
      simp
    · rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
        hsupp', hbitFalse]
      rfl

theorem orderFortyNineH5HighHighFixedClauses_bounded :
    dimacsFormulaBounded 1176 orderFortyNineH5HighHighFixedClauses := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH5HighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  exact orderFortyNineNegEdgeLiteral_bounded _ _
    (fun heq => orderFortyNineH5HighPairs_ne ab hab
      (orderFortyNineH5HighVertex_injective heq))

theorem orderFortyNineH5HighLowFixedClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176
      (orderFortyNineH5HighLowFixedClauses masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH5HighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  unfold orderFortyNineH5SupportUnitLiteral
  split
  · exact orderFortyNineEdgeLiteral_bounded _ _
      (orderFortyNineH5LowVertex_ne_highVertex y w)
  · exact orderFortyNineNegEdgeLiteral_bounded _ _
      (orderFortyNineH5LowVertex_ne_highVertex y w)

theorem orderFortyNineH5FixedClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176 (orderFortyNineH5FixedClauses masks) :=
  dimacsFormulaBounded_append orderFortyNineH5HighHighFixedClauses_bounded
    (orderFortyNineH5HighLowFixedClauses_bounded masks)

theorem orderFortyNineH5FixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hhigh : ∀ a b : Fin 5, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH5HighVertex a)
        (orderFortyNineH5HighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH5FixedClauses masks) :=
  dimacsFormulaSatisfied_append
    (orderFortyNineH5HighHighFixedClauses_satisfied edges hhigh)
    (orderFortyNineH5HighLowFixedClauses_satisfied hc)

theorem orderFortyNineH5FixedClauses_satisfied_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hzero : OrderFortyNineH5HighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH5FixedClauses masks) :=
  orderFortyNineH5FixedClauses_satisfied hc
    (orderFortyNineH5HighHigh_independent_of_zero_masks hc hzero)

theorem orderFortyNineH5LowVertex_injective :
    Function.Injective orderFortyNineH5LowVertex := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp [orderFortyNineH5LowVertex] at hval
  omega

theorem orderFortyNineH5LowVertex_surjective
    (k : Fin 49) (hk : 5 ≤ k.val) :
    ∃ y : Fin 44, orderFortyNineH5LowVertex y = k := by
  refine ⟨⟨k.val - 5, by omega⟩, ?_⟩
  apply Fin.ext
  simp [orderFortyNineH5LowVertex]
  omega

theorem orderFortyNineH5PartitionClause_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hzero : OrderFortyNineH5HighMasksZero masks)
    (y : Fin 44) (w : Fin 5) :
    dimacsClauseSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH5PartitionClause masks y w) := by
  let vy := orderFortyNineH5LowVertex y
  let candidates := Finset.univ.filter fun k =>
    orderFortyNineBitAdj edges vy k &&
      (orderFortyNineSupportMask masks k).getLsbD w.val
  have hcard : candidates.card = 1 := by
    let w9 : Fin 9 := Fin.castLE (by omega) w
    have hw9 : w9.val < 5 := by simp [w9]
    simpa [candidates, w9] using
      hc.2.2.2.2.2 vy (by simp [vy, orderFortyNineH5LowVertex]) w9 hw9
  have hpos : 0 < candidates.card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  have hkand := (Finset.mem_filter.mp hk).2
  simp only [Bool.and_eq_true] at hkand
  have hadj : orderFortyNineBitAdj edges vy k = true :=
    hkand.1
  have hsupport :
      (orderFortyNineSupportMask masks k).getLsbD w.val = true :=
    hkand.2
  have hkLow : 5 ≤ k.val := by
    by_contra hnot
    have hkHigh : k.val < 5 := by omega
    let a : Fin 5 := ⟨k.val, hkHigh⟩
    have hka : orderFortyNineH5HighVertex a = k := by
      apply Fin.ext
      rfl
    have hz := hzero a w
    rw [hka] at hz
    rw [hz] at hsupport
    contradiction
  obtain ⟨x, rfl⟩ := orderFortyNineH5LowVertex_surjective k hkLow
  have hxy : x ≠ y := by
    intro heq
    subst x
    simp [vy, orderFortyNineBitAdj] at hadj
  have hxmem : orderFortyNineH5LowVertex x ∈
      orderFortyNineH5PartitionNeighbors masks w := by
    simp only [orderFortyNineH5PartitionNeighbors, List.mem_filter,
      List.mem_map, List.mem_finRange, true_and]
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact hsupport
  refine ⟨orderFortyNineEdgeLiteral vy (orderFortyNineH5LowVertex x), ?_, ?_⟩
  · simp only [orderFortyNineH5PartitionClause, List.mem_map, List.mem_filter]
    have hneLow : orderFortyNineH5LowVertex x ≠ orderFortyNineH5LowVertex y :=
      fun heq => hxy (orderFortyNineH5LowVertex_injective heq)
    exact ⟨orderFortyNineH5LowVertex x, ⟨hxmem, by
      simpa only [decide_eq_true_eq] using hneLow⟩, rfl⟩
  · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges vy
      (orderFortyNineH5LowVertex x) (by
        exact fun heq => hxy (orderFortyNineH5LowVertex_injective heq.symm))]
    exact hadj

theorem orderFortyNineH5PartitionClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hzero : OrderFortyNineH5HighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH5PartitionClauses masks) := by
  intro clause hclause
  simp only [orderFortyNineH5PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  exact orderFortyNineH5PartitionClause_satisfied hc hzero y w

theorem orderFortyNineH5PartitionClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176 (orderFortyNineH5PartitionClauses masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH5PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineH5PartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  have hxyDec := (List.mem_filter.mp hx).2
  have hxy : x ≠ orderFortyNineH5LowVertex y :=
    of_decide_eq_true hxyDec
  exact orderFortyNineEdgeLiteral_bounded _ _ hxy.symm

theorem orderFortyNineH5C4Clauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineC4Clauses := by
  intro clause hclause
  simp only [orderFortyNineC4Clauses, List.mem_toArray, List.mem_map] at hclause
  obtain ⟨q, hq, rfl⟩ := hclause
  exact orderFortyNineC4Clause_satisfied hc.2.2.2.1 q hq

structure OrderFortyNineH5CnfSegmentsSatisfied
    (masks : Array Nat) (val : DimacsValuation) : Prop where
  fixed : dimacsFormulaSatisfied val (orderFortyNineH5FixedClauses masks)
  c4 : dimacsFormulaSatisfied val orderFortyNineC4Clauses
  degree : dimacsFormulaSatisfied val (orderFortyNineDegreeBlocks 5).clauses
  partition : dimacsFormulaSatisfied val (orderFortyNineH5PartitionClauses masks)

theorem orderFortyNineH5CnfSegments_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hzero : OrderFortyNineH5HighMasksZero masks) :
    ∃ val : DimacsValuation,
      OrderFortyNineH5CnfSegmentsSatisfied masks val ∧
      ∀ id, id ≤ 1176 → val id = orderFortyNineDimacsEdgeVal edges id := by
  obtain ⟨val, hdegreeSat, hdegreeBounded, htop, hagree⟩ :=
    orderFortyNineDegreeBlocks_invariant hc
  refine ⟨val, ?_, hagree⟩
  constructor
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH5FixedClauses_satisfied_of_zero_masks hc hzero)
      (orderFortyNineH5FixedClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH5C4Clauses_satisfied hc)
      orderFortyNineC4Clauses_bounded
      (fun id hid => (hagree id hid).symm)
  · exact hdegreeSat
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH5PartitionClauses_satisfied hc hzero)
      (orderFortyNineH5PartitionClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)

theorem orderFortyNineH5FixedClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineH5FixedClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH5FixedClauses, Array.mem_append] at hclause
  rcases hclause with hhigh | hlow
  · simp only [orderFortyNineH5HighHighFixedClauses, List.mem_toArray,
      List.mem_map] at hhigh
    obtain ⟨ab, hab, rfl⟩ := hhigh
    simp only [List.mem_singleton] at hlit
    subst lit
    simp [orderFortyNineEdgeLiteral] <;> omega
  · simp only [orderFortyNineH5HighLowFixedClauses, List.mem_toArray,
      List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hlow
    obtain ⟨y, w, rfl⟩ := hlow
    simp only [List.mem_singleton] at hlit
    subst lit
    unfold orderFortyNineH5SupportUnitLiteral
    split <;> simp [orderFortyNineEdgeLiteral] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem orderFortyNineDegreeBlocks_five_nonzero :
    ∀ clause ∈ (orderFortyNineDegreeBlocks 5).clauses,
      DimacsClauseNonzero clause := by
  have hcheck :
      (orderFortyNineDegreeBlocks 5).clauses.all fun clause =>
        clause.all fun lit => lit != 0 := by
    native_decide
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

theorem orderFortyNineH5PartitionClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineH5PartitionClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH5PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineH5PartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  simp [orderFortyNineEdgeLiteral] <;> omega

structure OrderFortyNineH5CnfCoveredBySegments
    (masks : Array Nat) (cnf : CNF Nat) : Prop where
  covered : ∀ clause ∈ cnf.clauses,
    (∃ source ∈ orderFortyNineH5FixedClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineC4Clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ (orderFortyNineDegreeBlocks 5).clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineH5PartitionClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source)

theorem orderFortyNineGeneratedH5SatCnf_covered (masks : Array Nat) :
    OrderFortyNineH5CnfCoveredBySegments masks
      (orderFortyNineGeneratedH5SatCnf masks) := by
  constructor
  intro clause hclause
  simp only [orderFortyNineGeneratedH5SatCnf, Array.mem_append,
    dimacsFormulaToSatClauses, Array.mem_map] at hclause
  rcases hclause with ((hfixed | hc4) | hdegree) | hpartition
  · obtain ⟨source, hsource, rfl⟩ := hfixed
    exact Or.inl ⟨source, hsource,
      orderFortyNineH5FixedClauses_nonzero masks source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hc4
    exact Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineC4Clauses_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hdegree
    exact Or.inr <| Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineDegreeBlocks_five_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hpartition
    exact Or.inr <| Or.inr <| Or.inr ⟨source, hsource,
      orderFortyNineH5PartitionClauses_nonzero masks source hsource, rfl⟩

theorem sat_of_orderFortyNineH5CnfSegmentsSatisfied_of_covered
    {masks : Array Nat} {cnf : CNF Nat} {val : DimacsValuation}
    (hsat : OrderFortyNineH5CnfSegmentsSatisfied masks val)
    (hcovered : OrderFortyNineH5CnfCoveredBySegments masks cnf) :
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

theorem false_of_orderFortyNine_generated_h5_lrat
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hzero : OrderFortyNineH5HighMasksZero masks)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedH5SatCnf masks)) : False := by
  obtain ⟨val, hsegments, _⟩ := orderFortyNineH5CnfSegments_satisfied hc hzero
  have hsat := sat_of_orderFortyNineH5CnfSegmentsSatisfied_of_covered
    hsegments (orderFortyNineGeneratedH5SatCnf_covered masks)
  have hunsat := Std.Tactic.BVDecide.LRAT.check_sound proof _ hcheck
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85
