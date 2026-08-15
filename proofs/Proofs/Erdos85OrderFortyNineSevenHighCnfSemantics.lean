import Proofs.Erdos85OrderFortyNineSevenHighCnf

/-! # Semantic bridge for the exact h=7 order-49 CNF -/

namespace Erdos85

open Std Sat

theorem orderFortyNineH7HighVertex_injective :
    Function.Injective orderFortyNineH7HighVertex := by
  intro a b hab
  apply Fin.ext
  simpa [orderFortyNineH7HighVertex] using congrArg Fin.val hab

theorem orderFortyNineH7LowVertex_ne_highVertex (y : Fin 42) (w : Fin 7) :
    orderFortyNineH7LowVertex y ≠ orderFortyNineH7HighVertex w := by
  intro heq
  have := congrArg Fin.val heq
  simp [orderFortyNineH7LowVertex, orderFortyNineH7HighVertex] at this
  omega

theorem orderFortyNineH7HighPairs_ne (ab : Fin 7 × Fin 7)
    (hab : ab ∈ orderFortyNineH7HighPairs) : ab.1 ≠ ab.2 := by
  native_decide +revert

theorem orderFortyNineH7HighHighFixedClauses_satisfied
    (edges : BitVec 1176)
    (hhigh : ∀ a b : Fin 7, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH7HighVertex a)
        (orderFortyNineH7HighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineH7HighHighFixedClauses := by
  intro clause hclause
  simp only [orderFortyNineH7HighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  rcases ab with ⟨a, b⟩
  have hab' : a ≠ b := orderFortyNineH7HighPairs_ne (a, b) hab
  have hne : orderFortyNineH7HighVertex a ≠ orderFortyNineH7HighVertex b := by
    exact fun heq => hab' (orderFortyNineH7HighVertex_injective heq)
  refine ⟨-orderFortyNineEdgeLiteral
      (orderFortyNineH7HighVertex a) (orderFortyNineH7HighVertex b), by simp, ?_⟩
  rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
    hhigh a b hab']
  rfl

theorem orderFortyNineH7HighHigh_independent_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges)
    (hzero : OrderFortyNineH7HighMasksZero masks) :
    ∀ a b : Fin 7, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH7HighVertex a)
        (orderFortyNineH7HighVertex b) = false := by
  intro a b hab
  let b9 : Fin 9 := Fin.castLE (by omega) b
  have hb9 : b9.val < 7 := by simp [b9]
  have hsupp := hc.2.2.2.2.1 (orderFortyNineH7HighVertex a) b9 hb9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineH7HighVertex a)
          (orderFortyNineH7HighVertex b) =
        (orderFortyNineSupportMask masks
          (orderFortyNineH7HighVertex a)).getLsbD b.val := by
    simpa [b9, orderFortyNineH7HighVertex] using hsupp
  rw [hsupp', hzero a b]

theorem orderFortyNineH7HighLowFixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH7HighLowFixedClauses masks) := by
  intro clause hclause
  simp only [orderFortyNineH7HighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  have hne := orderFortyNineH7LowVertex_ne_highVertex y w
  let w9 : Fin 9 := Fin.castLE (by omega) w
  have hw9 : w9.val < 7 := by simp [w9]
  have hsupp := hc.2.2.2.2.1 (orderFortyNineH7LowVertex y) w9 hw9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineH7LowVertex y)
          (orderFortyNineH7HighVertex w) =
        (orderFortyNineSupportMask masks (orderFortyNineH7LowVertex y)).getLsbD
          w.val := by
    simpa [w9, orderFortyNineH7HighVertex] using hsupp
  by_cases hbit :
      (orderFortyNineSupportMask masks (orderFortyNineH7LowVertex y)).getLsbD
        w.val = true
  · refine ⟨orderFortyNineEdgeLiteral
        (orderFortyNineH7LowVertex y) (orderFortyNineH7HighVertex w), ?_, ?_⟩
    · simp [orderFortyNineH7SupportUnitLiteral, hbit]
    · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne, hsupp', hbit]
  · have hbitFalse :
        (orderFortyNineSupportMask masks (orderFortyNineH7LowVertex y)).getLsbD
          w.val = false := Bool.eq_false_of_not_eq_true hbit
    refine ⟨-orderFortyNineEdgeLiteral
        (orderFortyNineH7LowVertex y) (orderFortyNineH7HighVertex w), ?_, ?_⟩
    · simp only [orderFortyNineH7SupportUnitLiteral]
      rw [if_neg hbit]
      simp
    · rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
        hsupp', hbitFalse]
      rfl

theorem orderFortyNineH7HighHighFixedClauses_bounded :
    dimacsFormulaBounded 1176 orderFortyNineH7HighHighFixedClauses := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH7HighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  exact orderFortyNineNegEdgeLiteral_bounded _ _
    (fun heq => orderFortyNineH7HighPairs_ne ab hab
      (orderFortyNineH7HighVertex_injective heq))

theorem orderFortyNineH7HighLowFixedClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176
      (orderFortyNineH7HighLowFixedClauses masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH7HighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  unfold orderFortyNineH7SupportUnitLiteral
  split
  · exact orderFortyNineEdgeLiteral_bounded _ _
      (orderFortyNineH7LowVertex_ne_highVertex y w)
  · exact orderFortyNineNegEdgeLiteral_bounded _ _
      (orderFortyNineH7LowVertex_ne_highVertex y w)

theorem orderFortyNineH7FixedClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176 (orderFortyNineH7FixedClauses masks) :=
  dimacsFormulaBounded_append orderFortyNineH7HighHighFixedClauses_bounded
    (orderFortyNineH7HighLowFixedClauses_bounded masks)

theorem orderFortyNineH7FixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges)
    (hhigh : ∀ a b : Fin 7, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineH7HighVertex a)
        (orderFortyNineH7HighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH7FixedClauses masks) :=
  dimacsFormulaSatisfied_append
    (orderFortyNineH7HighHighFixedClauses_satisfied edges hhigh)
    (orderFortyNineH7HighLowFixedClauses_satisfied hc)

theorem orderFortyNineH7FixedClauses_satisfied_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges)
    (hzero : OrderFortyNineH7HighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH7FixedClauses masks) :=
  orderFortyNineH7FixedClauses_satisfied hc
    (orderFortyNineH7HighHigh_independent_of_zero_masks hc hzero)

theorem orderFortyNineH7LowVertex_injective :
    Function.Injective orderFortyNineH7LowVertex := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp [orderFortyNineH7LowVertex] at hval
  omega

theorem orderFortyNineH7LowVertex_surjective
    (k : Fin 49) (hk : 7 ≤ k.val) :
    ∃ y : Fin 42, orderFortyNineH7LowVertex y = k := by
  refine ⟨⟨k.val - 7, by omega⟩, ?_⟩
  apply Fin.ext
  simp [orderFortyNineH7LowVertex]
  omega

theorem orderFortyNineH7PartitionClause_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges)
    (hzero : OrderFortyNineH7HighMasksZero masks)
    (y : Fin 42) (w : Fin 7) :
    dimacsClauseSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH7PartitionClause masks y w) := by
  let vy := orderFortyNineH7LowVertex y
  let candidates := Finset.univ.filter fun k =>
    orderFortyNineBitAdj edges vy k &&
      (orderFortyNineSupportMask masks k).getLsbD w.val
  have hcard : candidates.card = 1 := by
    let w9 : Fin 9 := Fin.castLE (by omega) w
    have hw9 : w9.val < 7 := by simp [w9]
    simpa [candidates, w9] using
      hc.2.2.2.2.2 vy (by simp [vy, orderFortyNineH7LowVertex]) w9 hw9
  have hpos : 0 < candidates.card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  have hkand := (Finset.mem_filter.mp hk).2
  simp only [Bool.and_eq_true] at hkand
  have hadj : orderFortyNineBitAdj edges vy k = true :=
    hkand.1
  have hsupport :
      (orderFortyNineSupportMask masks k).getLsbD w.val = true :=
    hkand.2
  have hkLow : 7 ≤ k.val := by
    by_contra hnot
    have hkHigh : k.val < 7 := by omega
    let a : Fin 7 := ⟨k.val, hkHigh⟩
    have hka : orderFortyNineH7HighVertex a = k := by
      apply Fin.ext
      rfl
    have hz := hzero a w
    rw [hka] at hz
    rw [hz] at hsupport
    contradiction
  obtain ⟨x, rfl⟩ := orderFortyNineH7LowVertex_surjective k hkLow
  have hxy : x ≠ y := by
    intro heq
    subst x
    simp [vy, orderFortyNineBitAdj] at hadj
  have hxmem : orderFortyNineH7LowVertex x ∈
      orderFortyNineH7PartitionNeighbors masks w := by
    simp only [orderFortyNineH7PartitionNeighbors, List.mem_filter,
      List.mem_map, List.mem_finRange, true_and]
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact hsupport
  refine ⟨orderFortyNineEdgeLiteral vy (orderFortyNineH7LowVertex x), ?_, ?_⟩
  · simp only [orderFortyNineH7PartitionClause, List.mem_map, List.mem_filter]
    have hneLow : orderFortyNineH7LowVertex x ≠ orderFortyNineH7LowVertex y :=
      fun heq => hxy (orderFortyNineH7LowVertex_injective heq)
    exact ⟨orderFortyNineH7LowVertex x, ⟨hxmem, by
      simpa only [decide_eq_true_eq] using hneLow⟩, rfl⟩
  · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges vy
      (orderFortyNineH7LowVertex x) (by
        exact fun heq => hxy (orderFortyNineH7LowVertex_injective heq.symm))]
    exact hadj

theorem orderFortyNineH7PartitionClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges)
    (hzero : OrderFortyNineH7HighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineH7PartitionClauses masks) := by
  intro clause hclause
  simp only [orderFortyNineH7PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  exact orderFortyNineH7PartitionClause_satisfied hc hzero y w

theorem orderFortyNineH7PartitionClauses_bounded (masks : Array Nat) :
    dimacsFormulaBounded 1176 (orderFortyNineH7PartitionClauses masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH7PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineH7PartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  have hxyDec := (List.mem_filter.mp hx).2
  have hxy : x ≠ orderFortyNineH7LowVertex y :=
    of_decide_eq_true hxyDec
  exact orderFortyNineEdgeLiteral_bounded _ _ hxy.symm

theorem orderFortyNineH7C4Clauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineC4Clauses := by
  intro clause hclause
  simp only [orderFortyNineC4Clauses, List.mem_toArray, List.mem_map] at hclause
  obtain ⟨q, hq, rfl⟩ := hclause
  exact orderFortyNineC4Clause_satisfied hc.2.2.2.1 q hq

structure OrderFortyNineH7CnfSegmentsSatisfied
    (masks : Array Nat) (val : DimacsValuation) : Prop where
  fixed : dimacsFormulaSatisfied val (orderFortyNineH7FixedClauses masks)
  c4 : dimacsFormulaSatisfied val orderFortyNineC4Clauses
  degree : dimacsFormulaSatisfied val (orderFortyNineDegreeBlocks 7).clauses
  partition : dimacsFormulaSatisfied val (orderFortyNineH7PartitionClauses masks)

theorem orderFortyNineH7CnfSegments_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges)
    (hzero : OrderFortyNineH7HighMasksZero masks) :
    ∃ val : DimacsValuation,
      OrderFortyNineH7CnfSegmentsSatisfied masks val ∧
      ∀ id, id ≤ 1176 → val id = orderFortyNineDimacsEdgeVal edges id := by
  obtain ⟨val, hdegreeSat, hdegreeBounded, htop, hagree⟩ :=
    orderFortyNineDegreeBlocks_invariant hc
  refine ⟨val, ?_, hagree⟩
  constructor
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH7FixedClauses_satisfied_of_zero_masks hc hzero)
      (orderFortyNineH7FixedClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH7C4Clauses_satisfied hc)
      orderFortyNineC4Clauses_bounded
      (fun id hid => (hagree id hid).symm)
  · exact hdegreeSat
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineH7PartitionClauses_satisfied hc hzero)
      (orderFortyNineH7PartitionClauses_bounded masks)
      (fun id hid => (hagree id hid).symm)

theorem orderFortyNineH7FixedClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineH7FixedClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH7FixedClauses, Array.mem_append] at hclause
  rcases hclause with hhigh | hlow
  · simp only [orderFortyNineH7HighHighFixedClauses, List.mem_toArray,
      List.mem_map] at hhigh
    obtain ⟨ab, hab, rfl⟩ := hhigh
    simp only [List.mem_singleton] at hlit
    subst lit
    simp [orderFortyNineEdgeLiteral] <;> omega
  · simp only [orderFortyNineH7HighLowFixedClauses, List.mem_toArray,
      List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hlow
    obtain ⟨y, w, rfl⟩ := hlow
    simp only [List.mem_singleton] at hlit
    subst lit
    unfold orderFortyNineH7SupportUnitLiteral
    split <;> simp [orderFortyNineEdgeLiteral] <;> omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem orderFortyNineDegreeBlocks_seven_nonzero :
    ∀ clause ∈ (orderFortyNineDegreeBlocks 7).clauses,
      DimacsClauseNonzero clause := by
  have hcheck :
      (orderFortyNineDegreeBlocks 7).clauses.all fun clause =>
        clause.all fun lit => lit != 0 := by
    native_decide
  simp only [Array.all_eq_true] at hcheck
  intro clause hclause lit hlit
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hclause
  have hclauseCheck := hcheck i hi
  simp only [List.all_eq_true] at hclauseCheck
  have hlitCheck := hclauseCheck lit hlit
  simpa using hlitCheck

theorem orderFortyNineH7PartitionClauses_nonzero (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineH7PartitionClauses masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineH7PartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineH7PartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  simp [orderFortyNineEdgeLiteral] <;> omega

structure OrderFortyNineH7CnfCoveredBySegments
    (masks : Array Nat) (cnf : CNF Nat) : Prop where
  covered : ∀ clause ∈ cnf.clauses,
    (∃ source ∈ orderFortyNineH7FixedClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineC4Clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ (orderFortyNineDegreeBlocks 7).clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineH7PartitionClauses masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source)

theorem orderFortyNineGeneratedH7SatCnf_covered (masks : Array Nat) :
    OrderFortyNineH7CnfCoveredBySegments masks
      (orderFortyNineGeneratedH7SatCnf masks) := by
  constructor
  intro clause hclause
  simp only [orderFortyNineGeneratedH7SatCnf, Array.mem_append,
    dimacsFormulaToSatClauses, Array.mem_map] at hclause
  rcases hclause with ((hfixed | hc4) | hdegree) | hpartition
  · obtain ⟨source, hsource, rfl⟩ := hfixed
    exact Or.inl ⟨source, hsource,
      orderFortyNineH7FixedClauses_nonzero masks source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hc4
    exact Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineC4Clauses_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hdegree
    exact Or.inr <| Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineDegreeBlocks_seven_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hpartition
    exact Or.inr <| Or.inr <| Or.inr ⟨source, hsource,
      orderFortyNineH7PartitionClauses_nonzero masks source hsource, rfl⟩

theorem sat_of_orderFortyNineH7CnfSegmentsSatisfied_of_covered
    {masks : Array Nat} {cnf : CNF Nat} {val : DimacsValuation}
    (hsat : OrderFortyNineH7CnfSegmentsSatisfied masks val)
    (hcovered : OrderFortyNineH7CnfCoveredBySegments masks cnf) :
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

theorem false_of_orderFortyNine_generated_h7_lrat
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges)
    (hzero : OrderFortyNineH7HighMasksZero masks)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedH7SatCnf masks)) : False := by
  obtain ⟨val, hsegments, _⟩ := orderFortyNineH7CnfSegments_satisfied hc hzero
  have hsat := sat_of_orderFortyNineH7CnfSegmentsSatisfied_of_covered
    hsegments (orderFortyNineGeneratedH7SatCnf_covered masks)
  have hunsat := Std.Tactic.BVDecide.LRAT.check_sound proof _ hcheck
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85
