import Proofs.Erdos85OrderFortyNineVariableHighCnf
import Proofs.Erdos85OrderFortyNineDegreeBlocksNonzero

/-! # Semantics of the variable-high order-49 CNF -/

namespace Erdos85

open Std Sat

theorem orderFortyNineVariableHighVertex_injective
    (h : OrderFortyNineHighCount) :
    Function.Injective (orderFortyNineVariableHighVertex h) := by
  intro a b hab
  apply Fin.ext
  simpa [orderFortyNineVariableHighVertex] using congrArg Fin.val hab

theorem orderFortyNineVariableLowVertex_ne_highVertex
    (h : OrderFortyNineHighCount) (y : Fin (49 - h.val)) (w : Fin h.val) :
    orderFortyNineVariableLowVertex h y ≠
      orderFortyNineVariableHighVertex h w := by
  intro heq
  have := congrArg Fin.val heq
  simp [orderFortyNineVariableLowVertex,
    orderFortyNineVariableHighVertex] at this
  omega

theorem orderFortyNineVariableHighPairs_ne
    (h : OrderFortyNineHighCount) (ab : Fin h.val × Fin h.val)
    (hab : ab ∈ orderFortyNineVariableHighPairs h) : ab.1 ≠ ab.2 := by
  simp only [orderFortyNineVariableHighPairs, List.mem_flatMap] at hab
  obtain ⟨a, _, hab⟩ := hab
  simp only [List.mem_map] at hab
  obtain ⟨b, hb, heq⟩ := hab
  have hab : a.val < b.val := by
    have := (List.mem_filter.mp hb).2
    simpa only [decide_eq_true_eq] using this
  have ha : a = ab.1 := congrArg Prod.fst heq
  have hb : b = ab.2 := congrArg Prod.snd heq
  intro heqab
  rw [ha, hb, heqab] at hab
  omega

theorem orderFortyNineVariableHighHighFixedClauses_satisfied
    {h : OrderFortyNineHighCount} (hh : h.val ≤ 9)
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h.val masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineVariableHighHighFixedClauses h masks) := by
  intro clause hclause
  simp only [orderFortyNineVariableHighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  rcases ab with ⟨a, b⟩
  have hab' : a ≠ b := orderFortyNineVariableHighPairs_ne h (a, b) hab
  have hne : orderFortyNineVariableHighVertex h a ≠
      orderFortyNineVariableHighVertex h b :=
    fun heq => hab' (orderFortyNineVariableHighVertex_injective h heq)
  let b9 : Fin 9 := ⟨b.val, by omega⟩
  have hb9 : b9.val < h.val := by simp [b9]
  have hsupp := hc.2.2.2.2.1
    (orderFortyNineVariableHighVertex h a) b9 hb9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineVariableHighVertex h a)
          (orderFortyNineVariableHighVertex h b) =
        (orderFortyNineSupportMask masks
          (orderFortyNineVariableHighVertex h a)).getLsbD b.val := by
    simpa [b9, orderFortyNineVariableHighVertex] using hsupp
  by_cases hbit :
      (orderFortyNineSupportMask masks
        (orderFortyNineVariableHighVertex h a)).getLsbD b.val = true
  · refine ⟨orderFortyNineEdgeLiteral
        (orderFortyNineVariableHighVertex h a)
        (orderFortyNineVariableHighVertex h b), ?_, ?_⟩
    · simp [orderFortyNineVariableHighHighUnitLiteral, hbit]
    · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne,
        hsupp', hbit]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    refine ⟨-orderFortyNineEdgeLiteral
        (orderFortyNineVariableHighVertex h a)
        (orderFortyNineVariableHighVertex h b), ?_, ?_⟩
    · simp only [orderFortyNineVariableHighHighUnitLiteral]
      rw [if_neg hbit]
      simp
    · rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
        hsupp', hbitFalse]
      rfl

theorem orderFortyNineVariableHighLowFixedClauses_satisfied
    {h : OrderFortyNineHighCount} (hh : h.val ≤ 9)
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h.val masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineVariableHighLowFixedClauses h masks) := by
  intro clause hclause
  simp only [orderFortyNineVariableHighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  have hne := orderFortyNineVariableLowVertex_ne_highVertex h y w
  let w9 : Fin 9 := ⟨w.val, by omega⟩
  have hw9 : w9.val < h.val := by simp [w9]
  have hsupp := hc.2.2.2.2.1
    (orderFortyNineVariableLowVertex h y) w9 hw9
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineVariableLowVertex h y)
          (orderFortyNineVariableHighVertex h w) =
        (orderFortyNineSupportMask masks
          (orderFortyNineVariableLowVertex h y)).getLsbD w.val := by
    simpa [w9, orderFortyNineVariableHighVertex] using hsupp
  by_cases hbit :
      (orderFortyNineSupportMask masks
        (orderFortyNineVariableLowVertex h y)).getLsbD w.val = true
  · refine ⟨orderFortyNineEdgeLiteral
        (orderFortyNineVariableLowVertex h y)
        (orderFortyNineVariableHighVertex h w), ?_, ?_⟩
    · simp [orderFortyNineVariableSupportUnitLiteral, hbit]
    · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne,
        hsupp', hbit]
  · have hbitFalse := Bool.eq_false_of_not_eq_true hbit
    refine ⟨-orderFortyNineEdgeLiteral
        (orderFortyNineVariableLowVertex h y)
        (orderFortyNineVariableHighVertex h w), ?_, ?_⟩
    · simp only [orderFortyNineVariableSupportUnitLiteral]
      rw [if_neg hbit]
      simp
    · rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
        hsupp', hbitFalse]
      rfl

theorem orderFortyNineVariableFixedClauses_satisfied
    {h : OrderFortyNineHighCount} (hh : h.val ≤ 9)
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h.val masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineVariableFixedClauses h masks) :=
  dimacsFormulaSatisfied_append
    (orderFortyNineVariableHighHighFixedClauses_satisfied hh hc)
    (orderFortyNineVariableHighLowFixedClauses_satisfied hh hc)

theorem orderFortyNineVariableHighHighFixedClauses_bounded
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    dimacsFormulaBounded 1176
      (orderFortyNineVariableHighHighFixedClauses h masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineVariableHighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  unfold orderFortyNineVariableHighHighUnitLiteral
  split
  · exact orderFortyNineEdgeLiteral_bounded _ _
      (fun heq => orderFortyNineVariableHighPairs_ne h ab hab
        (orderFortyNineVariableHighVertex_injective h heq))
  · exact orderFortyNineNegEdgeLiteral_bounded _ _
      (fun heq => orderFortyNineVariableHighPairs_ne h ab hab
        (orderFortyNineVariableHighVertex_injective h heq))

theorem orderFortyNineVariableHighLowFixedClauses_bounded
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    dimacsFormulaBounded 1176
      (orderFortyNineVariableHighLowFixedClauses h masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineVariableHighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [List.mem_singleton] at hlit
  subst lit
  unfold orderFortyNineVariableSupportUnitLiteral
  split
  · exact orderFortyNineEdgeLiteral_bounded _ _
      (orderFortyNineVariableLowVertex_ne_highVertex h y w)
  · exact orderFortyNineNegEdgeLiteral_bounded _ _
      (orderFortyNineVariableLowVertex_ne_highVertex h y w)

theorem orderFortyNineVariableFixedClauses_bounded
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    dimacsFormulaBounded 1176
      (orderFortyNineVariableFixedClauses h masks) :=
  dimacsFormulaBounded_append
    (orderFortyNineVariableHighHighFixedClauses_bounded h masks)
    (orderFortyNineVariableHighLowFixedClauses_bounded h masks)

/-- A mask-level condition ensuring that the unique common-neighbor witness
for a low vertex and a high label cannot itself be high. -/
def OrderFortyNineVariableHighPartitionExcluded
    (h : OrderFortyNineHighCount) (masks : Array Nat) : Prop :=
  ∀ (y : Fin (49 - h.val)) (a w : Fin h.val),
    (orderFortyNineSupportMask masks
      (orderFortyNineVariableHighVertex h a)).getLsbD w.val = true →
    (orderFortyNineSupportMask masks
      (orderFortyNineVariableLowVertex h y)).getLsbD a.val = false

theorem orderFortyNineVariableLowVertex_injective
    (h : OrderFortyNineHighCount) :
    Function.Injective (orderFortyNineVariableLowVertex h) := by
  intro x y hxy
  apply Fin.ext
  have hval := congrArg Fin.val hxy
  simp [orderFortyNineVariableLowVertex] at hval
  omega

theorem orderFortyNineVariableLowVertex_surjective
    (h : OrderFortyNineHighCount) (k : Fin 49) (hk : h.val ≤ k.val) :
    ∃ y : Fin (49 - h.val), orderFortyNineVariableLowVertex h y = k := by
  refine ⟨⟨k.val - h.val, by omega⟩, ?_⟩
  apply Fin.ext
  simp [orderFortyNineVariableLowVertex]
  omega

theorem orderFortyNineVariablePartitionClause_satisfied
    {h : OrderFortyNineHighCount} (hh : h.val ≤ 9)
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h.val masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded h masks)
    (y : Fin (49 - h.val)) (w : Fin h.val) :
    dimacsClauseSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineVariablePartitionClause h masks y w) := by
  let vy := orderFortyNineVariableLowVertex h y
  let candidates := Finset.univ.filter fun k =>
    orderFortyNineBitAdj edges vy k &&
      (orderFortyNineSupportMask masks k).getLsbD w.val
  have hcard : candidates.card = 1 := by
    let w9 : Fin 9 := ⟨w.val, by omega⟩
    have hw9 : w9.val < h.val := by simp [w9]
    simpa [candidates, w9] using
      hc.2.2.2.2.2 vy (by simp [vy, orderFortyNineVariableLowVertex]) w9 hw9
  have hpos : 0 < candidates.card := by omega
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  have hkand := (Finset.mem_filter.mp hk).2
  simp only [Bool.and_eq_true] at hkand
  have hadj : orderFortyNineBitAdj edges vy k = true := hkand.1
  have hsupport :
      (orderFortyNineSupportMask masks k).getLsbD w.val = true := hkand.2
  have hkLow : h.val ≤ k.val := by
    by_contra hnot
    have hkHigh : k.val < h.val := by omega
    let a : Fin h.val := ⟨k.val, hkHigh⟩
    have hka : orderFortyNineVariableHighVertex h a = k := by
      apply Fin.ext
      rfl
    have hhighSupport :
        (orderFortyNineSupportMask masks
          (orderFortyNineVariableHighVertex h a)).getLsbD w.val = true := by
      simpa [hka] using hsupport
    have hlowFalse := hexcluded y a w hhighSupport
    let a9 : Fin 9 := ⟨a.val, by omega⟩
    have ha9 : a9.val < h.val := by simp [a9]
    have hsupp := hc.2.2.2.2.1 vy a9 ha9
    have hsupp' :
        orderFortyNineBitAdj edges vy
            (orderFortyNineVariableHighVertex h a) =
          (orderFortyNineSupportMask masks vy).getLsbD a.val := by
      simpa [a9, orderFortyNineVariableHighVertex] using hsupp
    have hlowTrue :
        (orderFortyNineSupportMask masks vy).getLsbD a.val = true := by
      rw [← hsupp', hka]
      exact hadj
    rw [hlowFalse] at hlowTrue
    contradiction
  obtain ⟨x, rfl⟩ := orderFortyNineVariableLowVertex_surjective h k hkLow
  have hxy : x ≠ y := by
    intro heq
    subst x
    simp [vy, orderFortyNineBitAdj] at hadj
  have hxmem : orderFortyNineVariableLowVertex h x ∈
      orderFortyNineVariablePartitionNeighbors h masks w := by
    simp only [orderFortyNineVariablePartitionNeighbors, List.mem_filter,
      List.mem_map, List.mem_finRange, true_and]
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact hsupport
  refine ⟨orderFortyNineEdgeLiteral vy
      (orderFortyNineVariableLowVertex h x), ?_, ?_⟩
  · simp only [orderFortyNineVariablePartitionClause, List.mem_map,
      List.mem_filter]
    have hneLow : orderFortyNineVariableLowVertex h x ≠
        orderFortyNineVariableLowVertex h y :=
      fun heq => hxy (orderFortyNineVariableLowVertex_injective h heq)
    exact ⟨orderFortyNineVariableLowVertex h x, ⟨hxmem, by
      simpa only [decide_eq_true_eq] using hneLow⟩, rfl⟩
  · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges vy
      (orderFortyNineVariableLowVertex h x) (by
        exact fun heq => hxy
          (orderFortyNineVariableLowVertex_injective h heq.symm))]
    exact hadj

theorem orderFortyNineVariablePartitionClauses_satisfied
    {h : OrderFortyNineHighCount} (hh : h.val ≤ 9)
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h.val masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded h masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineVariablePartitionClauses h masks) := by
  intro clause hclause
  simp only [orderFortyNineVariablePartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  exact orderFortyNineVariablePartitionClause_satisfied hh hc hexcluded y w

theorem orderFortyNineVariablePartitionClauses_bounded
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    dimacsFormulaBounded 1176
      (orderFortyNineVariablePartitionClauses h masks) := by
  intro clause hclause lit hlit
  simp only [orderFortyNineVariablePartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineVariablePartitionClause, List.mem_map] at hlit
  obtain ⟨x, hx, rfl⟩ := hlit
  have hxyDec := (List.mem_filter.mp hx).2
  have hxy : x ≠ orderFortyNineVariableLowVertex h y :=
    of_decide_eq_true hxyDec
  exact orderFortyNineEdgeLiteral_bounded _ _ hxy.symm

theorem orderFortyNineVariableC4Clauses_satisfied
    {h : OrderFortyNineHighCount} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h.val masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineC4Clauses := by
  intro clause hclause
  simp only [orderFortyNineC4Clauses, List.mem_toArray, List.mem_map] at hclause
  obtain ⟨q, hq, rfl⟩ := hclause
  exact orderFortyNineC4Clause_satisfied hc.2.2.2.1 q hq

structure OrderFortyNineVariableCnfSegmentsSatisfied
    (h : OrderFortyNineHighCount) (masks : Array Nat)
    (val : DimacsValuation) : Prop where
  fixed : dimacsFormulaSatisfied val
    (orderFortyNineVariableFixedClauses h masks)
  c4 : dimacsFormulaSatisfied val orderFortyNineC4Clauses
  degree : dimacsFormulaSatisfied val (orderFortyNineDegreeBlocks h.val).clauses
  partition : dimacsFormulaSatisfied val
    (orderFortyNineVariablePartitionClauses h masks)

theorem orderFortyNineVariableCnfSegments_satisfied
    {h : OrderFortyNineHighCount} (hh : h.val ≤ 9)
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h.val masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded h masks) :
    ∃ val : DimacsValuation,
      OrderFortyNineVariableCnfSegmentsSatisfied h masks val ∧
      ∀ id, id ≤ 1176 → val id = orderFortyNineDimacsEdgeVal edges id := by
  obtain ⟨val, hdegreeSat, _, _, hagree⟩ :=
    orderFortyNineDegreeBlocks_invariant hc
  refine ⟨val, ?_, hagree⟩
  constructor
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineVariableFixedClauses_satisfied hh hc)
      (orderFortyNineVariableFixedClauses_bounded h masks)
      (fun id hid => (hagree id hid).symm)
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineVariableC4Clauses_satisfied hc)
      orderFortyNineC4Clauses_bounded
      (fun id hid => (hagree id hid).symm)
  · exact hdegreeSat
  · exact dimacsFormulaSatisfied_of_bounded_agree
      (orderFortyNineVariablePartitionClauses_satisfied hh hc hexcluded)
      (orderFortyNineVariablePartitionClauses_bounded h masks)
      (fun id hid => (hagree id hid).symm)

theorem orderFortyNineVariableFixedClauses_nonzero
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineVariableFixedClauses h masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineVariableFixedClauses, Array.mem_append] at hclause
  rcases hclause with hhigh | hlow
  · simp only [orderFortyNineVariableHighHighFixedClauses, List.mem_toArray,
      List.mem_map] at hhigh
    obtain ⟨ab, _, rfl⟩ := hhigh
    simp only [List.mem_singleton] at hlit
    subst lit
    unfold orderFortyNineVariableHighHighUnitLiteral
    split <;> simp [orderFortyNineEdgeLiteral] <;> omega
  · simp only [orderFortyNineVariableHighLowFixedClauses, List.mem_toArray,
      List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hlow
    obtain ⟨y, w, rfl⟩ := hlow
    simp only [List.mem_singleton] at hlit
    subst lit
    unfold orderFortyNineVariableSupportUnitLiteral
    split <;> simp [orderFortyNineEdgeLiteral] <;> omega

theorem orderFortyNineVariablePartitionClauses_nonzero
    (h : OrderFortyNineHighCount) (masks : Array Nat) :
    ∀ clause ∈ orderFortyNineVariablePartitionClauses h masks,
      DimacsClauseNonzero clause := by
  intro clause hclause lit hlit
  simp only [orderFortyNineVariablePartitionClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  simp only [orderFortyNineVariablePartitionClause, List.mem_map] at hlit
  obtain ⟨x, _, rfl⟩ := hlit
  simp [orderFortyNineEdgeLiteral] <;> omega

theorem orderFortyNineDegreeBlocks_five_nonzero :
    ∀ clause ∈ (orderFortyNineDegreeBlocks 5).clauses,
      DimacsClauseNonzero clause :=
  orderFortyNineDegreeBlocks_nonzero_all 5

structure OrderFortyNineVariableCnfCoveredBySegments
    (h : OrderFortyNineHighCount) (masks : Array Nat) (cnf : CNF Nat) : Prop where
  covered : ∀ clause ∈ cnf.clauses,
    (∃ source ∈ orderFortyNineVariableFixedClauses h masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineC4Clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ (orderFortyNineDegreeBlocks h.val).clauses,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source) ∨
    (∃ source ∈ orderFortyNineVariablePartitionClauses h masks,
      DimacsClauseNonzero source ∧ clause = dimacsClauseToSatClause source)

theorem orderFortyNineGeneratedVariableHighSatCnf_five_covered
    (masks : Array Nat) :
    OrderFortyNineVariableCnfCoveredBySegments (5 : Fin 50) masks
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50) masks) := by
  constructor
  intro clause hclause
  simp only [orderFortyNineGeneratedVariableHighSatCnf, Array.mem_append,
    dimacsFormulaToSatClauses, Array.mem_map] at hclause
  rcases hclause with ((hfixed | hc4) | hdegree) | hpartition
  · obtain ⟨source, hsource, rfl⟩ := hfixed
    exact Or.inl ⟨source, hsource,
      orderFortyNineVariableFixedClauses_nonzero _ masks source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hc4
    exact Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineC4Clauses_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hdegree
    exact Or.inr <| Or.inr <| Or.inl ⟨source, hsource,
      orderFortyNineDegreeBlocks_five_nonzero source hsource, rfl⟩
  · obtain ⟨source, hsource, rfl⟩ := hpartition
    exact Or.inr <| Or.inr <| Or.inr ⟨source, hsource,
      orderFortyNineVariablePartitionClauses_nonzero _ masks source hsource,
      rfl⟩

theorem sat_of_orderFortyNineVariableCnfSegmentsSatisfied_of_covered
    {h : OrderFortyNineHighCount} {masks : Array Nat} {cnf : CNF Nat}
    {val : DimacsValuation}
    (hsat : OrderFortyNineVariableCnfSegmentsSatisfied h masks val)
    (hcovered : OrderFortyNineVariableCnfCoveredBySegments h masks cnf) :
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

/-- A checked LRAT proof against the exact generated h=5 CNF rules out the
corresponding Boolean terminal assignment. -/
theorem false_of_orderFortyNine_generated_h5_lrat
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 5 masks edges)
    (hexcluded : OrderFortyNineVariableHighPartitionExcluded (5 : Fin 50) masks)
    (proof : Array Std.Tactic.BVDecide.LRAT.IntAction)
    (hcheck : Std.Tactic.BVDecide.LRAT.check proof
      (orderFortyNineGeneratedVariableHighSatCnf (5 : Fin 50) masks)) : False := by
  obtain ⟨val, hsegments, _⟩ :=
    orderFortyNineVariableCnfSegments_satisfied (by omega) hc hexcluded
  have hsat := sat_of_orderFortyNineVariableCnfSegmentsSatisfied_of_covered
    hsegments (orderFortyNineGeneratedVariableHighSatCnf_five_covered masks)
  have hunsat := Std.Tactic.BVDecide.LRAT.check_sound proof _ hcheck
  have hfalse := hunsat (satAssignmentOfDimacs val)
  rw [hsat] at hfalse
  contradiction

end Erdos85
