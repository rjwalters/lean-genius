import Proofs.Erdos85OrderFortyNineSevenHighCnf

/-! # Semantic bridge for the exact h=7 order-49 CNF -/

namespace Erdos85

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

theorem orderFortyNineH7C4Clauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 7 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineC4Clauses := by
  intro clause hclause
  simp only [orderFortyNineC4Clauses, List.mem_toArray, List.mem_map] at hclause
  obtain ⟨q, hq, rfl⟩ := hclause
  exact orderFortyNineC4Clause_satisfied hc.2.2.2.1 q hq

end Erdos85
