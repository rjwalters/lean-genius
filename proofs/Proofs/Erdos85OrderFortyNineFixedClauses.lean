import Proofs.Erdos85OrderFortyNineDegreeBlocks

/-!
# Fixed-edge clauses for the certified order-49 instances

These are the first two production clause groups: 36 negative high--high
units in lexicographic pair order, followed by 40 × 9 signed high-support
units in low-major, high-minor order.
-/

namespace Erdos85

def orderFortyNineHighVertex (w : Fin 9) : Fin 49 := ⟨w.val, by omega⟩

def orderFortyNineLowVertex (y : Fin 40) : Fin 49 := ⟨y.val + 9, by omega⟩

/-- Lexicographically ordered strict pairs, matching `itertools.combinations`. -/
def orderFortyNineHighPairs : List (Fin 9 × Fin 9) :=
  (List.finRange 9).flatMap fun a =>
    ((List.finRange 9).filter fun b => a.val < b.val).map fun b => (a, b)

def orderFortyNineHighHighFixedClauses : Array DimacsClause :=
  (orderFortyNineHighPairs.map fun ab =>
    [-orderFortyNineEdgeLiteral
      (orderFortyNineHighVertex ab.1) (orderFortyNineHighVertex ab.2)]).toArray

def orderFortyNineSupportUnitLiteral
    (masks : Array Nat) (y : Fin 40) (w : Fin 9) : Int :=
  let edge := orderFortyNineEdgeLiteral
    (orderFortyNineLowVertex y) (orderFortyNineHighVertex w)
  if (orderFortyNineSupportMask masks (orderFortyNineLowVertex y)).getLsbD w.val
    then edge else -edge

def orderFortyNineHighLowFixedClauses (masks : Array Nat) :
    Array DimacsClause :=
  ((List.finRange 40).flatMap fun y =>
    (List.finRange 9).map fun w =>
      [orderFortyNineSupportUnitLiteral masks y w]).toArray

def orderFortyNineFixedClauses (masks : Array Nat) : Array DimacsClause :=
  orderFortyNineHighHighFixedClauses ++
    orderFortyNineHighLowFixedClauses masks

/-- Certified profiles store zero support masks at the first nine (high)
vertices; low support masks begin at vertex nine. -/
def OrderFortyNineHighMasksZero (masks : Array Nat) : Prop :=
  ∀ a w : Fin 9,
    (orderFortyNineSupportMask masks (orderFortyNineHighVertex a)).getLsbD
      w.val = false

theorem orderFortyNineHighVertex_injective :
    Function.Injective orderFortyNineHighVertex := by
  intro a b hab
  apply Fin.ext
  simpa [orderFortyNineHighVertex] using congrArg Fin.val hab

theorem orderFortyNineLowVertex_ne_highVertex (y : Fin 40) (w : Fin 9) :
    orderFortyNineLowVertex y ≠ orderFortyNineHighVertex w := by
  intro heq
  have := congrArg Fin.val heq
  simp [orderFortyNineLowVertex, orderFortyNineHighVertex] at this
  omega

theorem orderFortyNineHighPairs_ne (ab : Fin 9 × Fin 9)
    (hab : ab ∈ orderFortyNineHighPairs) : ab.1 ≠ ab.2 := by
  native_decide +revert

theorem orderFortyNineHighHighFixedClauses_satisfied
    (edges : BitVec 1176)
    (hhigh : ∀ a b : Fin 9, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineHighVertex a)
        (orderFortyNineHighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineHighHighFixedClauses := by
  intro clause hclause
  simp only [orderFortyNineHighHighFixedClauses, List.mem_toArray,
    List.mem_map] at hclause
  obtain ⟨ab, hab, rfl⟩ := hclause
  rcases ab with ⟨a, b⟩
  have hab' : a ≠ b := orderFortyNineHighPairs_ne (a, b) hab
  have hne : orderFortyNineHighVertex a ≠ orderFortyNineHighVertex b := by
    exact fun heq => hab' (orderFortyNineHighVertex_injective heq)
  refine ⟨-orderFortyNineEdgeLiteral
      (orderFortyNineHighVertex a) (orderFortyNineHighVertex b), by simp, ?_⟩
  rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
    hhigh a b hab']
  rfl

theorem orderFortyNineHighHigh_independent_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks) :
    ∀ a b : Fin 9, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineHighVertex a)
        (orderFortyNineHighVertex b) = false := by
  intro a b hab
  have hsupp := hc.2.2.2.2.1 (orderFortyNineHighVertex a) b (by omega)
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineHighVertex a)
          (orderFortyNineHighVertex b) =
        (orderFortyNineSupportMask masks
          (orderFortyNineHighVertex a)).getLsbD b.val := by
    simpa [orderFortyNineHighVertex] using hsupp
  rw [hsupp', hzero a b]

theorem orderFortyNineHighLowFixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineHighLowFixedClauses masks) := by
  intro clause hclause
  simp only [orderFortyNineHighLowFixedClauses, List.mem_toArray,
    List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hclause
  obtain ⟨y, w, rfl⟩ := hclause
  have hne := orderFortyNineLowVertex_ne_highVertex y w
  have hsupp := hc.2.2.2.2.1 (orderFortyNineLowVertex y) w (by omega)
  have hsupp' :
      orderFortyNineBitAdj edges (orderFortyNineLowVertex y)
          (orderFortyNineHighVertex w) =
        (orderFortyNineSupportMask masks (orderFortyNineLowVertex y)).getLsbD
          w.val := by
    simpa [orderFortyNineHighVertex] using hsupp
  by_cases hbit :
      (orderFortyNineSupportMask masks (orderFortyNineLowVertex y)).getLsbD
        w.val = true
  · refine ⟨orderFortyNineEdgeLiteral
        (orderFortyNineLowVertex y) (orderFortyNineHighVertex w), ?_, ?_⟩
    · simp [orderFortyNineSupportUnitLiteral, hbit]
    · rw [orderFortyNineDimacsEdgeVal_edgeLiteral edges _ _ hne, hsupp', hbit]
  · have hbitFalse :
        (orderFortyNineSupportMask masks (orderFortyNineLowVertex y)).getLsbD
          w.val = false := Bool.eq_false_of_not_eq_true hbit
    refine ⟨-orderFortyNineEdgeLiteral
        (orderFortyNineLowVertex y) (orderFortyNineHighVertex w), ?_, ?_⟩
    · simp only [orderFortyNineSupportUnitLiteral]
      rw [if_neg hbit]
      simp
    · rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges _ _ hne,
        hsupp', hbitFalse]
      rfl

theorem orderFortyNineFixedClauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hhigh : ∀ a b : Fin 9, a ≠ b →
      orderFortyNineBitAdj edges (orderFortyNineHighVertex a)
        (orderFortyNineHighVertex b) = false) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineFixedClauses masks) :=
  dimacsFormulaSatisfied_append
    (orderFortyNineHighHighFixedClauses_satisfied edges hhigh)
    (orderFortyNineHighLowFixedClauses_satisfied hc)

theorem orderFortyNineFixedClauses_satisfied_of_zero_masks
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges)
    (hzero : OrderFortyNineHighMasksZero masks) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineFixedClauses masks) :=
  orderFortyNineFixedClauses_satisfied hc
    (orderFortyNineHighHigh_independent_of_zero_masks hc hzero)

end Erdos85
