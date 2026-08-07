import Proofs.Erdos85OrderFortyNineBooleanTerminal
import Proofs.Erdos85SequentialCounterReification

/-!
# DIMACS degree rows for the order-49 encoding

The certificate generator lists, for vertex `i`, the other endpoints in
increasing order and uses the one-based lexicographic unordered-edge ID.
This file proves that the resulting 48 signed literals reify precisely the
Boolean adjacency row stored in the 1176 edge bits.
-/

namespace Erdos85

/-- The `k`-th vertex other than `i`, in increasing order. -/
def orderFortyNineOtherVertex (i : Fin 49) (k : Fin 48) : Fin 49 :=
  if k.val < i.val then ⟨k.val, by omega⟩ else ⟨k.val + 1, by omega⟩

theorem orderFortyNineOtherVertex_ne (i : Fin 49) (k : Fin 48) :
    orderFortyNineOtherVertex i k ≠ i := by
  by_cases hki : k.val < i.val
  · intro heq
    have hval := congrArg Fin.val heq
    simp [orderFortyNineOtherVertex, hki] at hval
    omega
  · intro heq
    have hval := congrArg Fin.val heq
    simp [orderFortyNineOtherVertex, hki] at hval
    omega

theorem orderFortyNineOtherVertex_injective (i : Fin 49) :
    Function.Injective (orderFortyNineOtherVertex i) := by
  intro k l heq
  have hval := congrArg Fin.val heq
  by_cases hk : k.val < i.val <;> by_cases hl : l.val < i.val
  · simp [orderFortyNineOtherVertex, hk, hl] at hval
    exact Fin.ext hval
  · simp [orderFortyNineOtherVertex, hk, hl] at hval
    omega
  · simp [orderFortyNineOtherVertex, hk, hl] at hval
    omega
  · simp [orderFortyNineOtherVertex, hk, hl] at hval
    apply Fin.ext
    omega

theorem orderFortyNineOtherVertex_surjective_away
    (i j : Fin 49) (hji : j ≠ i) :
    ∃ k : Fin 48, orderFortyNineOtherVertex i k = j := by
  by_cases hlt : j.val < i.val
  · refine ⟨⟨j.val, by omega⟩, ?_⟩
    apply Fin.ext
    simp [orderFortyNineOtherVertex, hlt]
  · have hij : i.val < j.val := by
      have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
      omega
    let k : Fin 48 := ⟨j.val - 1, by omega⟩
    have hk : ¬k.val < i.val := by
      dsimp [k]
      omega
    refine ⟨k, ?_⟩
    apply Fin.ext
    simp [orderFortyNineOtherVertex, hk, k]
    omega
/-- One-based DIMACS edge ID. -/
def orderFortyNineEdgeLiteral (i j : Fin 49) : Int :=
  (orderFortyNineEdgeIndex i j + 1 : Nat)

/-- The exact 48-literal row passed to `CardEnc.equals`. -/
def orderFortyNineDimacsRow (i : Fin 49) : Array Int :=
  Array.ofFn fun k : Fin 48 =>
    orderFortyNineEdgeLiteral i (orderFortyNineOtherVertex i k)

/-- Truth assignment of the first 1176 DIMACS variables from an edge bitvec. -/
def orderFortyNineDimacsEdgeVal (edges : BitVec 1176) : DimacsValuation :=
  fun id => if 1 ≤ id ∧ id ≤ 1176 then edges.getLsbD (id - 1) else false

/-- Boolean row in the same 48-coordinate order as the DIMACS literals. -/
def orderFortyNineCounterRow (edges : BitVec 1176) (i : Fin 49) :
    Fin 48 → Bool := fun k =>
  orderFortyNineBitAdj edges i (orderFortyNineOtherVertex i k)

theorem orderFortyNineDimacsEdgeVal_literal
    (edges : BitVec 1176) (i : Fin 49) (k : Fin 48) :
    dimacsLitValue (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineEdgeLiteral i (orderFortyNineOtherVertex i k)) =
      orderFortyNineCounterRow edges i k := by
  have hne := orderFortyNineOtherVertex_ne i k
  have hlt := orderFortyNineEdgeIndex_lt i
    (orderFortyNineOtherVertex i k) hne.symm
  have hpos : 0 < orderFortyNineEdgeIndex i
      (orderFortyNineOtherVertex i k) + 1 := Nat.zero_lt_succ _
  simp only [orderFortyNineEdgeLiteral]
  rw [dimacsLitValue_natCast _ hpos]
  simp only [orderFortyNineDimacsEdgeVal,
    orderFortyNineCounterRow, orderFortyNineBitAdj, hne.symm, if_false]
  rw [if_pos (by omega)]
  congr 1

/-- Reification of an arbitrary off-diagonal positive edge literal. -/
theorem orderFortyNineDimacsEdgeVal_edgeLiteral
    (edges : BitVec 1176) (i j : Fin 49) (hij : i ≠ j) :
    dimacsLitValue (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineEdgeLiteral i j) = orderFortyNineBitAdj edges i j := by
  have hlt := orderFortyNineEdgeIndex_lt i j hij
  have hpos : 0 < orderFortyNineEdgeIndex i j + 1 := Nat.zero_lt_succ _
  simp only [orderFortyNineEdgeLiteral]
  rw [dimacsLitValue_natCast _ hpos]
  simp only [orderFortyNineDimacsEdgeVal, orderFortyNineBitAdj, hij, if_false]
  rw [if_pos (by omega)]
  congr 1

/-- Reification of an arbitrary off-diagonal negative edge literal. -/
theorem orderFortyNineDimacsEdgeVal_negEdgeLiteral
    (edges : BitVec 1176) (i j : Fin 49) (hij : i ≠ j) :
    dimacsLitValue (orderFortyNineDimacsEdgeVal edges)
      (-orderFortyNineEdgeLiteral i j) =
      !(orderFortyNineBitAdj edges i j) := by
  have hpos : 0 < orderFortyNineEdgeLiteral i j := by
    simp [orderFortyNineEdgeLiteral]
  have hneg : ¬0 < -orderFortyNineEdgeLiteral i j := by omega
  have hpositive := orderFortyNineDimacsEdgeVal_edgeLiteral edges i j hij
  simp only [dimacsLitValue, hpos, if_true] at hpositive
  simp only [dimacsLitValue, hneg, if_false, Int.natAbs_neg]
  rw [hpositive]

theorem orderFortyNineEdgeLiteral_bounded
    (i j : Fin 49) (hij : i ≠ j) :
    (orderFortyNineEdgeLiteral i j).natAbs ≤ 1176 := by
  have hlt := orderFortyNineEdgeIndex_lt i j hij
  simp [orderFortyNineEdgeLiteral]
  omega

theorem orderFortyNineNegEdgeLiteral_bounded
    (i j : Fin 49) (hij : i ≠ j) :
    (-orderFortyNineEdgeLiteral i j).natAbs ≤ 1176 := by
  simpa using orderFortyNineEdgeLiteral_bounded i j hij

/-- The graph-edge assignment reifies every literal in the exact PySAT row. -/
theorem orderFortyNineDimacsRow_reifies
    (edges : BitVec 1176) (i : Fin 49) :
    SeqCounterInputReifies (orderFortyNineDimacsEdgeVal edges) 1176
      (orderFortyNineDimacsRow i) (orderFortyNineCounterRow edges i) := by
  constructor
  · simp [orderFortyNineDimacsRow]
  · intro k hk
    have hk' : k < 48 := by simpa [orderFortyNineDimacsRow] using hk
    simp [orderFortyNineDimacsRow, Array.getD, hk', orderFortyNineEdgeLiteral]
    omega
  · intro k hk
    have hk' : k < 48 := by simpa [orderFortyNineDimacsRow] using hk
    have hne := orderFortyNineOtherVertex_ne i ⟨k, hk'⟩
    have hlt := orderFortyNineEdgeIndex_lt i
      (orderFortyNineOtherVertex i ⟨k, hk'⟩) hne.symm
    simp [orderFortyNineDimacsRow, Array.getD, hk', orderFortyNineEdgeLiteral]
    omega
  · intro k hk
    have hk' : k < 48 := by simpa [orderFortyNineDimacsRow] using hk
    simpa [orderFortyNineDimacsRow, Array.getD, hk'] using
      orderFortyNineDimacsEdgeVal_literal edges i ⟨k, hk'⟩

theorem seqPrefixTrue_full_eq_filter_card {n : Nat} (x : Fin n → Bool) :
    seqPrefixTrue x n = (Finset.univ.filter fun i => x i).card := by
  unfold seqPrefixTrue
  apply Finset.card_bij (fun i hi =>
    ⟨i, Finset.mem_range.mp (Finset.mem_filter.mp hi).1⟩)
  · intro i hi
    have hxi : ∃ hi' : i < n, x ⟨i, hi'⟩ = true := by
      simpa using (Finset.mem_filter.mp hi).2
    obtain ⟨hi', hxi⟩ := hxi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simpa using hxi
  · intro i₁ hi₁ i₂ hi₂ heq
    exact congrArg Fin.val heq
  · intro k hk
    refine ⟨k.val, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr k.isLt, ?_⟩
      simp only [k.isLt, dite_true]
      exact (Finset.mem_filter.mp hk).2
    · rfl

/-- Removing the diagonal coordinate does not change the adjacency-row
count, because the encoding is loopless. -/
theorem orderFortyNineCounterRow_count
    (edges : BitVec 1176) (i : Fin 49) :
    seqPrefixTrue (orderFortyNineCounterRow edges i) 48 =
      (Finset.univ.filter fun j => orderFortyNineBitAdj edges i j).card := by
  rw [seqPrefixTrue_full_eq_filter_card]
  apply Finset.card_bij (fun k _ => orderFortyNineOtherVertex i k)
  · intro k hk
    simpa [orderFortyNineCounterRow] using hk
  · intro k₁ hk₁ k₂ hk₂ heq
    exact orderFortyNineOtherVertex_injective i heq
  · intro j hj
    have hadj : orderFortyNineBitAdj edges i j = true :=
      (Finset.mem_filter.mp hj).2
    have hji : j ≠ i := by
      intro h
      subst j
      simp [orderFortyNineBitAdj] at hadj
    obtain ⟨k, rfl⟩ := orderFortyNineOtherVertex_surjective_away i j hji
    refine ⟨k, ?_, rfl⟩
    simpa [orderFortyNineCounterRow] using hadj

/-- The prescribed degree of a row in the classified order-49 instance. -/
def orderFortyNineTargetDegree (h : Nat) (i : Fin 49) : Nat :=
  if i.val < h then 8 else 7

/-- The relation-level Boolean constraints give the exact population count
used by the sequential-counter equality block for every vertex. -/
theorem orderFortyNineCounterRow_count_of_constraints
    {h : Nat} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h masks edges) (i : Fin 49) :
    seqPrefixTrue (orderFortyNineCounterRow edges i) 48 =
      orderFortyNineTargetDegree h i := by
  rw [orderFortyNineCounterRow_count]
  exact hc.2.2.1 i

@[simp] theorem orderFortyNineDimacsRow_size (i : Fin 49) :
    (orderFortyNineDimacsRow i).size = 48 := by
  rw [orderFortyNineDimacsRow, Array.size_ofFn]

/- The same graph row with the counter generator's literal-array-sized
index type.  Naming this adapter prevents repeated reduction of the concrete
48-entry array during elaboration of counter valuations. -/
def orderFortyNineDimacsSizedCounterRow
    (edges : BitVec 1176) (i : Fin 49) :
    Fin (orderFortyNineDimacsRow i).size → Bool := fun k =>
  orderFortyNineCounterRow edges i
    (Fin.cast (orderFortyNineDimacsRow_size i) k)

theorem orderFortyNineDimacsRow_reifies_sized
    (edges : BitVec 1176) (i : Fin 49) :
    SeqCounterInputReifies (orderFortyNineDimacsEdgeVal edges) 1176
      (orderFortyNineDimacsRow i)
      (orderFortyNineDimacsSizedCounterRow edges i) := by
  have h := orderFortyNineDimacsRow_reifies edges i
  constructor
  · rfl
  · intro k hk
    exact h.nonzero k (by
      rw [← orderFortyNineDimacsRow_size i]
      exact hk)
  · intro k hk
    exact h.bounded k (by
      rw [← orderFortyNineDimacsRow_size i]
      exact hk)
  · intro k hk
    have hk48 : k < 48 := by
      rw [← orderFortyNineDimacsRow_size i]
      exact hk
    rw [h.value k hk48]
    rfl

theorem seqPrefixTrue_cast {m n : Nat} (h : m = n) (x : Fin n → Bool) :
    seqPrefixTrue (fun k : Fin m => x (Fin.cast h k)) m =
      seqPrefixTrue x n := by
  subst n
  rfl

theorem orderFortyNineDimacsSizedCounterRow_count_of_constraints
    {h : Nat} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h masks edges) (i : Fin 49) :
    seqPrefixTrue (orderFortyNineDimacsSizedCounterRow edges i)
        (orderFortyNineDimacsRow i).size =
      orderFortyNineTargetDegree h i := by
  change seqPrefixTrue (fun k : Fin (orderFortyNineDimacsRow i).size =>
    orderFortyNineCounterRow edges i
      (Fin.cast (orderFortyNineDimacsRow_size i) k))
    (orderFortyNineDimacsRow i).size = _
  rw [seqPrefixTrue_cast (orderFortyNineDimacsRow_size i)]
  exact orderFortyNineCounterRow_count_of_constraints hc i

/- One graph degree row satisfying the Boolean terminal extends to a
satisfying valuation of its byte-exact `CardEnc.equals` block. -/
theorem orderFortyNineDimacsRow_equals_formulaSatisfied
    {h : Nat} {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints h masks edges) (i : Fin 49) :
    ∃ val : DimacsValuation,
      dimacsFormulaSatisfied val
        (seqCounterEqualsCore 1176 (orderFortyNineDimacsRow i)
          (orderFortyNineTargetDegree h i)).clauses := by
  let vars := orderFortyNineDimacsRow i
  let x := orderFortyNineDimacsSizedCounterRow edges i
  let t := orderFortyNineTargetDegree h i
  let negRow := seqCounterMappedNegRow vars x
  let lower := seqCounterAtLeastCore 1176 vars t
  let lowerVal := seqCounterBlockVal
    (orderFortyNineDimacsEdgeVal edges) 1176 negRow lower.ids
  let upper := seqCounterAtMostCore lower.top vars t
  let upperVal := seqCounterBlockVal lowerVal lower.top x upper.ids
  refine ⟨upperVal, ?_⟩
  exact seqCounterEqualsCore_formulaSatisfied
      (orderFortyNineDimacsEdgeVal edges) 1176
      (orderFortyNineDimacsRow i) (orderFortyNineDimacsSizedCounterRow edges i)
      (orderFortyNineDimacsRow_reifies_sized edges i)
      (orderFortyNineTargetDegree h i)
      (orderFortyNineDimacsSizedCounterRow_count_of_constraints hc i)

end Erdos85
