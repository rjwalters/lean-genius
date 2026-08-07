import Proofs.Erdos85OrderFortyNineFixedClauses

/-!
# C4 clauses for the order-49 DIMACS encoding

For every vertex pair `i < j` and every pair `w < w'` outside `{i,j}`, the
production generator emits the four-negative clause forbidding `w,w'` from
being two common neighbors.  The construction below preserves exactly that
lexicographic nesting while its soundness proof treats the family uniformly.
-/

namespace Erdos85

/-- Strict pairs from a list, in the same nesting order as
`itertools.combinations(xs, 2)`. -/
def orderFortyNineStrictPairs (xs : List (Fin 49)) :
    List (Fin 49 × Fin 49) :=
  xs.flatMap fun a => (xs.filter fun b => a.val < b.val).map fun b => (a, b)

theorem orderFortyNineStrictPairs_fst_mem {xs : List (Fin 49)}
    {ab : Fin 49 × Fin 49} (hab : ab ∈ orderFortyNineStrictPairs xs) :
    ab.1 ∈ xs := by
  rw [orderFortyNineStrictPairs] at hab
  obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hab
  obtain ⟨b, hb, hp⟩ := List.mem_map.mp hab
  rw [← hp]
  exact ha

theorem orderFortyNineStrictPairs_snd_mem {xs : List (Fin 49)}
    {ab : Fin 49 × Fin 49} (hab : ab ∈ orderFortyNineStrictPairs xs) :
    ab.2 ∈ xs := by
  rw [orderFortyNineStrictPairs] at hab
  obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hab
  obtain ⟨b, hb, hp⟩ := List.mem_map.mp hab
  rw [← hp]
  exact (List.mem_filter.mp hb).1

theorem orderFortyNineStrictPairs_lt {xs : List (Fin 49)}
    {ab : Fin 49 × Fin 49} (hab : ab ∈ orderFortyNineStrictPairs xs) :
    ab.1.val < ab.2.val := by
  rw [orderFortyNineStrictPairs] at hab
  obtain ⟨a, ha, hab⟩ := List.mem_flatMap.mp hab
  obtain ⟨b, hb, hp⟩ := List.mem_map.mp hab
  rw [← hp]
  exact of_decide_eq_true (List.mem_filter.mp hb).2

def orderFortyNineVerticesAway (i j : Fin 49) : List (Fin 49) :=
  (List.finRange 49).filter fun w => w ≠ i ∧ w ≠ j

def orderFortyNineC4Tuples :
    List ((Fin 49 × Fin 49) × (Fin 49 × Fin 49)) :=
  (orderFortyNineStrictPairs (List.finRange 49)).flatMap fun ij =>
    (orderFortyNineStrictPairs
      (orderFortyNineVerticesAway ij.1 ij.2)).map fun ww => (ij, ww)

def orderFortyNineC4Clause
    (q : (Fin 49 × Fin 49) × (Fin 49 × Fin 49)) : DimacsClause :=
  let i := q.1.1
  let j := q.1.2
  let w := q.2.1
  let w' := q.2.2
  [-orderFortyNineEdgeLiteral i w,
   -orderFortyNineEdgeLiteral j w,
   -orderFortyNineEdgeLiteral i w',
   -orderFortyNineEdgeLiteral j w']

def orderFortyNineC4Clauses : Array DimacsClause :=
  (orderFortyNineC4Tuples.map orderFortyNineC4Clause).toArray

theorem orderFortyNineC4Tuples_properties
    {q : (Fin 49 × Fin 49) × (Fin 49 × Fin 49)}
    (hq : q ∈ orderFortyNineC4Tuples) :
    q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧
    q.2.1 ≠ q.1.1 ∧ q.2.1 ≠ q.1.2 ∧
    q.2.2 ≠ q.1.1 ∧ q.2.2 ≠ q.1.2 := by
  rw [orderFortyNineC4Tuples] at hq
  obtain ⟨ij, hij, hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨ww, hww, heq⟩ := List.mem_map.mp hq
  rw [← heq]
  have hijlt := orderFortyNineStrictPairs_lt hij
  have hwwlt := orderFortyNineStrictPairs_lt hww
  have hwmem := orderFortyNineStrictPairs_fst_mem hww
  have hw'mem := orderFortyNineStrictPairs_snd_mem hww
  have hwaway : ww.1 ≠ ij.1 ∧ ww.1 ≠ ij.2 :=
    of_decide_eq_true (List.mem_filter.mp hwmem).2
  have hw'away : ww.2 ≠ ij.1 ∧ ww.2 ≠ ij.2 :=
    of_decide_eq_true (List.mem_filter.mp hw'mem).2
  exact ⟨Fin.ne_of_lt hijlt, Fin.ne_of_lt hwwlt, hwaway.1, hwaway.2,
    hw'away.1, hw'away.2⟩

theorem orderFortyNineC4Clause_satisfied
    {edges : BitVec 1176}
    (hcommon : ∀ i j : Fin 49, i ≠ j →
      (Finset.univ.filter fun k =>
        orderFortyNineBitAdj edges i k &&
          orderFortyNineBitAdj edges j k).card ≤ 1)
    (q : (Fin 49 × Fin 49) × (Fin 49 × Fin 49))
    (hq : q ∈ orderFortyNineC4Tuples) :
    dimacsClauseSatisfied (orderFortyNineDimacsEdgeVal edges)
      (orderFortyNineC4Clause q) := by
  rcases q with ⟨⟨i, j⟩, ⟨w, w'⟩⟩
  obtain ⟨hij, hww', hwi, hwj, hw'i, hw'j⟩ :=
    orderFortyNineC4Tuples_properties hq
  by_cases hiw : orderFortyNineBitAdj edges i w = true
  · by_cases hjw : orderFortyNineBitAdj edges j w = true
    · by_cases hiw' : orderFortyNineBitAdj edges i w' = true
      · by_cases hjw' : orderFortyNineBitAdj edges j w' = true
        · have hwmem : w ∈ Finset.univ.filter fun k =>
              orderFortyNineBitAdj edges i k &&
                orderFortyNineBitAdj edges j k := by
            simp [hiw, hjw]
          have hw'mem : w' ∈ Finset.univ.filter fun k =>
              orderFortyNineBitAdj edges i k &&
                orderFortyNineBitAdj edges j k := by
            simp [hiw', hjw']
          have heq := Finset.card_le_one.mp (hcommon i j hij) w hwmem w' hw'mem
          exact (hww' heq).elim
        · have hjw'False := Bool.eq_false_of_not_eq_true hjw'
          refine ⟨-orderFortyNineEdgeLiteral j w', by
            simp [orderFortyNineC4Clause], ?_⟩
          rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges j w' hw'j.symm,
            hjw'False]
          rfl
      · have hiw'False := Bool.eq_false_of_not_eq_true hiw'
        refine ⟨-orderFortyNineEdgeLiteral i w', by
          simp [orderFortyNineC4Clause], ?_⟩
        rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges i w' hw'i.symm,
          hiw'False]
        rfl
    · have hjwFalse := Bool.eq_false_of_not_eq_true hjw
      refine ⟨-orderFortyNineEdgeLiteral j w, by
        simp [orderFortyNineC4Clause], ?_⟩
      rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges j w hwj.symm,
        hjwFalse]
      rfl
  · have hiwFalse := Bool.eq_false_of_not_eq_true hiw
    refine ⟨-orderFortyNineEdgeLiteral i w, by
      simp [orderFortyNineC4Clause], ?_⟩
    rw [orderFortyNineDimacsEdgeVal_negEdgeLiteral edges i w hwi.symm,
      hiwFalse]
    rfl

theorem orderFortyNineC4Clauses_satisfied
    {masks : Array Nat} {edges : BitVec 1176}
    (hc : orderFortyNineBooleanConstraints 9 masks edges) :
    dimacsFormulaSatisfied (orderFortyNineDimacsEdgeVal edges)
      orderFortyNineC4Clauses := by
  intro clause hclause
  simp only [orderFortyNineC4Clauses, List.mem_toArray, List.mem_map] at hclause
  obtain ⟨q, hq, rfl⟩ := hclause
  exact orderFortyNineC4Clause_satisfied hc.2.2.2.1 q hq

end Erdos85
