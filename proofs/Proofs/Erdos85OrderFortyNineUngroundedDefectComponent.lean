import Proofs.Erdos85OrderFortyNineIncidence
import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85ExteriorDefectDecomposition

/-! # Ungrounded ordinary defect components at order 49 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cauchy terminal for an ungrounded six-regular defect component.  Its
seven incidences per vertex and exact collision moment cannot be supported
away from the three high vertices: they would require `49 s² ≤ 46 s²`.

The graph-side consumer supplies the two moments by counting ordered pairs in
the component: diagonal pairs contribute seven, its six defect neighbors
contribute zero, and every remaining distinct pair contributes one. -/
theorem false_of_threeHigh_ungrounded_incidence_moments
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 49)
    (H C : Finset V) (hHcard : H.card = 3) (hCpos : 0 < C.card)
    (hzero : ∀ x ∈ H, (G.neighborFinset x ∩ C).card = 0)
    (hfirst : (∑ x : V, (G.neighborFinset x ∩ C).card) = 7 * C.card)
    (hsecond : (∑ x : V, ((G.neighborFinset x ∩ C).card) ^ 2) = C.card ^ 2) :
    False := by
  let L := (Finset.univ : Finset V) \ H
  let k : V → ℕ := fun x => (G.neighborFinset x ∩ C).card
  have hhighFirst : (∑ x ∈ H, k x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact hzero x hx
  have hhighSecond : (∑ x ∈ H, k x * k x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    dsimp [k]
    rw [hzero x hx]
    norm_num
  have hsplitFirst := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp) (f := k)
  have hsplitSecond := Finset.sum_sdiff
    (show H ⊆ (Finset.univ : Finset V) by simp)
    (f := fun x => k x * k x)
  have hlowFirst : (∑ x ∈ L, k x) = 7 * C.card := by
    rw [hhighFirst, add_zero] at hsplitFirst
    simpa [L, k] using hsplitFirst.trans hfirst
  have hlowSecond : (∑ x ∈ L, k x * k x) = C.card ^ 2 := by
    rw [hhighSecond, add_zero] at hsplitSecond
    have hsecond' : (∑ x : V, k x * k x) = C.card ^ 2 := by
      simpa [k, pow_two] using hsecond
    simpa [L] using hsplitSecond.trans hsecond'
  have hz := sq_sum_le_card_mul_sum_sq
    (s := L) (f := fun x => (k x : ℤ))
  have hcs : (∑ x ∈ L, k x) * (∑ x ∈ L, k x) ≤
      L.card * ∑ x ∈ L, k x * k x := by
    norm_num [pow_two] at hz
    exact_mod_cast hz
  have hLcard : L.card = 46 := by
    dsimp [L]
    rw [Finset.card_sdiff, Finset.card_univ, hcard]
    simp [hHcard]
  rw [hlowFirst, hlowSecond, hLcard] at hcs
  nlinarith

/-- Graph-facing version of the Cauchy terminal.  It is enough that every
selected vertex has degree seven and that the total common-neighbor count
against the selected set is exactly the size of that set. -/
theorem false_of_threeHigh_ungrounded_common_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V = 49)
    (H C : Finset V) (hHcard : H.card = 3) (hCpos : 0 < C.card)
    (hzero : ∀ x ∈ H, (G.neighborFinset x ∩ C).card = 0)
    (hdegree : ∀ c ∈ C, G.degree c = 7)
    (hrow : ∀ c ∈ C,
      (∑ d ∈ C, (G.neighborFinset c ∩ G.neighborFinset d).card) = C.card) :
    False := by
  apply false_of_threeHigh_ungrounded_incidence_moments
    G hcard H C hHcard hCpos hzero
  · rw [sum_card_neighbor_inter_eq_sum_degree]
    calc
      (∑ c ∈ C, G.degree c) = ∑ _c ∈ C, 7 := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hdegree c hc
      _ = 7 * C.card := by simp [Nat.mul_comm]
  · rw [sum_neighbor_inter_sq_eq_sum_sum_common]
    calc
      (∑ c ∈ C, ∑ d ∈ C,
          (G.neighborFinset c ∩ G.neighborFinset d).card) =
          ∑ _c ∈ C, C.card := by
        apply Finset.sum_congr rfl
        intro c hc
        exact hrow c hc
      _ = C.card ^ 2 := by simp [pow_two]

/-- A degree-seven row in a selected set with exactly six defect neighbors
has common-neighbor row sum equal to the selected-set cardinality. -/
theorem commonNeighbor_row_sum_eq_card_of_six_defect_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (C : Finset V) {c : V} (hc : c ∈ C)
    (hcdegree : G.degree c = 7)
    (hDdegree :
      ((secondOrderDefectGraph G).neighborFinset c ∩ C).card = 6) :
    (∑ d ∈ C, (G.neighborFinset c ∩ G.neighborFinset d).card) = C.card := by
  let D := secondOrderDefectGraph G
  have hterm : ∀ d ∈ C,
      (G.neighborFinset c ∩ G.neighborFinset d).card =
        if d = c then 7 else if D.Adj c d then 0 else 1 := by
    intro d _hd
    by_cases hdc : d = c
    · subst d
      rw [if_pos rfl, Finset.inter_self,
        G.card_neighborFinset_eq_degree, hcdegree]
    · rw [if_neg hdc]
      by_cases hD : D.Adj c d
      · rw [if_pos hD]
        exact (secondOrderDefectGraph_adj_iff_card_common_eq_zero
          G hfree (Ne.symm hdc)).mp hD
      · rw [if_neg hD]
        have hnzero :
            (G.neighborFinset c ∩ G.neighborFinset d).card ≠ 0 := by
          intro hz
          exact hD ((secondOrderDefectGraph_adj_iff_card_common_eq_zero
            G hfree (Ne.symm hdc)).mpr hz)
        have hle := (not_containsC4_iff_forall_common_le_one G).mp
          hfree c d (Ne.symm hdc)
        omega
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_erase_add _ _ hc]
  simp only [↓reduceIte]
  let S := C.erase c
  let N := S.filter fun d => D.Adj c d
  let R := S.filter fun d => ¬ D.Adj c d
  have hN : N = D.neighborFinset c ∩ C := by
    ext d
    constructor
    · intro hd
      have hd' := Finset.mem_filter.mp hd
      exact Finset.mem_inter.mpr
        ⟨(D.mem_neighborFinset c d).mpr hd'.2,
          Finset.mem_of_mem_erase hd'.1⟩
    · intro hd
      have hd' := Finset.mem_inter.mp hd
      have hAdj := (D.mem_neighborFinset c d).mp hd'.1
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨(D.ne_of_adj hAdj).symm, hd'.2⟩, hAdj⟩
  have hNcard : N.card = 6 := by
    rw [hN]
    exact hDdegree
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := S) (p := fun d => D.Adj c d)
  have hRcard : R.card + 6 = C.card - 1 := by
    have hScard : S.card = C.card - 1 := Finset.card_erase_of_mem hc
    have hp : N.card + R.card = S.card := by simpa [N, R] using hpartition
    omega
  have hsum : (∑ d ∈ S, if D.Adj c d then 0 else 1) = R.card := by
    calc
      (∑ d ∈ S, if D.Adj c d then 0 else 1) =
          ∑ d ∈ S, if ¬ D.Adj c d then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro d _
            by_cases hd : D.Adj c d <;> simp [hd]
      _ = R.card := by rw [Finset.sum_boole]; rfl
  change (∑ d ∈ S, if d = c then 7 else if D.Adj c d then 0 else 1) + 7 = C.card
  have hcnot : ∀ d ∈ S, d ≠ c := fun d hd => (Finset.mem_erase.mp hd).1
  rw [Finset.sum_congr rfl (fun d hd => by rw [if_neg (hcnot d hd)]), hsum]
  have hCseven : 7 ≤ C.card := by
    have hNle : N.card ≤ S.card := Finset.card_filter_le _ _
    rw [hNcard, Finset.card_erase_of_mem hc] at hNle
    omega
  omega

/-- No nonempty set disjoint from the three high neighborhoods can induce
six defect neighbors per vertex.  This is the graph-semantic exclusion of an
ungrounded ordinary defect component. -/
theorem false_of_threeHigh_ungrounded_sixRegular_defect_set
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hcard : Fintype.card V = 49)
    (H C : Finset V) (hHcard : H.card = 3) (hCpos : 0 < C.card)
    (hzero : ∀ x ∈ H, (G.neighborFinset x ∩ C).card = 0)
    (hdegree : ∀ c ∈ C, G.degree c = 7)
    (hDdegree : ∀ c ∈ C,
      ((secondOrderDefectGraph G).neighborFinset c ∩ C).card = 6) :
    False := by
  apply false_of_threeHigh_ungrounded_common_row
    G hcard H C hHcard hCpos hzero hdegree
  intro c hc
  exact commonNeighbor_row_sum_eq_card_of_six_defect_neighbors
    G hfree C hc (hdegree c hc) (hDdegree c hc)

end

end Erdos85

#print axioms Erdos85.false_of_threeHigh_ungrounded_incidence_moments
#print axioms Erdos85.false_of_threeHigh_ungrounded_common_row
#print axioms Erdos85.commonNeighbor_row_sum_eq_card_of_six_defect_neighbors
#print axioms Erdos85.false_of_threeHigh_ungrounded_sixRegular_defect_set
