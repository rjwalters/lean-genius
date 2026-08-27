import Proofs.Erdos85OrderFortyNineIncidence

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

end

end Erdos85

#print axioms Erdos85.false_of_threeHigh_ungrounded_incidence_moments
#print axioms Erdos85.false_of_threeHigh_ungrounded_common_row
