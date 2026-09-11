import Proofs.Erdos85GadgetDegreeSquares

namespace Erdos85

/-- The fixed-graph moment obstruction used for order-five automorphisms.
The boundary hypothesis is the degree-sum inequality supplied by at most
one fixed neighbour per moved vertex in an ambient graph of order at most 80. -/
theorem containsC4_of_four_nine_degrees_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hlo : 14 ≤ Fintype.card V) (hhi : Fintype.card V ≤ 23)
    (hdegrees : ∀ v, G.degree v = 4 ∨ G.degree v = 9)
    (hboundary : 10 * Fintype.card V ≤ (∑ v : V, G.degree v) + 80) :
    containsC4 V G := by
  by_contra hfree
  have hpoint : ∀ v : V, 12 * G.degree v ≤ 2 * (G.degree v).choose 2 + 36 := by
    intro v
    rcases hdegrees v with h | h <;> norm_num [h, Nat.choose]
  have hsum : 12 * (∑ v : V, G.degree v) ≤
      2 * (∑ v : V, (G.degree v).choose 2) + 36 * Fintype.card V := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] using h
  have hcherry := sum_degree_choose_two_le_card_choose_two_of_not_containsC4 G hfree
  have hchoose := two_mul_choose_two (Fintype.card V)
  have hpred : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  have hmoment : 85 * Fintype.card V ≤
      Fintype.card V * Fintype.card V + 960 := by
    nlinarith
  have hinterval : Fintype.card V * Fintype.card V + 322 ≤
      37 * Fintype.card V := by
    nlinarith
  nlinarith

end Erdos85

#print axioms Erdos85.containsC4_of_four_nine_degrees_boundary
