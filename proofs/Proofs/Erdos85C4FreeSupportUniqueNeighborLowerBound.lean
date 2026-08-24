import Proofs.Erdos85C4FreeSubsetCherryBound
import Proofs.Erdos85GadgetCounting

/-!
# Unique-neighbor lower bound for a C4-free support

If a support `S` has size `m` in a `q`-regular C4-free graph, its total
incidence is `mq`.  C4-freeness bounds the total number of centered pairs by
`choose(m,2)`.  Consequently at least `m(q-m+1)` vertices see exactly one
point of `S` (when `m ≤ q`).  This is the support-counting input in the
maximal defect-connectivity argument for `NONBIP-CONNECTED [q]`.
-/

open Finset SimpleGraph

namespace Erdos85

/-- Abstract incidence-to-unique-neighbor conversion. -/
theorem card_eq_one_lower_of_sum_and_pair_budget
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ι → ℕ) (m q : ℕ) (hmq : m ≤ q)
    (hsum : ∑ v, k v = m * q)
    (hpair : ∑ v, (k v).choose 2 ≤ m.choose 2) :
    m * (q - m + 1) ≤ (Finset.univ.filter fun v => k v = 1).card := by
  by_cases hm0 : m = 0
  · simp [hm0]
  have hpoint : ∀ v : ι,
      k v ≤ (if k v = 1 then 1 else 0) + 2 * (k v).choose 2 := by
    intro v
    by_cases h0 : k v = 0
    · simp [h0]
    by_cases h1 : k v = 1
    · simp [h1]
    have hk : 2 ≤ k v := by omega
    simp [h1]
    rw [show 2 * (k v).choose 2 = k v * (k v - 1) by
      rw [mul_comm, Nat.choose_two_right,
        Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self (k v))]]
    exact Nat.le_mul_of_pos_right (k v) (by omega)
  have hsumle := Finset.sum_le_sum
    (s := (Finset.univ : Finset ι)) (fun v _ => hpoint v)
  rw [Finset.sum_add_distrib, hsum] at hsumle
  rw [← Finset.mul_sum] at hsumle
  have hindicator :
      (∑ v : ι, if k v = 1 then 1 else 0) =
        (Finset.univ.filter fun v => k v = 1).card := by
    rw [← Finset.sum_filter]
    simp
  rw [hindicator] at hsumle
  have hbudgetChoose : m * q ≤
      (Finset.univ.filter fun v => k v = 1).card + 2 * m.choose 2 :=
    hsumle.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 2 hpair) _)
  have htwom : 2 * m.choose 2 = m * (m - 1) := by
    rw [mul_comm, Nat.choose_two_right,
      Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self m)]
  rw [htwom] at hbudgetChoose
  have hdecomp : m * q = m * (q - m + 1) + m * (m - 1) := by
    have hqform : q = (q - m + 1) + (m - 1) := by omega
    nth_rewrite 1 [hqform]
    ring
  rw [hdecomp] at hbudgetChoose
  omega

/-- A support of size `m ≤ q` in a `q`-regular C4-free graph has at least
`m(q-m+1)` vertices incident with exactly one support vertex. -/
theorem c4Free_regular_card_one_supportNeighbor_lower
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ v, G.degree v = q) (S : Finset V)
    (hSq : S.card ≤ q) :
    S.card * (q - S.card + 1) ≤
      (Finset.univ.filter fun v =>
        (G.neighborFinset v ∩ S).card = 1).card := by
  apply card_eq_one_lower_of_sum_and_pair_budget
    (fun v => (G.neighborFinset v ∩ S).card) S.card q hSq
  · rw [sum_card_neighbor_inter_eq_sum_degree]
    simp [hreg]
  · exact sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      G hfree S

#print axioms card_eq_one_lower_of_sum_and_pair_budget
#print axioms c4Free_regular_card_one_supportNeighbor_lower

end Erdos85
