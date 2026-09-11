import Proofs.Erdos85GadgetCounting

/-!
# Capacity and equality in a graph incidence count

If all neighbours of a finite set `A` lie among receivers `D`, and each
receiver meets `A` at most once, the degree sum on `A` is at most `card D`.
Equality forces every receiver to meet `A` exactly once. These statements
package the incidence argument for the attached sets in Erdős problem 85.
-/

namespace Erdos85

/-- At most one incidence per allowed receiver bounds the degree sum. -/
theorem sum_degree_le_card_receivers
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A D : Finset V)
    (hzero : ∀ v, v ∉ D → (G.neighborFinset v ∩ A).card = 0)
    (hcap : ∀ v, (G.neighborFinset v ∩ A).card ≤ 1) :
    (∑ a ∈ A, G.degree a) ≤ D.card := by
  classical
  have hpoint : ∀ v : V,
      (G.neighborFinset v ∩ A).card ≤ if v ∈ D then 1 else 0 := by
    intro v
    split_ifs with hv
    · exact hcap v
    · rw [hzero v hv]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v)
  rw [sum_card_neighbor_inter_eq_sum_degree G A] at h
  simpa using h

/-- Equality in the incidence bound forces every receiver to be used. -/
theorem card_neighbor_inter_eq_one_of_receiver_capacity_equality
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A D : Finset V)
    (hzero : ∀ v, v ∉ D → (G.neighborFinset v ∩ A).card = 0)
    (hcap : ∀ v, (G.neighborFinset v ∩ A).card ≤ 1)
    (heq : (∑ a ∈ A, G.degree a) = D.card) (v : V) (hv : v ∈ D) :
    (G.neighborFinset v ∩ A).card = 1 := by
  classical
  have hpoint : ∀ w : V,
      (G.neighborFinset w ∩ A).card ≤ if w ∈ D then 1 else 0 := by
    intro w
    split_ifs with hw
    · exact hcap w
    · rw [hzero w hw]
  have hsum : (∑ w : V, (G.neighborFinset w ∩ A).card) =
      ∑ w : V, if w ∈ D then 1 else 0 := by
    rw [sum_card_neighbor_inter_eq_sum_degree G A, heq]
    simp
  have hall := (Finset.sum_eq_sum_iff_of_le
    (s := Finset.univ) (fun w _ => hpoint w)).mp hsum
  simpa only [if_pos hv] using hall v (Finset.mem_univ v)

end Erdos85
