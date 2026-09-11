import Proofs.Erdos85GadgetCounting


/-!
# A second-neighbour cover bounds degree

In a C₄-free graph, if every neighbour of `a` has a neighbour in a finite set
`B` not containing `a`, then `degree a ≤ card B`. Choosing such a neighbour
defines an injection: two preimages would be two common neighbours of `a`
and a vertex of `B`. This packages the final eight-walk/seven-endpoint
pigeonhole step in the order-seven argument for Erdős problem 85.
-/

namespace Erdos85

/-- A second-neighbour cover excluding the centre has at least its degree. -/
theorem degree_le_card_of_neighbor_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (a : V) (B : Finset V) (ha : a ∉ B)
    (hcover : ∀ u, G.Adj a u → ∃ b ∈ B, G.Adj u b) :
    G.degree a ≤ B.card := by
  classical
  let f : G.neighborSet a → B := fun u =>
    ⟨(hcover u u.property).choose, (hcover u u.property).choose_spec.1⟩
  have hfadj : ∀ u : G.neighborSet a, G.Adj u (f u) := by
    intro u
    exact (hcover u u.property).choose_spec.2
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    by_contra hne
    have hab : a ≠ (f u).val := by
      intro heq
      exact ha (heq.symm ▸ (f u).property)
    have hvb : G.Adj v (f u) := by
      rw [huv]
      exact hfadj v
    exact hfree (containsC4_of_two_common hab hne
      u.property.symm (hfadj u) v.property.symm hvb)
  have h := Fintype.card_le_of_injective f hinj
  simpa only [G.card_neighborSet_eq_degree, Fintype.card_coe] using h

/-- Too few second-neighbour endpoints force a C₄. -/
theorem containsC4_of_neighbor_cover_card_lt_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (ha : a ∉ B)
    (hcover : ∀ u, G.Adj a u → ∃ b ∈ B, G.Adj u b)
    (hcard : B.card < G.degree a) : containsC4 V G := by
  by_contra hfree
  exact (Nat.not_le_of_lt hcard) (degree_le_card_of_neighbor_cover G hfree a B ha hcover)

end Erdos85


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

#print axioms Erdos85.degree_le_card_of_neighbor_cover

#print axioms Erdos85.containsC4_of_neighbor_cover_card_lt_degree

#print axioms Erdos85.sum_degree_le_card_receivers

#print axioms Erdos85.card_neighbor_inter_eq_one_of_receiver_capacity_equality
