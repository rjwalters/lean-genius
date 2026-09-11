import Proofs.Erdos85Problem

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
