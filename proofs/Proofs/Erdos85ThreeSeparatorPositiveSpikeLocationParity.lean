import Proofs.Erdos85ThreeSeparatorEndpointClique

/-!
# Positive-spike location parity

The internal-degree profile on the `X` shore differs from a constant by the
indicator of `K`.  Handshake parity in the induced defect graph therefore
forces the number of `K`-points in an even shore to be even.  This is (B16a).
-/

open Finset SimpleGraph

namespace Erdos85

private theorem even_sum_internal_neighbor_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (X : Finset V) :
    Even (∑ x ∈ X, (D.neighborFinset x ∩ X).card) := by
  have hdegree (x : (X : Set V)) : (D.induce (X : Set V)).degree x =
      (D.neighborFinset x.1 ∩ X).card := by
    let e : (X : Set V) ↪ V := ⟨Subtype.val, Subtype.val_injective⟩
    calc
      (D.induce (X : Set V)).degree x =
          ((D.induce (X : Set V)).neighborFinset x).card :=
        ((D.induce (X : Set V)).card_neighborFinset_eq_degree x).symm
      _ = (((D.induce (X : Set V)).neighborFinset x).map e).card :=
        (Finset.card_map _).symm
      _ = (D.neighborFinset x.1 ∩ X).card := by
        congr 1
        ext z
        simp [e]
  have hsumAttach :
      (∑ x : (X : Set V), (D.neighborFinset x.1 ∩ X).card) =
        ∑ x ∈ X, (D.neighborFinset x ∩ X).card := by
    change (∑ x : (X : Set V), (D.neighborFinset x.1 ∩ X).card) = _
    rw [← X.attach_eq_univ]
    exact Finset.sum_attach X fun x => (D.neighborFinset x ∩ X).card
  have hhandshake :
      ∑ x : (X : Set V), (D.induce (X : Set V)).degree x =
        2 * (D.induce (X : Set V)).edgeFinset.card :=
    (D.induce (X : Set V)).sum_degrees_eq_twice_card_edges
  refine ⟨(D.induce (X : Set V)).edgeFinset.card, ?_⟩
  calc
    ∑ x ∈ X, (D.neighborFinset x ∩ X).card =
        ∑ x : (X : Set V), (D.neighborFinset x.1 ∩ X).card := hsumAttach.symm
    _ = ∑ x : (X : Set V), (D.induce (X : Set V)).degree x := by
      apply Finset.sum_congr rfl
      intro x _
      exact (hdegree x).symm
    _ = 2 * (D.induce (X : Set V)).edgeFinset.card := hhandshake
    _ = (D.induce (X : Set V)).edgeFinset.card +
        (D.induce (X : Set V)).edgeFinset.card := two_mul _

/-- B16a: if the induced-degree profile is
`deg_D[X](x) + 1_(x∈K) = a+1` and `X` has even size, then `K` occupies an
even number of points of `X`. -/
theorem even_card_inter_of_even_shore_internal_indicator_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (X K : Finset V) (a : ℕ) (hXeven : Even X.card)
    (hprofile : ∀ x ∈ X,
      (D.neighborFinset x ∩ X).card + (if x ∈ K then 1 else 0) = a + 1) :
    Even (X ∩ K).card := by
  let I := ∑ x ∈ X, (D.neighborFinset x ∩ X).card
  have hIeven : Even I := by
    exact even_sum_internal_neighbor_cards D X
  have hindicator : (∑ x ∈ X, if x ∈ K then 1 else 0) = (X ∩ K).card := by
    calc
      (∑ x ∈ X, if x ∈ K then 1 else 0) =
          (X.filter fun x => x ∈ K).card := by
        rw [← Finset.sum_filter]
        simp
      _ = (X ∩ K).card := by
        congr 1
  have hsum : I + (X ∩ K).card = (a + 1) * X.card := by
    calc
      I + (X ∩ K).card =
          ∑ x ∈ X, ((D.neighborFinset x ∩ X).card +
            (if x ∈ K then 1 else 0)) := by
              rw [Finset.sum_add_distrib, hindicator]
      _ = ∑ _x ∈ X, (a + 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hprofile x hx
      _ = (a + 1) * X.card := by simp [Nat.mul_comm]
  have htotalEven : Even (I + (X ∩ K).card) := by
    rw [hsum]
    exact hXeven.mul_left (a + 1)
  exact (Nat.even_add.mp htotalEven).mp hIeven

#print axioms even_card_inter_of_even_shore_internal_indicator_profile

end Erdos85
