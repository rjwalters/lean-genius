import Proofs.Erdos85SquareOrderTwoHighTerminal

/-! A saturated matching between equally sized blocks supplies a labeling equivalence. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem saturated_neighbor_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hle : ∀ x ∈ A, (G.neighborFinset x ∩ B).card ≤ 1)
    (hmass : (∑ x ∈ A, (G.neighborFinset x ∩ B).card) = A.card) :
    ∀ x ∈ A, (G.neighborFinset x ∩ B).card = 1 := by
  apply (Finset.sum_eq_sum_iff_of_le hle).mp
  simpa using hmass

theorem saturated_neighbor_blocks_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcard : A.card = B.card)
    (hA : ∀ x ∈ A, (G.neighborFinset x ∩ B).card ≤ 1)
    (hB : ∀ y ∈ B, (G.neighborFinset y ∩ A).card ≤ 1)
    (hmass : (∑ x ∈ A, (G.neighborFinset x ∩ B).card) = A.card) :
    ∃ e : (↑A : Set V) ≃ (↑B : Set V),
      ∀ (x : (↑A : Set V)) (y : (↑B : Set V)), G.Adj x.val y.val ↔ e x = y := by
  classical
  have hcA := saturated_neighbor_cards G A B hA hmass
  have hmassB : (∑ y ∈ B, (G.neighborFinset y ∩ A).card) = B.card := by
    rw [← sum_card_neighbor_inter_comm G A B, hmass, hcard]
  have hcB := saturated_neighbor_cards G B A hB hmassB
  have hex (x : (↑A : Set V)) : ∃ y : (↑B : Set V), G.Adj x.val y.val := by
    have hp : 0 < (G.neighborFinset x.val ∩ B).card := by rw [hcA x.val x.property]; decide
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hp
    exact ⟨⟨y, (Finset.mem_inter.mp hy).2⟩, (G.mem_neighborFinset x.val y).mp (Finset.mem_inter.mp hy).1⟩
  let f : (↑A : Set V) → (↑B : Set V) := fun x => Classical.choose (hex x)
  have hf (x : (↑A : Set V)) : G.Adj x.val (f x).val := Classical.choose_spec (hex x)
  have huniq (x : (↑A : Set V)) (y : (↑B : Set V)) (hxy : G.Adj x.val y.val) : f x = y := by
    apply Subtype.ext
    exact Finset.card_le_one.mp (hA x.val x.property) (f x).val
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x.val (f x).val).mpr (hf x), (f x).property⟩)
      y.val (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset x.val y.val).mpr hxy, y.property⟩)
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hy : G.Adj (f x).val y.val := by rw [hxy]; exact (hf y).symm
    exact Finset.card_le_one.mp (hB (f x).val (f x).property) x.val
      (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset (f x).val x.val).mpr (hf x).symm, x.property⟩)
      y.val (Finset.mem_inter.mpr ⟨(G.mem_neighborFinset (f x).val y.val).mpr hy, y.property⟩)
  have hsurj : Function.Surjective f := by
    intro y
    have hp : 0 < (G.neighborFinset y.val ∩ A).card := by rw [hcB y.val y.property]; decide
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hp
    let a : (↑A : Set V) := ⟨x, (Finset.mem_inter.mp hx).2⟩
    exact ⟨a, huniq a y ((G.mem_neighborFinset y.val x).mp (Finset.mem_inter.mp hx).1).symm⟩
  refine ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, ?_⟩
  intro x y
  change G.Adj x.val y.val ↔ f x = y
  constructor
  · exact huniq x y
  · intro he
    rw [← he]
    exact hf x

end
end Erdos85
#print axioms Erdos85.saturated_neighbor_blocks_equiv
