import Proofs.Erdos85ThreeSeparatorPositiveSpikeWingDecomposition

/-! # Exact wing matching at the positive-spike endpoint -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Equal finite wings are matched exactly when every source has a unique
routed target and distinct sources have disjoint ambient neighborhoods. -/
theorem exists_equiv_of_unique_commonNeighbor_in_equal_wing
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (Xw Rw : Finset V) (w : V)
    (hcard : Xw.card = Rw.card)
    (hroute : ∀ x ∈ Xw, ∃! r, r ∈ Rw ∧ G.Adj x r ∧ G.Adj w r)
    (hdisjoint : ∀ x ∈ Xw, ∀ y ∈ Xw, x ≠ y →
      Disjoint (G.neighborFinset x) (G.neighborFinset y)) :
    ∃ e : Xw ≃ Rw, ∀ x : Xw,
      G.Adj x.1 (e x).1 ∧ G.Adj w (e x).1 := by
  let f : Xw → Rw := fun x =>
    ⟨Classical.choose (hroute x.1 x.2),
      (Classical.choose_spec (hroute x.1 x.2)).1.1⟩
  have hfroute : ∀ x : Xw, G.Adj x.1 (f x).1 ∧ G.Adj w (f x).1 := by
    intro x
    exact (Classical.choose_spec (hroute x.1 x.2)).1.2
  have hfinj : Function.Injective f := by
    intro x y hxy
    by_contra hne
    have hvalne : x.1 ≠ y.1 := by
      intro h
      exact hne (Subtype.ext h)
    have hd := hdisjoint x.1 x.2 y.1 y.2 hvalne
    have hxmem : (f x).1 ∈ G.neighborFinset x.1 := by
      simpa [SimpleGraph.mem_neighborFinset] using (hfroute x).1
    have hymem : (f x).1 ∈ G.neighborFinset y.1 := by
      have := (hfroute y).1
      rw [← hxy] at this
      simpa [SimpleGraph.mem_neighborFinset] using this
    exact Finset.disjoint_left.mp hd hxmem hymem
  have hcards : Fintype.card Xw = Fintype.card Rw := by
    simpa using hcard
  have hfbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).2 ⟨hfinj, hcards⟩
  let e : Xw ≃ Rw := Equiv.ofBijective f hfbij
  refine ⟨e, ?_⟩
  intro x
  exact hfroute x

#print axioms exists_equiv_of_unique_commonNeighbor_in_equal_wing

end

end Erdos85
