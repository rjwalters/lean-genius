import Proofs.Erdos85ControlledDeletion
import Proofs.Erdos85QuadraticPlateauComponents

/-!
# Nonextension descends to connected components

If one connected component of a C₄-free minimum-degree witness can be
extended by one vertex, retain every other component and take a disjoint
union.  This extends the original graph.  Hence every proper component of a
plateau core is itself a one-step nonextension obstruction.
-/

namespace Erdos85

open SimpleGraph

/-- Extending one proper connected component extends the whole graph. -/
theorem c4FreeMinDegreeWitness_succ_of_component_extension
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hmin : d ≤ G.minDegree)
    (c : G.ConnectedComponent)
    (hcProper : c.supp.ncard < Fintype.card V)
    (hext : C4FreeMinDegreeWitness (c.supp.ncard + 1) d) :
    C4FreeMinDegreeWitness (Fintype.card V + 1) d := by
  classical
  let D : Finset V := c.supp.toFinset
  have hDcard : D.card = c.supp.ncard := by
    dsimp [D]
    exact (Set.ncard_eq_toFinset_card' c.supp).symm
  have hloss : ∀ v : {v : V // v ∉ D},
      (G.neighborFinset v ∩ D).card ≤ 0 := by
    intro v
    rw [Nat.le_zero, Finset.card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hyv : G.Adj v.1 y :=
      (G.mem_neighborFinset v.1 y).mp (Finset.mem_inter.mp hy).1
    have hyc : y ∈ c.supp := by
      simpa [D] using (Finset.mem_inter.mp hy).2
    have hyMk : G.connectedComponentMk y = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mp hyc
    have hvMk : G.connectedComponentMk v.1 = c :=
      (SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hyv).trans hyMk
    have hvc : v.1 ∈ c.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c v.1).mpr hvMk
    exact v.2 (by simpa [D] using hvc)
  have hrest : C4FreeMinDegreeWitness
      (Fintype.card V - c.supp.ncard) d := by
    simpa using c4FreeMinDegreeWitness_delete_vertex_set
      G D (N := Fintype.card V) (d := d) (k := c.supp.ncard) (r := 0)
      rfl hDcard (by omega) hmin hfree hloss
  have hsum := C4FreeMinDegreeWitness.add
    (a := c.supp.ncard + 1)
    (b := Fintype.card V - c.supp.ncard)
    (d := d) (by omega) (by omega) hext hrest
  convert hsum using 1
  omega

/-- In a plateau core, every component other than the whole vertex set is a
one-step nonextension obstruction at the inherited minimum degree. -/
theorem C4PlateauCore.exists_componentwise_nonextension
    {m d : ℕ} (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      ∀ c : G.ConnectedComponent, c.supp.ncard < m →
        ¬ C4FreeMinDegreeWitness (c.supp.ncard + 1) d := by
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  intro c hc hext
  have hglobal := c4FreeMinDegreeWitness_succ_of_component_extension
    G hfree hmin.ge c (by simpa using hc) hext
  have hglobal' : C4FreeMinDegreeWitness (m + 1) d := by
    simpa using hglobal
  rcases hglobal' with ⟨H, hHdec, hHmin, hHfree⟩
  exact hHfree (hnext H hHdec hHmin)

end Erdos85
