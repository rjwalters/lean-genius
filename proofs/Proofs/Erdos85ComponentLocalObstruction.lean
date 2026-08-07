import Proofs.Erdos85ComponentwiseNonextension

/-!
# Connected components as exact local obstructions

Edge-minimal normalization says every edge has a minimum-degree endpoint.
Consequently every connected component of a normalized witness has minimum
degree exactly `d`: it inherits the lower bound, and any edge supplies a
degree-`d` endpoint.  Proper components of a plateau core also inherit
one-step nonextension.
-/

namespace Erdos85

open SimpleGraph

/-- All neighbors of a vertex lie in its connected component. -/
theorem neighborSet_subset_connectedComponent_supp
    {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent)
    (x : c.supp) : G.neighborSet x.1 ⊆ c.supp := by
  intro y hxy
  have hxMk : G.connectedComponentMk x.1 = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c x.1).mp x.2
  have hxyMk :=
    SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy
  exact (SimpleGraph.ConnectedComponent.mem_supp_iff c y).mpr
    (hxyMk.symm.trans hxMk)

/-- Inducing on a connected component preserves every vertex degree. -/
theorem degree_induce_connectedComponent_supp
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : G.ConnectedComponent) (x : c.supp) :
    (G.induce c.supp).degree x = G.degree x.1 := by
  exact G.degree_induce_of_neighborSet_subset
    (neighborSet_subset_connectedComponent_supp G c x)

/-- A connected component of a normalized minimum-degree witness has exact
minimum degree `d`. -/
theorem minDegree_induce_connectedComponent_eq_of_edge_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ} (hd : 1 ≤ d)
    (hmin : G.minDegree = d)
    (hcover : ∀ ⦃u v⦄, G.Adj u v →
      G.degree u = d ∨ G.degree v = d)
    (c : G.ConnectedComponent) :
    (G.induce c.supp).minDegree = d := by
  classical
  let H := G.induce c.supp
  letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
  have hminH : d ≤ H.minDegree := by
    apply H.le_minDegree_of_forall_le_degree
    intro x
    rw [degree_induce_connectedComponent_supp G c x]
    exact hmin.ge.trans (G.minDegree_le_degree x.1)
  let x : c.supp := Classical.choice inferInstance
  have hxpos : 0 < G.degree x.1 := by
    have hx := hmin.ge.trans (G.minDegree_le_degree x.1)
    omega
  have hxN : (G.neighborFinset x.1).Nonempty := by
    rw [← Finset.card_pos, G.card_neighborFinset_eq_degree]
    exact hxpos
  obtain ⟨y, hy⟩ := hxN
  have hxy : G.Adj x.1 y := (G.mem_neighborFinset x.1 y).mp hy
  have hySupp : y ∈ c.supp :=
    neighborSet_subset_connectedComponent_supp G c x hxy
  let y' : c.supp := ⟨y, hySupp⟩
  rcases hcover hxy with hxTight | hyTight
  · apply le_antisymm
    · calc
        H.minDegree ≤ H.degree x := H.minDegree_le_degree x
        _ = G.degree x.1 := degree_induce_connectedComponent_supp G c x
        _ = d := hxTight
    · exact hminH
  · apply le_antisymm
    · calc
        H.minDegree ≤ H.degree y' := H.minDegree_le_degree y'
        _ = G.degree y := degree_induce_connectedComponent_supp G c y'
        _ = d := hyTight
    · exact hminH

/-- Restricting a C₄-free graph to one component remains C₄-free. -/
theorem not_containsC4_induce_connectedComponent
    {V : Type*} (G : SimpleGraph V)
    (hfree : ¬ containsC4 V G) (c : G.ConnectedComponent) :
    ¬ containsC4 c.supp (G.induce c.supp) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  exact ⟨fun i ↦ (f i).1, Subtype.val_injective.comp hf,
    fun i j hij ↦ hadj i j hij⟩

/-- Every component of a plateau core is an exact-degree normalized local
obstruction; every proper component is additionally one-step nonextendable. -/
theorem C4PlateauCore.exists_component_local_obstructions
    {m d : ℕ} (hm : 4 ≤ m) (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      ∀ c : G.ConnectedComponent,
        let H := G.induce c.supp
        H.minDegree = d ∧
        ¬ containsC4 c.supp H ∧
        (∀ ⦃u v : c.supp⦄, H.Adj u v →
          H.degree u = d ∨ H.degree v = d) ∧
        (c.supp.ncard < m →
          ¬ C4FreeMinDegreeWitness (c.supp.ncard + 1) d) := by
  have hd : 1 ≤ d := by
    have := hcore.two_le_degree hm
    omega
  rcases hcore with ⟨G, hdec, hmin, hfree, hcover, hnext⟩
  letI : DecidableRel G.Adj := hdec
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  intro c
  dsimp
  refine ⟨minDegree_induce_connectedComponent_eq_of_edge_cover
      G hd hmin (hcover := fun {u v} huv ↦ hcover huv) c,
    not_containsC4_induce_connectedComponent G hfree c, ?_, ?_⟩
  · intro u v huv
    have huvG : G.Adj u.1 v.1 := huv
    rcases hcover huvG with hu | hv
    · left
      rw [degree_induce_connectedComponent_supp G c u]
      exact hu
    · right
      rw [degree_induce_connectedComponent_supp G c v]
      exact hv
  · intro hc hext
    have hglobal := c4FreeMinDegreeWitness_succ_of_component_extension
      G hfree hmin.ge c (by simpa using hc) hext
    have hglobal' : C4FreeMinDegreeWitness (m + 1) d := by
      simpa using hglobal
    rcases hglobal' with ⟨H, hHdec, hHmin, hHfree⟩
    exact hHfree (hnext H hHdec hHmin)

end Erdos85
