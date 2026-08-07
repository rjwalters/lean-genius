import Proofs.Erdos85RamseyPlateau

/-!
# Connected components and safe attachment sets

Choosing one vertex from each connected component always gives a
common-neighbour-independent set.  Thus the number of components is a
universal lower bound for the conflict independence number, and a plateau
core of degree `d` has fewer than `d` components.
-/

namespace Erdos85

open SimpleGraph

noncomputable def connectedComponentRepresentative
    {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent) : V :=
  Classical.choose c.nonempty_supp

theorem connectedComponentRepresentative_mem
    {V : Type*} (G : SimpleGraph V) (c : G.ConnectedComponent) :
    connectedComponentRepresentative G c ∈ c.supp :=
  Classical.choose_spec c.nonempty_supp

theorem connectedComponentRepresentative_injective
    {V : Type*} (G : SimpleGraph V) :
    Function.Injective (connectedComponentRepresentative G) := by
  intro c e hce
  have hc := (SimpleGraph.ConnectedComponent.mem_supp_iff c
    (connectedComponentRepresentative G c)).mp
      (connectedComponentRepresentative_mem G c)
  have he := (SimpleGraph.ConnectedComponent.mem_supp_iff e
    (connectedComponentRepresentative G e)).mp
      (connectedComponentRepresentative_mem G e)
  rw [hce] at hc
  exact hc.symm.trans he

/-- Representatives of distinct connected components cannot have a common
neighbor. -/
theorem connectedComponentRepresentatives_commonNeighbors_eq_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {c e : G.ConnectedComponent} (hce : c ≠ e) :
    G.neighborFinset (connectedComponentRepresentative G c) ∩
      G.neighborFinset (connectedComponentRepresentative G e) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro z hz
  simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hz
  have hcRep := (SimpleGraph.ConnectedComponent.mem_supp_iff c
    (connectedComponentRepresentative G c)).mp
      (connectedComponentRepresentative_mem G c)
  have heRep := (SimpleGraph.ConnectedComponent.mem_supp_iff e
    (connectedComponentRepresentative G e)).mp
      (connectedComponentRepresentative_mem G e)
  have hcz := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hz.1
  have hez := SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hz.2
  apply hce
  rw [← hcRep, ← heRep]
  exact hcz.trans hez.symm

/-- The conflict independence number is at least the number of connected
components of the original graph. -/
theorem card_connectedComponents_le_conflict_indepNum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [Fintype G.ConnectedComponent] [DecidableEq G.ConnectedComponent] :
    Fintype.card G.ConnectedComponent ≤
      (commonNeighborConflict G).indepNum := by
  let S : Finset V := Finset.univ.image (connectedComponentRepresentative G)
  have hcard : S.card = Fintype.card G.ConnectedComponent := by
    dsimp only [S]
    rw [Finset.card_image_of_injective _
      (connectedComponentRepresentative_injective G), Finset.card_univ]
  have hind : (commonNeighborConflict G).IsIndepSet S := by
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy hconf
    change x ∈ Finset.univ.image (connectedComponentRepresentative G) at hx
    change y ∈ Finset.univ.image (connectedComponentRepresentative G) at hy
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hy
    have hce : c ≠ e := by
      intro h
      subst e
      exact hxy rfl
    have hempty :=
      connectedComponentRepresentatives_commonNeighbors_eq_empty G hce
    rw [commonNeighborConflict_adj_iff] at hconf
    rw [hempty] at hconf
    exact Finset.not_nonempty_empty hconf.2
  rw [← hcard]
  exact hind.card_le_indepNum

/-- Every plateau core of degree `d` has fewer than `d` connected
components. -/
theorem C4PlateauCore.connectedComponent_count_lt {m d : ℕ}
    (hcore : C4PlateauCore m d) :
    ∃ (G : SimpleGraph (Fin m)) (_ : DecidableRel G.Adj),
      G.minDegree = d ∧ ¬ containsC4 (Fin m) G ∧
      Fintype.card G.ConnectedComponent < d := by
  obtain ⟨G, hdec, hmin, hfree, -, hind⟩ := hcore.conflict_indepNum_lt
  letI : DecidableRel G.Adj := hdec
  letI : DecidableEq G.ConnectedComponent := Classical.decEq _
  refine ⟨G, hdec, hmin, hfree, ?_⟩
  exact (card_connectedComponents_le_conflict_indepNum G).trans_lt hind

end Erdos85
