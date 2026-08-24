import Proofs.Erdos85EulerianCutParity

/-!
# Componentwise cut parity in an Eulerian graph

The global paired-star relay graph in the Baer coupling audit is Eulerian.
This file records the componentwise form of its cut law: every connected
component contains an even number of edges crossing any prescribed vertex
shore.  This is equation (73rnz_cjibkp), the unpriced owner-flow invariant.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The vertices of a connected component, as a finset. -/
def connectedComponentFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} (c : H.ConnectedComponent) : Finset V :=
  by
    classical
    exact Finset.univ.filter fun v => v ∈ c.supp

/-- Cut incidences whose endpoint on the chosen shore lies in `c`.
Because no graph edge leaves a connected component, this counts precisely
the cut edges lying in that component. -/
def componentGraphCutMass
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : H.ConnectedComponent) (S : Finset V) : ℕ :=
  ∑ v ∈ S ∩ connectedComponentFinset c,
    (H.neighborFinset v \ S).card

private theorem neighbor_mem_component_of_mem_component
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : H.ConnectedComponent) {u v : V}
    (hu : u ∈ c.supp) (huv : H.Adj u v) : v ∈ c.supp := by
  rw [ConnectedComponent.mem_supp_iff] at hu ⊢
  exact (ConnectedComponent.connectedComponentMk_eq_of_adj huv).symm.trans hu

/-- Restricting the shore to one component does not change the cut mass
inside that component. -/
theorem graphCutMass_inter_connectedComponentFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (c : H.ConnectedComponent) (S : Finset V) :
    graphCutMass H (S ∩ connectedComponentFinset c) =
      componentGraphCutMass H c S := by
  classical
  simp only [graphCutMass, componentGraphCutMass]
  apply Finset.sum_congr rfl
  intro u hu
  have huS : u ∈ S := (Finset.mem_inter.mp hu).1
  have huc : u ∈ c.supp := by
    simpa [connectedComponentFinset] using (Finset.mem_inter.mp hu).2
  congr 1
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨hvn, hvout⟩
    have hadj : H.Adj u v := by
      simpa [SimpleGraph.mem_neighborFinset] using hvn
    have hvc : v ∈ connectedComponentFinset c := by
      simp only [connectedComponentFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact neighbor_mem_component_of_mem_component H c huc hadj
    exact ⟨hvn, fun hvS => hvout ⟨hvS, hvc⟩⟩
  · rintro ⟨hvn, hvout⟩
    exact ⟨hvn, fun hv => hvout hv.1⟩

/-- **Componentwise Eulerian cut parity (73rnz_cjibkp).**  In a finite
even-degree graph, every connected component contains an even number of
edges crossing a prescribed vertex shore. -/
theorem even_componentGraphCutMass_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, Even (H.degree v))
    (c : H.ConnectedComponent) (S : Finset V) :
    Even (componentGraphCutMass H c S) := by
  rw [← graphCutMass_inter_connectedComponentFinset H c S]
  exact even_graphCutMass_of_even_degree H hdegree _

/-- Owner-flow consequence of componentwise cut parity.  If the crossings in
one component split into marked pole crossings and ordinary crossings, then
an odd marked population forces an odd (hence nonempty) ordinary population.
This is the count-level form of “an owner cannot terminate in its component.” -/
theorem odd_ordinary_crossings_of_odd_marked_crossings
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, Even (H.degree v))
    (c : H.ConnectedComponent) (S : Finset V)
    (marked ordinary : ℕ)
    (hsplit : componentGraphCutMass H c S = marked + ordinary)
    (hmarked : Odd marked) :
    Odd ordinary ∧ 0 < ordinary := by
  have htotal := even_componentGraphCutMass_of_even_degree H hdegree c S
  rw [hsplit] at htotal
  rcases htotal with ⟨k, hk⟩
  rcases hmarked with ⟨m, hm⟩
  have hordinary : Odd ordinary := by
    use k - m - 1
    omega
  exact ⟨hordinary, hordinary.pos⟩

end

end Erdos85

#print axioms Erdos85.graphCutMass_inter_connectedComponentFinset
#print axioms Erdos85.even_componentGraphCutMass_of_even_degree
#print axioms Erdos85.odd_ordinary_crossings_of_odd_marked_crossings
