import Proofs.Erdos85TaggedFactorization
import Proofs.Erdos85UniqueIntermediateBoundary

/-!
# Tagged middle coordinates at the second-order boundary

Between two distinct defect components, the global square identity supplies
one common neighbour.  Parametrizing every defect component transports this
to a unique pair consisting of the intermediate component tag and its cyclic
coordinate.  This is the graph-facing source of the tagged additive
factorization.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Coordinate form of the unique common-neighbour statement, with the
intermediate defect component retained as a tag. -/
theorem secondOrder_unique_tagged_middle_coordinate
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    {Z : Type*} [Fintype Z]
    {c e : (secondOrderDefectGraph G).ConnectedComponent} (hce : c ≠ e)
    (u v : Z → V)
    (huRange : Set.range u = c.supp)
    (hvRange : Set.range v = e.supp)
    (w : (secondOrderDefectGraph G).ConnectedComponent → Z → V)
    (hwInj : ∀ k, Function.Injective (w k))
    (hwRange : ∀ k, Set.range (w k) = k.supp) :
    ∀ x y : Z, ∃! p : Σ _k : (secondOrderDefectGraph G).ConnectedComponent, Z,
      G.Adj (u x) (w p.1 p.2) ∧ G.Adj (w p.1 p.2) (v y) := by
  intro x y
  let D := secondOrderDefectGraph G
  have hux : u x ∈ c.supp := by rw [← huRange]; exact ⟨x, rfl⟩
  have hvy : v y ∈ e.supp := by rw [← hvRange]; exact ⟨y, rfl⟩
  have hmkx : D.connectedComponentMk (u x) = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c (u x)).mp hux
  have hmky : D.connectedComponentMk (v y) = e :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff e (v y)).mp hvy
  have hxy : u x ≠ v y := by
    intro huv
    apply hce
    rw [← hmkx, ← hmky, huv]
  have hDxy : ¬ D.Adj (u x) (v y) := by
    intro hadj
    apply hce
    rw [← hmkx, ← hmky]
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hadj
  have hnotmem : v y ∉ D.neighborFinset (u x) := by
    simpa only [SimpleGraph.mem_neighborFinset] using hDxy
  have hcommon := card_common_eq_if_secondOrderDefect_of_even
    G hfree hd heven hmin hcard (u x) (v y) hxy
  rw [if_neg hnotmem] at hcommon
  obtain ⟨q, hqset⟩ := Finset.card_eq_one.mp hcommon
  have hqmem : q ∈ G.neighborFinset (u x) ∩ G.neighborFinset (v y) := by
    rw [hqset]
    simp
  have hqu : G.Adj (u x) q :=
    (G.mem_neighborFinset (u x) q).mp (Finset.mem_inter.mp hqmem).1
  have hqv : G.Adj q (v y) :=
    ((G.mem_neighborFinset (v y) q).mp (Finset.mem_inter.mp hqmem).2).symm
  let k : D.ConnectedComponent := D.connectedComponentMk q
  have hqk : q ∈ k.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff k q).mpr rfl
  have hqrange : q ∈ Set.range (w k) := by
    rw [hwRange k]
    exact hqk
  obtain ⟨z, hz⟩ := hqrange
  let p : Σ _k : D.ConnectedComponent, Z := ⟨k, z⟩
  refine ⟨p, ?_, ?_⟩
  · simpa [p, hz] using And.intro hqu hqv
  · rintro ⟨k', z'⟩ hp'
    have hp'mem : w k' z' ∈
        G.neighborFinset (u x) ∩ G.neighborFinset (v y) := by
      exact Finset.mem_inter.mpr ⟨
        (G.mem_neighborFinset (u x) _).mpr hp'.1,
        (G.mem_neighborFinset (v y) _).mpr hp'.2.symm⟩
    rw [hqset] at hp'mem
    have hp'q : w k' z' = q := Finset.mem_singleton.mp hp'mem
    have hp'supp : w k' z' ∈ k'.supp := by
      rw [← hwRange k']
      exact ⟨z', rfl⟩
    have hp'mk : D.connectedComponentMk (w k' z') = k' :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff k' _).mp hp'supp
    have htag : k' = k := by
      rw [← hp'mk, hp'q]
    subst k'
    have hz' : z' = z := hwInj k (hp'q.trans hz.symm)
    subst z'
    rfl

end

end Erdos85
