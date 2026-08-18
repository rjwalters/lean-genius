import Proofs.Erdos85SecondOrderQuotient

/-!
# Cross-component pair counting for the second-order defect partition

Two distinct vertices lying in different components of the second-order
defect graph have exactly one common neighbor: zero common neighbors would
make the pair defect-adjacent (antipodal or triangle-free, both zero-common
relations), placing them in one component, while two common neighbors form
a four-cycle.

Summing over all cross pairs gives the exact product formula
`Σ_z |N(z) ∩ c| · |N(z) ∩ c'| = |c| · |c'|` for distinct components
`c ≠ c'`.  This is the counting input for the minimum-sector assembly
terminal.
-/

namespace Erdos85

open SimpleGraph

/-- **Cross-component pairs have exactly one common neighbor.**  Vertices in
distinct components of the second-order defect graph are not defect-adjacent,
hence have at least one common neighbor; `C4`-freeness caps the count at
one. -/
theorem card_common_eq_one_of_componentMk_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {x y : V}
    (hne : (secondOrderDefectGraph G).connectedComponentMk x ≠
      (secondOrderDefectGraph G).connectedComponentMk y) :
    (G.neighborFinset x ∩ G.neighborFinset y).card = 1 := by
  have hxy : x ≠ y := by
    rintro rfl
    exact hne rfl
  have hnadj : ¬ (secondOrderDefectGraph G).Adj x y := by
    intro h
    exact hne (SimpleGraph.ConnectedComponent.sound h.reachable)
  have hpos : (G.neighborFinset x ∩ G.neighborFinset y).card ≠ 0 := by
    intro h0
    apply hnadj
    rw [secondOrderDefectGraph, SimpleGraph.sup_adj]
    by_cases hadj : G.Adj x y
    · refine Or.inr ?_
      rw [triangleFreeEdgeGraph_adj, mem_triangleFreeNeighbors]
      exact ⟨hadj, h0⟩
    · refine Or.inl ?_
      rw [antipodalGraph_adj, mem_antipodalNeighbors]
      exact ⟨hxy.symm, hadj, h0⟩
  have hle : (G.neighborFinset x ∩ G.neighborFinset y).card ≤ 1 := by
    by_contra hlt
    push Not at hlt
    obtain ⟨v, hv, v', hv', hvv⟩ := Finset.one_lt_card.mp hlt
    rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset,
      SimpleGraph.mem_neighborFinset] at hv hv'
    exact hfree (containsC4_of_two_common hxy hvv hv.1.symm hv.2.symm
      hv'.1.symm hv'.2.symm)
  omega

/-- **Exact cross product formula.**  For distinct components `c ≠ c'` of
the second-order defect graph, summing the product of neighbor counts over
all vertices counts each of the `|c| · |c'|` cross pairs exactly once. -/
theorem sum_componentNeighborCard_mul_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) (hne : c ≠ c') :
    (∑ z : V,
        (componentNeighborFinset G (secondOrderDefectGraph G) c z).card *
          (componentNeighborFinset G (secondOrderDefectGraph G) c' z).card) =
      c.supp.ncard * c'.supp.ncard := by
  have hcfin : c.supp.Finite := Set.toFinite c.supp
  have hcfin' : c'.supp.Finite := Set.toFinite c'.supp
  let cs : Finset V := hcfin.toFinset
  let cs' : Finset V := hcfin'.toFinset
  have hcardc : cs.card = c.supp.ncard :=
    (Set.ncard_eq_toFinset_card c.supp hcfin).symm
  have hcardc' : cs'.card = c'.supp.ncard :=
    (Set.ncard_eq_toFinset_card c'.supp hcfin').symm
  have hmemc : ∀ w : V, w ∈ cs ↔
      (secondOrderDefectGraph G).connectedComponentMk w = c := by
    intro w
    simp [cs, SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hmemc' : ∀ w : V, w ∈ cs' ↔
      (secondOrderDefectGraph G).connectedComponentMk w = c' := by
    intro w
    simp [cs', SimpleGraph.ConnectedComponent.mem_supp_iff]
  have hcount : ∀ z : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c z).card =
        ∑ x ∈ cs, (if G.Adj z x then 1 else 0) := by
    intro z
    have hfilter :
        componentNeighborFinset G (secondOrderDefectGraph G) c z =
          cs.filter (fun w => G.Adj z w) := by
      ext w
      simp only [componentNeighborFinset, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset, hmemc w]
      tauto
    rw [hfilter, Finset.card_filter]
  have hcount' : ∀ z : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c' z).card =
        ∑ y ∈ cs', (if G.Adj z y then 1 else 0) := by
    intro z
    have hfilter :
        componentNeighborFinset G (secondOrderDefectGraph G) c' z =
          cs'.filter (fun w => G.Adj z w) := by
      ext w
      simp only [componentNeighborFinset, Finset.mem_filter,
        SimpleGraph.mem_neighborFinset, hmemc' w]
      tauto
    rw [hfilter, Finset.card_filter]
  have hcommon : ∀ x ∈ cs, ∀ y ∈ cs',
      (∑ z : V, (if G.Adj z x then 1 else 0) *
        (if G.Adj z y then 1 else 0)) = 1 := by
    intro x hx y hy
    have hxc := (hmemc x).mp hx
    have hyc := (hmemc' y).mp hy
    have hxyne :
        (secondOrderDefectGraph G).connectedComponentMk x ≠
          (secondOrderDefectGraph G).connectedComponentMk y := by
      rw [hxc, hyc]
      exact hne
    have hone := card_common_eq_one_of_componentMk_ne G hfree hxyne
    have hinter :
        G.neighborFinset x ∩ G.neighborFinset y =
          Finset.univ.filter (fun z : V => G.Adj z x ∧ G.Adj z y) := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ,
        true_and, SimpleGraph.mem_neighborFinset]
      rw [G.adj_comm x z, G.adj_comm y z]
    calc
      (∑ z : V, (if G.Adj z x then 1 else 0) *
          (if G.Adj z y then 1 else 0)) =
          ∑ z : V, (if G.Adj z x ∧ G.Adj z y then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases h1 : G.Adj z x <;> by_cases h2 : G.Adj z y <;>
          simp [h1, h2]
      _ = (Finset.univ.filter
            (fun z : V => G.Adj z x ∧ G.Adj z y)).card :=
        (Finset.card_filter _ _).symm
      _ = (G.neighborFinset x ∩ G.neighborFinset y).card := by
        rw [hinter]
      _ = 1 := hone
  calc
    (∑ z : V,
        (componentNeighborFinset G (secondOrderDefectGraph G) c z).card *
          (componentNeighborFinset G (secondOrderDefectGraph G) c' z).card) =
        ∑ z : V, (∑ x ∈ cs, (if G.Adj z x then 1 else 0)) *
          (∑ y ∈ cs', (if G.Adj z y then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [hcount z, hcount' z]
    _ = ∑ z : V, ∑ x ∈ cs, ∑ y ∈ cs',
          (if G.Adj z x then 1 else 0) * (if G.Adj z y then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_mul_sum]
    _ = ∑ x ∈ cs, ∑ y ∈ cs', ∑ z : V,
          (if G.Adj z x then 1 else 0) * (if G.Adj z y then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = ∑ x ∈ cs, ∑ y ∈ cs', 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact hcommon x hx y hy
    _ = cs.card * cs'.card := by
      simp
    _ = c.supp.ncard * c'.supp.ncard := by
      rw [hcardc, hcardc']

end Erdos85
