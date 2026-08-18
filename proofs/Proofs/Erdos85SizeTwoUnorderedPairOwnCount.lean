import Proofs.Erdos85SizeTwoUnorderedPairRouting

/-!
# The two endpoint services of an unordered outside pair

This packages the label-free hit law as an actual finite set.  It is the
first counting layer for the owner-overlap statistic: an endpoint contributes
one outside neighbour precisely when it avoids both endpoints of the owner's
pair.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Outside neighbours of `z` whose owned pair contains the inside vertex
`u`. -/
def outsidePairServiceFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z : {x : V // x ∉ c.supp}) (u : c.supp) :
    Finset {x : V // x ∉ c.supp} :=
  Finset.univ.filter fun y =>
    G.Adj z.1 y.1 ∧
      u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset

@[simp] theorem mem_outsidePairServiceFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z y : {x : V // x ∉ c.supp}) (u : c.supp) :
    y ∈ outsidePairServiceFinset G c hcard z u ↔
      G.Adj z.1 y.1 ∧
        u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset := by
  simp [outsidePairServiceFinset]

/-- Finite-cardinality form of the unordered-pair hit law. -/
theorem outsidePairServiceFinset_card_eq_one_iff_endpoint_avoidance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z : {x : V // x ∉ c.supp}) (u : c.supp) :
    (outsidePairServiceFinset G c hcard z u).card = 1 ↔
      ∀ w : c.supp,
        w ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset →
          ¬ G.Adj u.1 w.1 := by
  rw [← existsUnique_outsidePair_service_iff_endpoint_avoidance
    G hfree c hcard z u]
  constructor
  · intro hone
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hone
    refine ⟨y, ?_, ?_⟩
    · exact (mem_outsidePairServiceFinset G c hcard z y u).mp (by
        rw [hy]
        simp)
    · intro y' hy'
      have : y' ∈ ({y} : Finset {x : V // x ∉ c.supp}) := by
        rw [← hy]
        simpa using hy'
      simpa using this
  · rintro ⟨y, hy, hyuniq⟩
    apply Finset.card_eq_one.mpr
    refine ⟨y, Finset.ext fun y' => ?_⟩
    simp only [mem_outsidePairServiceFinset, Finset.mem_singleton]
    constructor
    · exact fun hy' => hyuniq y' hy'
    · rintro rfl
      exact hy

/-- Equality of the endpoint sets owned by two outside vertices forces the
owners to agree whenever the component-neighbour selector is injective. -/
theorem outsidePair_eq_of_toFinset_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (z y : {x : V // x ∉ c.supp})
    (hpair :
      (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset =
        (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset) :
    z = y := by
  apply Subtype.ext
  apply hinc
  ext x
  constructor
  · intro hx
    have hxs : x ∈ c.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mpr
        (Finset.mem_filter.mp hx).2
    have hx' : (⟨x, hxs⟩ : c.supp) ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset := by
      rw [outsidePair_toFinset]
      exact Finset.mem_subtype.mpr hx
    rw [hpair, outsidePair_toFinset] at hx'
    exact Finset.mem_subtype.mp hx'
  · intro hx
    have hxs : x ∈ c.supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mpr
        (Finset.mem_filter.mp hx).2
    have hx' : (⟨x, hxs⟩ : c.supp) ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset := by
      rw [outsidePair_toFinset]
      exact Finset.mem_subtype.mpr hx
    rw [← hpair, outsidePair_toFinset] at hx'
    exact Finset.mem_subtype.mp hx'

/-- Distinct endpoints of the owner's pair have disjoint service sets.  If
one outside neighbour serviced both, its two-element owned set would equal
the owner's set; selector injectivity would make it the owner itself,
contradicting looplessness. -/
theorem outsidePairServiceFinset_disjoint_of_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (z : {x : V // x ∉ c.supp}) (u v : c.supp)
    (huv : u ≠ v)
    (hu : u ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset)
    (hv : v ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset) :
    Disjoint (outsidePairServiceFinset G c hcard z u)
      (outsidePairServiceFinset G c hcard z v) := by
  classical
  rw [Finset.disjoint_left]
  intro y hyu hyv
  have hyu' := (mem_outsidePairServiceFinset G c hcard z y u).mp hyu
  have hyv' := (mem_outsidePairServiceFinset G c hcard z y v).mp hyv
  let Pz := (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset
  let Py := (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset
  have hcardPz : Pz.card = 2 := by
    simp [Pz, outsidePair_toFinset,
      componentNeighborSubtypeFinset_card, hcard]
  have hcardPy : Py.card = 2 := by
    simp [Py, outsidePair_toFinset,
      componentNeighborSubtypeFinset_card, hcard]
  have hpairZ : ({u, v} : Finset c.supp) = Pz := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    · simpa [huv, hcardPz]
  have hpairY : ({u, v} : Finset c.supp) = Py := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hyu'.2
      · exact hyv'.2
    · simpa [huv, hcardPy]
  have hzy : z = y := outsidePair_eq_of_toFinset_eq G c hcard hinc z y (by
    change Pz = Py
    rw [← hpairZ, ← hpairY])
  subst y
  exact G.loopless.irrefl z.1 hyu'.1

theorem outsidePairServiceFinset_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z : {x : V // x ∉ c.supp}) (u : c.supp) :
    (outsidePairServiceFinset G c hcard z u).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro y hy y' hy'
  have hy := (mem_outsidePairServiceFinset G c hcard z y u).mp hy
  have hy' := (mem_outsidePairServiceFinset G c hcard z y' u).mp hy'
  apply Subtype.ext
  apply Finset.card_le_one.mp
    (common_le_one_of_not_containsC4 hfree u.1 z.1
      (fun huz => z.2 (huz ▸ u.2)))
  · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨(mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard y u).mp hy.2, hy.1⟩
  · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨(mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard y' u).mp hy'.2, hy'.1⟩

/-- For the two endpoints of an owned pair, each endpoint service fibre has
cardinality zero or one according as the endpoints are adjacent or not. -/
theorem outsidePairServiceFinset_endpoint_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z : {x : V // x ∉ c.supp}) (u v : c.supp)
    (huv : u ≠ v)
    (hu : u ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset)
    (hv : v ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset) :
    (outsidePairServiceFinset G c hcard z u).card =
      if G.Adj u.1 v.1 then 0 else 1 := by
  let P := (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset
  have hcardP : P.card = 2 := by
    simp [P, outsidePair_toFinset,
      componentNeighborSubtypeFinset_card, hcard]
  have hpair : ({u, v} : Finset c.supp) = P := by
    apply Finset.eq_of_subset_of_card_le
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    · simpa [huv, hcardP]
  have hav :
      (∀ w : c.supp, w ∈ P → ¬ G.Adj u.1 w.1) ↔
        ¬ G.Adj u.1 v.1 := by
    rw [← hpair]
    simp [huv, G.loopless.irrefl]
  by_cases huvAdj : G.Adj u.1 v.1
  · rw [if_pos huvAdj]
    have hne : (outsidePairServiceFinset G c hcard z u).card ≠ 1 := by
      intro hone
      have havoid :=
        (outsidePairServiceFinset_card_eq_one_iff_endpoint_avoidance
          G hfree c hcard z u).mp hone
      exact (hav.mp havoid) huvAdj
    have hle := outsidePairServiceFinset_card_le_one G hfree c hcard z u
    omega
  · rw [if_neg huvAdj]
    apply (outsidePairServiceFinset_card_eq_one_iff_endpoint_avoidance
      G hfree c hcard z u).mpr
    exact hav.mpr huvAdj

/-- The owner-overlap count is exactly `0` or `2`: an outside neighbour's
owned pair meets the owner's pair in no ways when the owner endpoints are
adjacent, and in one distinct service for each endpoint otherwise. -/
theorem outsidePair_endpointService_union_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (z : {x : V // x ∉ c.supp}) (u v : c.supp)
    (huv : u ≠ v)
    (hu : u ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset)
    (hv : v ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset) :
    ((outsidePairServiceFinset G c hcard z u) ∪
      (outsidePairServiceFinset G c hcard z v)).card =
        if G.Adj u.1 v.1 then 0 else 2 := by
  rw [Finset.card_union_of_disjoint
    (outsidePairServiceFinset_disjoint_of_mem
      G c hcard hinc z u v huv hu hv),
    outsidePairServiceFinset_endpoint_card G hfree c hcard z u v huv hu hv,
    outsidePairServiceFinset_endpoint_card G hfree c hcard z v u huv.symm hv hu]
  by_cases h : G.Adj u.1 v.1
  · simp [h, G.adj_comm]
  · simp [h, G.adj_comm]

end

end Erdos85

#print axioms Erdos85.outsidePairServiceFinset_card_eq_one_iff_endpoint_avoidance
#print axioms Erdos85.outsidePairServiceFinset_disjoint_of_mem
#print axioms Erdos85.outsidePair_endpointService_union_card
