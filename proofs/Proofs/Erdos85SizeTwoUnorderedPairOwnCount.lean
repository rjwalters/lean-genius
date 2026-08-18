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

end

end Erdos85

#print axioms Erdos85.outsidePairServiceFinset_card_eq_one_iff_endpoint_avoidance
