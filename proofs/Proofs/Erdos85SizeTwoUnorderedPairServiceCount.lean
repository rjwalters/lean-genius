import Proofs.Erdos85SizeTwoUnorderedPairRouting

/-!
# Exact-one owner-service counts

Node: `SIZE-TWO-EIGENLINE(8)` beneath outline F.3.

This finset wrapper is the direct graph-facing form of the equations in the
finite exterior-owner constraint system.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exterior neighbors of `z` whose owned pair contains the internal vertex
`u`. -/
def outsidePairServiceOwnerFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z : {x : V // x ∉ c.supp}) (u : c.supp) :
    Finset {x : V // x ∉ c.supp} :=
  Finset.univ.filter fun y =>
    G.Adj z.1 y.1 ∧
      u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset

@[simp] theorem mem_outsidePairServiceOwnerFinset_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z y : {x : V // x ∉ c.supp}) (u : c.supp) :
    y ∈ outsidePairServiceOwnerFinset G c hcard z u ↔
      G.Adj z.1 y.1 ∧
        u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset := by
  simp [outsidePairServiceOwnerFinset]

/-- The unordered-pair hit law as an exact finset count: an internal vertex
is contained in exactly one neighboring owner's pair iff it avoids both
endpoints of the current owner's pair. -/
theorem outsidePairServiceOwnerFinset_card_eq_one_iff_endpoint_avoidance
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
    (outsidePairServiceOwnerFinset G c hcard z u).card = 1 ↔
      ∀ w : c.supp,
        w ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset →
          ¬ G.Adj u.1 w.1 := by
  have hroute := existsUnique_outsidePair_service_iff_endpoint_avoidance
    G hfree c hcard z u
  let F := outsidePairServiceOwnerFinset G c hcard z u
  constructor
  · intro hF
    obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hF
    apply hroute.mp
    refine ⟨y, ?_, ?_⟩
    · exact (mem_outsidePairServiceOwnerFinset_iff
        G c hcard z y u).mp (by rw [hy]; simp)
    · intro y' hy'
      have hy'mem : y' ∈ F :=
        (mem_outsidePairServiceOwnerFinset_iff G c hcard z y' u).mpr hy'
      change y' ∈ outsidePairServiceOwnerFinset G c hcard z u at hy'mem
      rw [hy, Finset.mem_singleton] at hy'mem
      exact hy'mem
  · intro havoid
    obtain ⟨y, hy, hyuniq⟩ := hroute.mpr havoid
    rw [Finset.card_eq_one]
    refine ⟨y, ?_⟩
    ext y'
    constructor
    · intro hy'
      rw [Finset.mem_singleton]
      exact hyuniq y'
        ((mem_outsidePairServiceOwnerFinset_iff G c hcard z y' u).mp hy')
    · intro hy'
      rw [Finset.mem_singleton] at hy'
      subst y'
      exact (mem_outsidePairServiceOwnerFinset_iff
        G c hcard z y u).mpr hy

end

end Erdos85

#print axioms Erdos85.outsidePairServiceOwnerFinset_card_eq_one_iff_endpoint_avoidance
