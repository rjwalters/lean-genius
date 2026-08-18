import Proofs.Erdos85OrderSixtyFourOutsideEdgeBijection
import Proofs.Erdos85OutsideCommonNeighborRouting

/-!
# Routing through the unordered pair owned by an outside vertex

This is the label-free local service law needed after the alternating
joint-eigenline branches.  It identifies absence of an internal common
neighbor with avoidance of both endpoints of the outside vertex's owned
pair, and then invokes cross-component uniqueness to obtain the unique
outside service vertex.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- An inside vertex and an outside owner have no common neighbor inside the
component exactly when the inside vertex avoids both endpoints of the
owner's unordered pair. -/
theorem no_insideCommon_iff_outsidePair_endpoint_avoidance
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (z : {x : V // x ∉ c.supp}) (u : c.supp) :
    (¬ ∃ w : c.supp, G.Adj u.1 w.1 ∧ G.Adj z.1 w.1) ↔
      ∀ w : c.supp,
        w ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset →
          ¬ G.Adj u.1 w.1 := by
  classical
  constructor
  · intro hno w hw huw
    apply hno
    refine ⟨w, huw, ?_⟩
    exact (mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard z w).mp hw |>.symm
  · intro havoid hin
    obtain ⟨w, huw, hzw⟩ := hin
    exact havoid w ((mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard z w).mpr hzw.symm) huw

/-- **Unordered-pair hit law.**  An inside vertex receives a unique service
from an outside neighbor of `z` exactly when it avoids both endpoints of the
pair owned by `z`.  Endpoint membership for the service owner is used instead
of a coordinate label, so the statement does not require an alternating
adjacency eigenline. -/
theorem existsUnique_outsidePair_service_iff_endpoint_avoidance
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
    (∃! y : {x : V // x ∉ c.supp},
      G.Adj z.1 y.1 ∧
        u ∈ (outsidePair G (secondOrderDefectGraph G) c hcard y).toFinset) ↔
      ∀ w : c.supp,
        w ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).toFinset →
          ¬ G.Adj u.1 w.1 := by
  classical
  constructor
  · rintro ⟨y, hy, _hyuniq⟩
    rw [← no_insideCommon_iff_outsidePair_endpoint_avoidance
      G c hcard z u]
    intro hin
    apply (not_exists_outsideCommon_of_exists_insideCommon
      G hfree c u z.1 z.2 hin)
    refine ⟨y, ?_, hy.1⟩
    exact (mem_outsidePair_toFinset_iff_adj
      G (secondOrderDefectGraph G) c hcard y u).mp hy.2
  · intro havoid
    have hno : ¬ ∃ w : c.supp,
        G.Adj u.1 w.1 ∧ G.Adj z.1 w.1 :=
      (no_insideCommon_iff_outsidePair_endpoint_avoidance
        G c hcard z u).mpr havoid
    obtain ⟨y, hy, hyuniq⟩ :=
      existsUnique_outsideCommon_of_no_insideCommon
        G hfree c u z.1 z.2 hno
    refine ⟨y, ⟨hy.2, ?_⟩, ?_⟩
    · exact (mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard y u).mpr hy.1
    · intro y' hy'
      apply hyuniq y'
      exact ⟨(mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard y' u).mp hy'.2, hy'.1⟩

end

end Erdos85

#print axioms Erdos85.no_insideCommon_iff_outsidePair_endpoint_avoidance
#print axioms Erdos85.existsUnique_outsidePair_service_iff_endpoint_avoidance
