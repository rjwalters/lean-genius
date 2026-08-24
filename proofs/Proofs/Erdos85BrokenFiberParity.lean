import Proofs.Erdos85C4FreeTrianglePartnerInvolution
import Proofs.Erdos85FinsetInvolutionParity

/-!
# Parity of the Baer broken-edge fiber

At a witness `p`, the neighbor star splits into the canonical
triangle-partner domain and the triangle-free (broken) edges.  The canonical
domain is paired by its involution, so it is even.  Hence an even full star
has an even broken fiber.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a C4-free graph, an even-degree vertex has an even number of incident
triangle-free edges. -/
theorem even_triangleFreeEdge_fiber_of_even_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (p : V) (heven : Even (G.degree p)) :
    Even ((Finset.univ.filter fun x =>
      (triangleFreeEdgeGraph G).Adj p x).card) := by
  classical
  let canonical := Finset.univ.filter fun x =>
    trianglePartnerEligible G p x
  let broken := Finset.univ.filter fun x =>
    (triangleFreeEdgeGraph G).Adj p x
  have hcanonicalEven : Even canonical.card := by
    apply even_card_of_closed_fixedPointFree_involution
      (trianglePartner G p) canonical
    · intro x hx
      have helig : trianglePartnerEligible G p x :=
        by simpa [canonical] using hx
      simpa [canonical] using trianglePartner_closed helig
    · intro x hx
      exact trianglePartner_involutive hfree (by simpa [canonical] using hx)
    · intro x hx
      exact trianglePartner_fixedPointFree (by simpa [canonical] using hx)
  have hdisjoint : Disjoint canonical broken := by
    rw [Finset.disjoint_left]
    intro x hxC hxB
    have helig : trianglePartnerEligible G p x := by
      simpa [canonical] using hxC
    have hbroken : (triangleFreeEdgeGraph G).Adj p x := by
      simpa [broken] using hxB
    exact ((trianglePartnerEligible_iff_not_triangleFreeEdge G p x).1
      helig).2 hbroken
  have hunion : canonical ∪ broken = G.neighborFinset p := by
    ext x
    simp only [canonical, broken, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]
    rw [trianglePartnerEligible_iff_not_triangleFreeEdge G p x]
    constructor
    · rintro (⟨hpx, _⟩ | hbroken)
      · exact hpx
      · exact ((mem_triangleFreeNeighbors G p x).mp
          ((triangleFreeEdgeGraph_adj G p x).mp hbroken)).1
    · intro hpx
      by_cases hbroken : (triangleFreeEdgeGraph G).Adj p x
      · exact Or.inr hbroken
      · exact Or.inl ⟨hpx, hbroken⟩
  have hcard : canonical.card + broken.card = G.degree p := by
    rw [← G.card_neighborFinset_eq_degree p, ← hunion,
      Finset.card_union_of_disjoint hdisjoint]
  obtain ⟨k, hk⟩ := hcanonicalEven
  obtain ⟨m, hm⟩ := heven
  have hbrokenEven : Even broken.card := by
    refine ⟨m - k, ?_⟩
    omega
  exact hbrokenEven

#print axioms even_triangleFreeEdge_fiber_of_even_degree

end

end Erdos85
