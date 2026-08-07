import Proofs.Erdos85CrossComponentPairCount

/-!
# The weighted Gram identity for the boundary component quotient

Grouping the cross-component pair count by the component of the middle
vertex turns it into a statement about the component quotient matrix: for
distinct components `c ≠ c'` of the second-order defect graph,

`Σ_e |e| · Q(e,c) · Q(e,c') = |c| · |c'|`.

This is the off-diagonal of the weighted Gram matrix of `Q` and the
counting spine of the minimum-sector assembly terminal.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Fiberwise evaluation of a quotient-uniform product.**  Summing the
product of neighbor counts toward `c` and `c'` over all vertices equals the
weighted sum of quotient entry products over components. -/
theorem sum_componentNeighborCard_mul_eq_sum_ncard_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ z : V,
        (componentNeighborFinset G (secondOrderDefectGraph G) c z).card *
          (componentNeighborFinset G (secondOrderDefectGraph G) c' z).card) =
      ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
        e.supp.ncard *
          (componentQuotientMatrix G (secondOrderDefectGraph G) e c *
            componentQuotientMatrix G (secondOrderDefectGraph G) e c') := by
  classical
  have hreg : ∀ x : V, (secondOrderDefectGraph G).degree x = 2 :=
    secondOrderDefectGraph_degree_eq_two G hfree hd heven hmin hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_even_real
    G hfree hd heven hmin hcard
  calc
    (∑ z : V,
        (componentNeighborFinset G (secondOrderDefectGraph G) c z).card *
          (componentNeighborFinset G (secondOrderDefectGraph G) c' z).card) =
        ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          ∑ z ∈ Finset.univ.filter
            (fun z : V =>
              (secondOrderDefectGraph G).connectedComponentMk z = e),
            (componentNeighborFinset G (secondOrderDefectGraph G) c z).card *
              (componentNeighborFinset G (secondOrderDefectGraph G)
                c' z).card :=
      (Finset.sum_fiberwise_of_maps_to
        (fun z _ => Finset.mem_univ
          ((secondOrderDefectGraph G).connectedComponentMk z)) _).symm
    _ = ∑ e : (secondOrderDefectGraph G).ConnectedComponent,
          e.supp.ncard *
            (componentQuotientMatrix G (secondOrderDefectGraph G) e c *
              componentQuotientMatrix G (secondOrderDefectGraph G) e c') := by
      apply Finset.sum_congr rfl
      intro e _
      have hfiber :
          Finset.univ.filter
            (fun z : V =>
              (secondOrderDefectGraph G).connectedComponentMk z = e) =
            e.supp.toFinset := by
        ext z
        simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
      have hval : ∀ z ∈ Finset.univ.filter
          (fun z : V =>
            (secondOrderDefectGraph G).connectedComponentMk z = e),
          (componentNeighborFinset G (secondOrderDefectGraph G) c z).card *
              (componentNeighborFinset G (secondOrderDefectGraph G)
                c' z).card =
            componentQuotientMatrix G (secondOrderDefectGraph G) e c *
              componentQuotientMatrix G (secondOrderDefectGraph G) e c' := by
        intro z hz
        have hze : z ∈ e.supp := by
          rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
          exact (Finset.mem_filter.mp hz).2
        rw [componentQuotientMatrix_apply_eq G (secondOrderDefectGraph G) 2
          hreg hcomm e c hze,
          componentQuotientMatrix_apply_eq G (secondOrderDefectGraph G) 2
            hreg hcomm e c' hze]
      rw [Finset.sum_congr rfl hval, Finset.sum_const, smul_eq_mul, hfiber,
        ← Set.ncard_eq_toFinset_card' e.supp]

/-- **Weighted Gram identity.**  For distinct components of the
second-order defect graph, the component-weighted sum of quotient entry
products toward the two components equals the product of their orders. -/
theorem sum_ncard_mul_componentQuotient_eq_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c c' : (secondOrderDefectGraph G).ConnectedComponent) (hne : c ≠ c') :
    (∑ e : (secondOrderDefectGraph G).ConnectedComponent,
        e.supp.ncard *
          (componentQuotientMatrix G (secondOrderDefectGraph G) e c *
            componentQuotientMatrix G (secondOrderDefectGraph G) e c')) =
      c.supp.ncard * c'.supp.ncard := by
  rw [← sum_componentNeighborCard_mul_eq_sum_ncard_mul
    G hfree hd heven hmin hcard c c']
  exact sum_componentNeighborCard_mul_of_ne G hfree c c' hne

end

end Erdos85
