import Proofs.Erdos85OrderSixtyFourPositiveHighExcluded
import Proofs.Erdos85ExcessDefectRegular
import Proofs.Erdos85BoundaryConnectedClean

/-! # The remaining regular kernel at order 64 -/

open SimpleGraph

namespace Erdos85

/-- Once positive high vertices are excluded, tight edge cover forces exact
8-regularity. -/
theorem orderSixtyFour_regular_of_tightCover
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    ∀ x : Fin 64, G.degree x = 8 := by
  have hempty := orderSixtyFour_highVertices_eq_empty_of_tightCover
    G hfree hmin
  apply orderSixtyFour_regular_of_no_high G hfree hmin hcover
  rw [hempty]
  simp

/-- Any C4-free minimum-degree-eight graph on 64 vertices is connected.
The elementary component Moore bound gives at least 58 vertices per
component, so two components cannot fit. -/
theorem orderSixtyFour_connected
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x) :
    Fintype.card G.ConnectedComponent = 1 := by
  classical
  have hminDegree : 8 ≤ G.minDegree :=
    G.le_minDegree_of_forall_le_degree 8 hmin
  have hcomponent (c : G.ConnectedComponent) : 58 ≤ c.supp.ncard := by
    have hc := connectedComponent_clean_moore_bound
      G hfree (d := 8) (by norm_num) hminDegree c
    norm_num at hc ⊢
    exact hc
  have hparts : (∑ c : G.ConnectedComponent, c.supp.ncard) = 64 := by
    calc
      (∑ c : G.ConnectedComponent, c.supp.ncard) =
          ∑ c : G.ConnectedComponent, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : G.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card (Fin 64) :=
        (Fintype.card_congr (vertexConnectedComponentEquiv G)).symm
      _ = 64 := by simp
  have hsubsingleton : Subsingleton G.ConnectedComponent := by
    constructor
    intro c e
    by_contra hce
    have hpair : c.supp.ncard + e.supp.ncard ≤
        ∑ a : G.ConnectedComponent, a.supp.ncard := by
      calc
        c.supp.ncard + e.supp.ncard =
            ∑ a ∈ ({c, e} : Finset G.ConnectedComponent),
              a.supp.ncard := by simp [hce]
        _ ≤ ∑ a ∈ (Finset.univ : Finset G.ConnectedComponent),
            a.supp.ncard := by
          exact Finset.sum_le_sum_of_subset_of_nonneg (by simp) (by simp)
        _ = ∑ a : G.ConnectedComponent, a.supp.ncard := by simp
    have hc := hcomponent c
    have he := hcomponent e
    omega
  letI : Unique G.ConnectedComponent := {
    default := G.connectedComponentMk 0
    uniq := fun _ => hsubsingleton.elim _ _ }
  exact Fintype.card_unique

/-- Exact regular-branch kernel: the ambient graph is connected, its
second-order defect graph is 7-regular, and the adjacency matrices satisfy
`A² = 7I + J - D`. -/
theorem orderSixtyFour_regular_defect_kernel
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    (∀ x : Fin 64, G.degree x = 8) ∧
      Fintype.card G.ConnectedComponent = 1 ∧
      (∀ x : Fin 64, (secondOrderDefectGraph G).degree x = 7) ∧
      G.adjMatrix ℤ * G.adjMatrix ℤ =
        (7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin 64) -
            (secondOrderDefectGraph G).adjMatrix ℤ := by
  have hreg := orderSixtyFour_regular_of_tightCover
    G hfree hmin hcover
  refine ⟨hreg, orderSixtyFour_connected G hfree hmin, ?_, ?_⟩
  · intro x
    have hdegree := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree (d := 8) (e := 5) hreg (by norm_num) x
    norm_num at hdegree ⊢
    exact hdegree
  · have hmatrix := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
      G hfree hreg
    norm_num at hmatrix ⊢
    exact hmatrix

end Erdos85
