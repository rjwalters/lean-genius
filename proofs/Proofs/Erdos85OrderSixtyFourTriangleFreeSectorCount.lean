import Proofs.Erdos85GlobalLocalTriangleCount
import Proofs.Erdos85MinimumSectorAssemblyInterface

/-! # The eighty-triangle terminal selects one triangle-free sector -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the order-64 all-size-sixteen branch, suppose triangle-free degree is
constant on each defect component and is either zero or two, encoded as
`2 * ε c`.  If the ambient graph has eighty triangles, exactly one component
has triangle-free degree two. -/
theorem orderSixtyFour_sum_triangleFreeSectorIndicator_eq_one
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (ε : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hconst : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ x : Fin 64, x ∈ c.supp →
        (triangleFreeEdgeGraph G).degree x = 2 * ε c)
    (htriangles : ((triangularEdgeGraph G).cliqueFinset 3).card = 80) :
    ∑ c, ε c = 1 := by
  let D := secondOrderDefectGraph G
  let rooted : Fin 64 → ℕ := fun x =>
    (G.induce (G.neighborSet x)).edgeFinset.card
  let tf : Fin 64 → ℕ := fun x => (triangleFreeEdgeGraph G).degree x
  have hlocal (x : Fin 64) : tf x + 2 * rooted x = 8 := by
    have hx := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
    have hcard : (triangleFreeNeighbors G x).card = tf x := by
      calc
        (triangleFreeNeighbors G x).card =
            ((triangleFreeEdgeGraph G).neighborFinset x).card := by
          rw [triangleFreeEdgeGraph_neighborFinset]
        _ = tf x := (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree x
    simpa [tf, rooted, hcard, hreg x] using hx
  have hlocalSum : (∑ x, rooted x) = 240 := by
    have hglobal := sum_localTriangleEdges_eq_three_mul_triangularCliques
      G hfree
    rw [htriangles] at hglobal
    simpa [rooted] using hglobal
  have htotal : (∑ x, tf x) + 2 * (∑ x, rooted x) = 512 := by
    calc
      (∑ x, tf x) + 2 * (∑ x, rooted x) =
          ∑ x, (tf x + 2 * rooted x) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = ∑ _x : Fin 64, 8 := by
        apply Finset.sum_congr rfl
        intro x _
        exact hlocal x
      _ = 512 := by norm_num
  have htfSum : (∑ x, tf x) = 32 * ∑ c, ε c := by
    calc
      (∑ x, tf x) =
          ∑ c : D.ConnectedComponent, c.supp.ncard * (2 * ε c) := by
        apply sum_vertex_eq_sum_component_ncard_mul D tf (fun c => 2 * ε c)
        intro c x hx
        exact hconst c x hx
      _ = ∑ c : D.ConnectedComponent, 32 * ε c := by
        apply Finset.sum_congr rfl
        intro c _
        rw [hsize c]
        omega
      _ = 32 * ∑ c : D.ConnectedComponent, ε c := by
        rw [Finset.mul_sum]
  rw [hlocalSum, htfSum] at htotal
  omega

end

end Erdos85
