import Proofs.Erdos85GlobalLocalTriangleCount

/-! # Eighty triangles determine the order of the triangle-free color -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At the order-64 degree-eight boundary, if every triangle-free degree is
zero or two and the ambient graph has eighty triangles, then exactly sixteen
vertices have triangle-free degree two. -/
theorem orderSixtyFour_triangleFreeColorOrder_eq_sixteen_of_triangleCount_eighty
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hdegree : ∀ x, (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2)
    (htriangles : ((triangularEdgeGraph G).cliqueFinset 3).card = 80) :
    (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 16 := by
  let rooted : Fin 64 → ℕ := fun x =>
    (G.induce (G.neighborSet x)).edgeFinset.card
  let tf : Fin 64 → ℕ := fun x => (triangleFreeEdgeGraph G).degree x
  let C := (Finset.univ.filter fun x : Fin 64 => tf x = 2).card
  have hlocal (x : Fin 64) : tf x + 2 * rooted x = 8 := by
    have hx := card_triangleFreeNeighbors_add_two_mul_localEdges G hfree x
    have hcard : (triangleFreeNeighbors G x).card = tf x := by
      calc
        (triangleFreeNeighbors G x).card =
            ((triangleFreeEdgeGraph G).neighborFinset x).card := by
          rw [triangleFreeEdgeGraph_neighborFinset]
        _ = tf x := (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree x
    simpa [tf, rooted, hcard, hreg x] using hx
  have hrootedSum : (∑ x, rooted x) = 240 := by
    have hglobal := sum_localTriangleEdges_eq_three_mul_triangularCliques
      G hfree
    rw [htriangles] at hglobal
    simpa [rooted] using hglobal
  have htfSum : (∑ x, tf x) = 2 * C := by
    calc
      (∑ x, tf x) = ∑ x, if tf x = 2 then 2 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hdegree x with hx | hx <;> simp [tf, hx]
      _ = 2 * C := by
        simp only [C]
        rw [← Finset.sum_filter]
        simp
        omega
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
  rw [htfSum, hrootedSum] at htotal
  change C = 16
  omega

end

end Erdos85
