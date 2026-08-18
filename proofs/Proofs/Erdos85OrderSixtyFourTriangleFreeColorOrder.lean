import Proofs.Erdos85GlobalLocalTriangleCount
import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85LocalTriangleParity

/-! # Eighty triangles determine the order of the triangle-free color -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If every defect component has order sixteen at the order-64 degree-eight
boundary, triangle-free degree is pointwise zero or two.  The valid input is
only that every triangle-free neighbor stays in the vertex's defect
component; the reverse inclusion need not hold. -/
theorem orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (x : Fin 64) :
    (triangleFreeEdgeGraph G).degree x = 0 ∨
      (triangleFreeEdgeGraph G).degree x = 2 := by
  let D := secondOrderDefectGraph G
  let T := triangleFreeEdgeGraph G
  let c := D.connectedComponentMk x
  have hind : (G.induce c.supp).degree ⟨x, by rfl⟩ = 2 := by
    apply binarySquare_regular_degree_induce_defectComponent_eq_part
      G hfree (q := 8) (m := 2) (by norm_num) hreg (by norm_num) c
    simpa [D, c] using hsize c
  have hsubset : T.neighborFinset x ⊆
      ((G.induce c.supp).neighborFinset ⟨x, by rfl⟩).image
        (fun y : c.supp => y.1) := by
    intro y hy
    have hTxy : T.Adj x y := (T.mem_neighborFinset x y).mp hy
    have hDxy : D.Adj x y := by
      change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj x y
      exact Or.inr hTxy
    have hyc : y ∈ c.supp := by
      rw [ConnectedComponent.mem_supp_iff]
      exact (ConnectedComponent.connectedComponentMk_eq_of_adj hDxy).symm
    rw [Finset.mem_image]
    refine ⟨⟨y, hyc⟩, ?_, rfl⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hTxy)).1
  have hle : T.degree x ≤ 2 := by
    rw [← T.card_neighborFinset_eq_degree]
    calc
      (T.neighborFinset x).card ≤
          (((G.induce c.supp).neighborFinset ⟨x, by rfl⟩).image
            (fun y : c.supp => y.1)).card :=
        Finset.card_le_card hsubset
      _ = ((G.induce c.supp).neighborFinset ⟨x, by rfl⟩).card := by
        rw [Finset.card_image_of_injective _ Subtype.val_injective]
      _ = 2 := by
        rw [(G.induce c.supp).card_neighborFinset_eq_degree, hind]
  have heven : T.degree x % 2 = 0 := by
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    simpa [hreg x] using
      triangleFreeNeighbors_card_mod_two_eq_vertexDegree G hfree x
  have hle' : (triangleFreeEdgeGraph G).degree x ≤ 2 := by simpa [T] using hle
  have heven' : (triangleFreeEdgeGraph G).degree x % 2 = 0 := by
    simpa [T] using heven
  omega

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

/-- Graph-facing all-size-sixteen specialization of the exact colored-order
terminal. -/
theorem orderSixtyFour_allSixteen_triangleFreeColorOrder_eq_sixteen_of_triangleCount_eighty
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (htriangles : ((triangularEdgeGraph G).cliqueFinset 3).card = 80) :
    (Finset.univ.filter fun x : Fin 64 =>
      (triangleFreeEdgeGraph G).degree x = 2).card = 16 := by
  apply orderSixtyFour_triangleFreeColorOrder_eq_sixteen_of_triangleCount_eighty
    G hfree hreg (fun x => ?_) htriangles
  exact orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two
    G hfree hreg hsize x

end

end Erdos85
