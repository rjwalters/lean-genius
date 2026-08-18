import Proofs.Erdos85GlobalLocalTriangleCount
import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85LocalTriangleParity

/-! # Eighty triangles determine the order of the triangle-free color -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Four order-sixteen defect components partition the sixty-four
vertices. -/
theorem orderSixtyFour_defectComponent_count_eq_four_of_allSixteen
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16) :
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent = 4 := by
  let D := secondOrderDefectGraph G
  have hsum := sum_connectedComponent_supp_ncard D
  have hsum' :
      (∑ c : D.ConnectedComponent, c.supp.ncard) = 64 := by
    simpa [Nat.card_eq_fintype_card] using hsum
  simp_rw [hsize] at hsum'
  have hmul : Fintype.card D.ConnectedComponent * 16 = 64 := by
    simpa [Finset.sum_const, Nat.nsmul_eq_mul] using hsum'
  have hcardD : Fintype.card D.ConnectedComponent = 4 := by omega
  simpa [D] using hcardD

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

/-- On an internal ambient edge of a size-sixteen defect component, the
triangle-free degree-two predicate propagates in both directions.  Thus the
colored support is a union of whole cycles of the internal ambient
two-factor. -/
theorem orderSixtyFour_allSixteen_triangleFree_degree_two_iff_of_internal_adj
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hsize : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : Fin 64} (hx : x ∈ c.supp) (hy : y ∈ c.supp)
    (hxy : G.Adj x y) :
    (triangleFreeEdgeGraph G).degree x = 2 ↔
      (triangleFreeEdgeGraph G).degree y = 2 := by
  let D := secondOrderDefectGraph G
  let T := triangleFreeEdgeGraph G
  have htarget (z : Fin 64) (hz : z ∈ c.supp) :
      (componentNeighborFinset G D c z).card = 2 := by
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg (by norm_num)
      c c (x := z) hz
    rw [hsize c] at hmul
    have hcard :
        (componentNeighborFinset G (secondOrderDefectGraph G) c z).card = 2 := by
      omega
    simpa [D] using hcard
  have hforward {u v : Fin 64} (hu : u ∈ c.supp) (hv : v ∈ c.supp)
      (huv : G.Adj u v) (hTu : T.degree u = 2) : T.degree v = 2 := by
    have hsub : T.neighborFinset u ⊆ componentNeighborFinset G D c u := by
      intro z hz
      have hTuz : T.Adj u z := (T.mem_neighborFinset u z).mp hz
      have hDuz : D.Adj u z := by
        change (antipodalGraph G ⊔ triangleFreeEdgeGraph G).Adj u z
        exact Or.inr hTuz
      rw [componentNeighborFinset, Finset.mem_filter]
      refine ⟨?_, ?_⟩
      · exact (G.mem_neighborFinset u z).mpr
          (((mem_triangleFreeNeighbors G u z).mp
            ((triangleFreeEdgeGraph_adj G u z).mp hTuz)).1)
      · rw [← ConnectedComponent.mem_supp_iff]
        exact (ConnectedComponent.mem_supp_congr_adj c hDuz).mp hu
    have hTeq : T.neighborFinset u = componentNeighborFinset G D c u := by
      apply Finset.eq_of_subset_of_card_le hsub
      rw [T.card_neighborFinset_eq_degree, hTu, htarget u hu]
    have hvTarget : v ∈ componentNeighborFinset G D c u := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset u v).mpr huv,
        (ConnectedComponent.mem_supp_iff c v).mp hv⟩
    have hTuv : T.Adj u v := by
      exact (T.mem_neighborFinset u v).mp (hTeq.symm ▸ hvTarget)
    have hpos : 0 < T.degree v := by
      rw [← T.card_neighborFinset_eq_degree]
      exact Finset.card_pos.mpr ⟨u,
        (T.mem_neighborFinset v u).mpr hTuv.symm⟩
    rcases orderSixtyFour_allSixteen_triangleFree_degree_zero_or_two
      G hfree hreg hsize v with hv0 | hv2
    · simp [T, hv0] at hpos
    · simpa [T] using hv2
  constructor
  · intro hTx
    exact hforward hx hy hxy (by simpa [T] using hTx)
  · intro hTy
    exact hforward hy hx hxy.symm (by simpa [T] using hTy)

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
