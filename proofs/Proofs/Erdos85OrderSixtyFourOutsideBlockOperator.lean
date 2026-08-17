import Proofs.Erdos85OrderSixtyFourComponentComplexGram
import Proofs.Erdos85OrderSixtyFourSevenComponentLocal
import Proofs.Erdos85OrderSixtyFourRegularKernel

/-! # The first operator involving the outside 48-vertex block -/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- If the H-to-outside incidence matrix has row sum six and column sum two,
and the outside graph is six-regular, then the length-three return operator
`B C Bᴴ` has principal eigenvalue `72`.  These are exactly the block degrees
in the seven-component order-64 branch. -/
theorem outsideReturn_mulVec_one_eq_seventyTwo
    {H O : Type*} [Fintype H] [Fintype O] [DecidableEq H] [DecidableEq O]
    (B : Matrix H O ℂ) (C : Matrix O O ℂ)
    (hB : B.mulVec (fun _ ↦ 1) = (6 : ℂ) • (fun _ ↦ 1))
    (hBt : (Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (2 : ℂ) • (fun _ ↦ 1))
    (hC : C.mulVec (fun _ ↦ 1) = (6 : ℂ) • (fun _ ↦ 1)) :
    ((B * C) * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (72 : ℂ) • (fun _ ↦ 1) := by
  rw [← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec, hC, Matrix.mulVec_smul, hB]
  module

/-- The same computation, stated for arbitrary row, column, and middle
degrees. -/
theorem rectangularReturn_mulVec_one
    {H O : Type*} [Fintype H] [Fintype O] [DecidableEq H] [DecidableEq O]
    (B : Matrix H O ℂ) (C : Matrix O O ℂ) (r s t : ℂ)
    (hB : B.mulVec (fun _ ↦ 1) = r • (fun _ ↦ 1))
    (hBt : (Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      s • (fun _ ↦ 1))
    (hC : C.mulVec (fun _ ↦ 1) = t • (fun _ ↦ 1)) :
    ((B * C) * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (s * t * r) • (fun _ ↦ 1) := by
  rw [← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_smul,
    ← Matrix.mulVec_mulVec, hC, Matrix.mulVec_smul, hB]
  module

/-- The complement of the distinguished H16 block is six-regular in the
ambient graph: every outside vertex has total degree eight and exactly two
neighbors in H16. -/
theorem orderSixtyFour_seven_components_outside_induce_sixRegular
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      let q : Set (Fin 64) := {x | x ∉ c.supp}
      ∀ z : q, (G.induce q).degree z = 6 := by
  classical
  obtain ⟨c, hc16, htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  refine ⟨c, hc16, ?_⟩
  let q : Set (Fin 64) := {x | x ∉ c.supp}
  change ∀ z : q, (G.induce q).degree z = 6
  intro z
  let inside : Finset (Fin 64) :=
    (G.neighborFinset z.1).filter (fun x ↦ x ∈ c.supp)
  let outside : Finset (Fin 64) :=
    (G.neighborFinset z.1).filter (fun x ↦ x ∉ c.supp)
  have hins : inside.card = 2 := by
    have hc := htwo z.1
    change ((G.neighborFinset z.1).filter fun y ↦
      (secondOrderDefectGraph G).connectedComponentMk y = c).card = 2 at hc
    have heq : inside =
        (G.neighborFinset z.1).filter (fun y ↦
          (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp [inside, SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [heq, hc]
  have htotal : inside.card + outside.card = G.degree z.1 := by
    simpa [inside, outside, G.card_neighborFinset_eq_degree] using
      (Finset.card_filter_add_card_filter_not
        (s := G.neighborFinset z.1) (fun x ↦ x ∈ c.supp))
  have hout : outside.card = 6 := by
    rw [hins, hreg z.1] at htotal
    omega
  have hmap := G.map_neighborFinset_induce z
  have hmapCard := congrArg Finset.card hmap
  rw [Finset.card_map] at hmapCard
  have hdegree :
      (G.induce q).degree z = outside.card := by
    calc
      _ = ((G.induce q).neighborFinset z).card :=
        ((G.induce q).card_neighborFinset_eq_degree z).symm
      _ = (G.neighborFinset z.1 ∩
          q.toFinset).card := hmapCard
      _ = outside.card := by
        apply congrArg Finset.card
        ext y
        simp [outside, q]
  rw [hdegree, hout]

end

end Erdos85
