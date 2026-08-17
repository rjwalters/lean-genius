import Proofs.Erdos85OrderSixtyFourComponentComplexGram
import Proofs.Erdos85OrderSixtyFourSevenComponentLocal
import Proofs.Erdos85OrderSixtyFourRegularKernel
import Proofs.Erdos85OrderSixtyFourSixteenBlockGramTrace

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

/-- The actual H16--outside--outside--H return operator has principal
eigenvalue `72`.  This is the first exact spectral datum that sees the
outside 48-vertex adjacency block. -/
theorem orderSixtyFour_seven_components_outsideReturn_mulVec_one
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
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let q : Set (Fin 64) := {x | ¬p x}
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      (((B * C) * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
        (72 : ℂ) • (fun _ ↦ 1)) := by
  classical
  obtain ⟨c, hc16, htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let q : Set (Fin 64) := {x | ¬p x}
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
  let C := (G.induce q).adjMatrix ℂ
  have hBt : (Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (2 : ℂ) • (fun _ ↦ 1) := by
    ext z
    have hz := htwo z.1
    change ((G.neighborFinset z.1).filter fun y ↦
      (secondOrderDefectGraph G).connectedComponentMk y = c).card = 2 at hz
    let S : Finset c.supp :=
      Finset.univ.filter (fun x ↦ G.Adj x.1 z.1)
    let ι : c.supp ↪ Fin 64 :=
      .subtype (fun x : Fin 64 ↦ x ∈ c.supp)
    have heq : S.map ι =
        (G.neighborFinset z.1).filter (fun y ↦
          (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp [S, ι, SimpleGraph.ConnectedComponent.mem_supp_iff, G.adj_comm]
    have hScard : S.card = 2 := by
      rw [← Finset.card_map ι, heq, hz]
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, B,
      Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply, Complex.star_def,
      mul_one, Pi.smul_apply]
    calc
      (∑ x : c.supp,
          (starRingEnd ℂ) (if G.Adj x.1 z.1 then 1 else 0)) =
          ∑ x : c.supp, if G.Adj x.1 z.1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : G.Adj x.1 z.1 <;> simp [hx]
      _ = (S.card : ℂ) := by rw [Finset.sum_boole]
      _ = 2 := by rw [hScard]; norm_num
      _ = (2 : ℂ) • (1 : ℂ) := by
        rw [smul_eq_mul, mul_one]
  have hdeg : ∀ x : c.supp, (G.induce c.supp).degree x = 2 := by
    intro x
    have hx := htwo x.1
    change ((G.neighborFinset x.1).filter fun y ↦
      (secondOrderDefectGraph G).connectedComponentMk y = c).card = 2 at hx
    have hmap := G.map_neighborFinset_induce x
    have hmapCard := congrArg Finset.card hmap
    rw [Finset.card_map] at hmapCard
    rw [← (G.induce c.supp).card_neighborFinset_eq_degree, hmapCard]
    have heq : G.neighborFinset x.1 ∩ c.supp.toFinset =
        (G.neighborFinset x.1).filter (fun y ↦
          (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [heq, hx]
  have hQone := orderSixtyFour_sixteenBlock_exteriorGram_mulVec_one
    G hfree hmin hcover c hc16 hdeg
  change (B * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
      (12 : ℂ) • (fun _ ↦ 1) at hQone
  have hB : B.mulVec (fun _ ↦ 1) = (6 : ℂ) • (fun _ ↦ 1) := by
    ext x
    have hx := congrFun hQone x
    rw [← Matrix.mulVec_mulVec, hBt, Matrix.mulVec_smul] at hx
    simp only [Pi.smul_apply] at hx ⊢
    linear_combination hx / 2
  have hout := orderSixtyFour_seven_components_outside_induce_sixRegular
    G hfree hmin hcover hcount
  obtain ⟨c', hc'16, houtdeg⟩ := hout
  have hcc' : c = c' := by
    obtain ⟨d, hd16, hsmall⟩ :=
      orderSixtyFour_seven_defect_components_partition
        G hfree hmin hcover hcount
    have hcd : c = d := by
      by_contra hne
      exact (by have := hsmall c hne; omega)
    have hc'd : c' = d := by
      by_contra hne
      exact (by have := hsmall c' hne; omega)
    exact hcd.trans hc'd.symm
  subst c'
  have hC : C.mulVec (fun _ ↦ 1) = (6 : ℂ) • (fun _ ↦ 1) := by
    ext z
    have hd : (G.induce q).degree z = 6 := by
      convert houtdeg z using 1
    have hm := SimpleGraph.adjMatrix_mulVec_const_apply
      (G := G.induce q) (α := ℂ) (a := 1) (v := z)
    rw [mul_one, hd] at hm
    change ((G.induce q).adjMatrix ℂ).mulVec (fun _ ↦ 1) z = _
    convert hm using 1 <;> norm_num
  exact outsideReturn_mulVec_one_eq_seventyTwo B C hB hBt hC

end

end Erdos85
