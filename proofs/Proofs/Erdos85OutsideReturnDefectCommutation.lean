import Proofs.Erdos85OutsideReturnEdgeSeparation
import Proofs.Erdos85DefectComponentBlockCommute

/-! # Defect commutation of the outside return operator -/

namespace Erdos85

noncomputable section

/-- Pure block algebra: an off-diagonal incidence block intertwining two
operators in both directions, and a commuting middle block, makes the
return operator commute with the left operator. -/
theorem rectangularReturn_comm_of_intertwine
    {H O : Type*} [Fintype H] [Fintype O] [DecidableEq H] [DecidableEq O]
    (B : Matrix H O ℂ) (E : Matrix O H ℂ)
    (C : Matrix O O ℂ) (DH : Matrix H H ℂ) (DO : Matrix O O ℂ)
    (hB : B * DO = DH * B) (hE : DO * E = E * DH)
    (hC : C * DO = DO * C) :
    DH * ((B * C) * E) = ((B * C) * E) * DH := by
  calc
    DH * ((B * C) * E) = ((DH * B) * C) * E := by
      simp only [Matrix.mul_assoc]
    _ = ((B * DO) * C) * E := by rw [hB]
    _ = (B * (DO * C)) * E := by simp only [Matrix.mul_assoc]
    _ = (B * (C * DO)) * E := by rw [hC]
    _ = ((B * C) * DO) * E := by simp only [Matrix.mul_assoc]
    _ = (B * C) * (DO * E) := by simp only [Matrix.mul_assoc]
    _ = (B * C) * (E * DH) := by rw [hE]
    _ = ((B * C) * E) * DH := by simp only [Matrix.mul_assoc]

/-- Extract all three required intertwining identities from a global
commutation when `D` has no edges across the cut. -/
theorem cut_blocks_intertwine_of_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (A D : Matrix V V ℂ) (p : V → Prop) [DecidablePred p]
    (hcomm : A * D = D * A)
    (hD12 : D.toBlock p (fun x ↦ ¬p x) = 0)
    (hD21 : D.toBlock (fun x ↦ ¬p x) p = 0) :
    let B := A.toBlock p (fun x ↦ ¬p x)
    let E := A.toBlock (fun x ↦ ¬p x) p
    let C := A.toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    let DH := D.toBlock p p
    let DO := D.toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    (B * DO = DH * B) ∧ (DO * E = E * DH) ∧ (C * DO = DO * C) := by
  classical
  have h12 := congrArg
    (fun M ↦ M.toBlock p (fun x ↦ ¬p x)) hcomm
  rw [Matrix.toBlock_mul_eq_add p p (fun x ↦ ¬p x) A D,
    Matrix.toBlock_mul_eq_add p p (fun x ↦ ¬p x) D A,
    hD12, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add] at h12
  have h21 := congrArg
    (fun M ↦ M.toBlock (fun x ↦ ¬p x) p) hcomm
  rw [Matrix.toBlock_mul_eq_add (fun x ↦ ¬p x) p p A D,
    Matrix.toBlock_mul_eq_add (fun x ↦ ¬p x) p p D A,
    hD21, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add] at h21
  have h22 := congrArg (fun M ↦
    M.toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)) hcomm
  rw [Matrix.toBlock_mul_eq_add (fun x ↦ ¬p x) p (fun x ↦ ¬p x) A D,
    Matrix.toBlock_mul_eq_add (fun x ↦ ¬p x) p (fun x ↦ ¬p x) D A] at h22
  simp only [hD12, hD21, Matrix.mul_zero, Matrix.zero_mul, zero_add] at h22
  exact ⟨h12, h21.symm, h22⟩

/-- Graph-facing form: for any connected component of `D`, the ambient
three-step return through its complement commutes with the induced `D`
block whenever the two global adjacency matrices commute. -/
theorem outsideReturn_comm_induce_component_of_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel D.Adj]
    (hcomm : G.adjMatrix ℂ * D.adjMatrix ℂ =
      D.adjMatrix ℂ * G.adjMatrix ℂ)
    (c : D.ConnectedComponent) :
    let p : V → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
    let C := (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
    let DH := (D.induce c.supp).adjMatrix ℂ
    DH * ((B * C) * Matrix.conjTranspose B) =
      ((B * C) * Matrix.conjTranspose B) * DH := by
  classical
  let p : V → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let E := (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) p
  let C := (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  let DH := (D.induce c.supp).adjMatrix ℂ
  let DO := (D.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
  have hD12 : (D.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x) = 0 := by
    ext i j
    simp only [Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply,
      Matrix.zero_apply]
    rw [if_neg]
    intro hij
    exact j.2 ((c.mem_supp_congr_adj hij).mp i.2)
  have hD21 : (D.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) p = 0 := by
    ext i j
    simp only [Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply,
      Matrix.zero_apply]
    rw [if_neg]
    intro hij
    exact i.2 ((c.mem_supp_congr_adj hij).mpr j.2)
  obtain ⟨hB, hE, hC⟩ := cut_blocks_intertwine_of_comm
    (G.adjMatrix ℂ) (D.adjMatrix ℂ) p hcomm hD12 hD21
  have hEeq : E = Matrix.conjTranspose B := by
    ext i j
    simp [E, B, Matrix.toBlock_apply, Matrix.conjTranspose_apply,
      SimpleGraph.adjMatrix_apply, G.adj_comm]
  have hDHeq : (D.adjMatrix ℂ).toBlock p p = DH := by
    ext i j
    simp [DH, p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  change DH * ((B * C) * Matrix.conjTranspose B) =
    ((B * C) * Matrix.conjTranspose B) * DH
  change B * (D.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x) =
    (D.adjMatrix ℂ).toBlock p p * B at hB
  change (D.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x) * E =
    E * (D.adjMatrix ℂ).toBlock p p at hE
  change (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x) *
      (D.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x) =
    (D.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x) *
      (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x) at hC
  change B * DO = (D.adjMatrix ℂ).toBlock p p * B at hB
  change DO * E = E * (D.adjMatrix ℂ).toBlock p p at hE
  change C * DO = DO * C at hC
  rw [hDHeq] at hB hE
  rw [hEeq] at hE
  exact rectangularReturn_comm_of_intertwine B (Matrix.conjTranspose B)
    C DH DO hB hE hC

/-- In the actual seven-component order-64 branch, the outside return
operator on H16 commutes with the induced defect adjacency. -/
theorem orderSixtyFour_seven_components_outsideReturn_comm_defect
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
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
      let C := (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x) (fun x ↦ ¬p x)
      let DH := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ
      DH * ((B * C) * Matrix.conjTranspose B) =
        ((B * C) * Matrix.conjTranspose B) * DH := by
  classical
  obtain ⟨c, hc16, _htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hcommZ := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have hcommC : G.adjMatrix ℂ * (secondOrderDefectGraph G).adjMatrix ℂ =
      (secondOrderDefectGraph G).adjMatrix ℂ * G.adjMatrix ℂ := by
    have h := congrArg (fun A ↦ A.map (Int.castRingHom ℂ)) hcommZ
    simpa only [Matrix.map_mul, adjMatrix_map_intCast] using h
  exact outsideReturn_comm_induce_component_of_comm
    G (secondOrderDefectGraph G) hcommC c

end

end Erdos85
