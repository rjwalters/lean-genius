import Proofs.Erdos85OutsideReturnCapacity

/-! # The outside return operator is determined by the exterior Gram matrix -/

namespace Erdos85

noncomputable section

/-- The off-diagonal block equation `H B + B C = J`, followed by a return
through `E`, determines `B C E` from the Gram matrix `B E`. -/
theorem rectangularOutsideReturn_eq_smul_sub_internal_mul_gram
    {H O : Type*} [Fintype H] [Fintype O] [DecidableEq H] [DecidableEq O]
    {K : Type*} [CommRing K]
    (A : Matrix H H K) (B : Matrix H O K) (C : Matrix O O K)
    (E : Matrix O H K) (JHO : Matrix H O K) (JHH : Matrix H H K)
    (r : K)
    (hcross : A * B + B * C = JHO)
  (hreturn : JHO * E = r • JHH) :
    (B * C) * E = r • JHH - A * (B * E) := by
  have hBC : B * C = JHO - A * B :=
    eq_sub_of_add_eq' hcross
  rw [hBC, Matrix.sub_mul, hreturn]
  rw [Matrix.mul_assoc]

/-- Pointwise form of the return/Gram identity.  Once a return entry is the
natural number `n`, it turns into an exact entry equation for `A Q`. -/
theorem internal_mul_gram_apply_eq_of_outsideReturn_identity
    {H : Type*} [Fintype H] [DecidableEq H]
    (A Q M : Matrix H H ℂ) (r : ℕ)
    (hidentity : M = (r : ℂ) •
      (FriendshipTheoremOQ01.onesMatrix H).map (Int.castRingHom ℂ) - A * Q)
    (u v : H) {n : ℕ} (hentry : M u v = n) :
    (A * Q) u v = (r : ℂ) - (n : ℂ) := by
  have huv := congr_fun₂ hidentity u v
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    FriendshipTheoremOQ01.onesMatrix, Matrix.map_apply, Matrix.of_apply] at huv
  rw [hentry] at huv
  rw [map_one, mul_one] at huv
  linear_combination huv

/-- Combining the return capacity bound with `M = 6J - A Q` forces every
entry of `A Q` to be an integer in `[0,6]`. -/
theorem internal_mul_gram_apply_eq_nat_le_six_of_outsideReturn
    {H : Type*} [Fintype H] [DecidableEq H]
    (A Q M : Matrix H H ℂ)
    (hidentity : M = (6 : ℂ) •
      (FriendshipTheoremOQ01.onesMatrix H).map (Int.castRingHom ℂ) - A * Q)
    (hcapacity : ∀ u v, ∃ n : ℕ, n ≤ 6 ∧ M u v = n)
    (u v : H) :
    ∃ k : ℕ, k ≤ 6 ∧ (A * Q) u v = k := by
  obtain ⟨n, hn, hentry⟩ := hcapacity u v
  refine ⟨6 - n, Nat.sub_le _ _, ?_⟩
  have h := internal_mul_gram_apply_eq_of_outsideReturn_identity
    A Q M 6 hidentity u v hentry
  rw [h, Nat.cast_sub hn]

/-- In the seven-component order-64 branch, the concrete outside-return
operator is exactly `6J - H Q`, where `H` is internal adjacency and `Q` is
the exterior Gram matrix. -/
theorem orderSixtyFour_seven_components_outsideReturn_eq_sixJ_sub_HQ
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
      let H := (G.induce c.supp).adjMatrix ℂ
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      let Q := B * Matrix.conjTranspose B
      let M := (B * C) * Matrix.conjTranspose B
      H * B + B * C = (fun _ _ ↦ (1 : ℂ)) ∧
        M = (6 : ℂ) •
            (FriendshipTheoremOQ01.onesMatrix c.supp).map
              (Int.castRingHom ℂ) - H * Q := by
  classical
  obtain ⟨c, hc16, htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  let D := secondOrderDefectGraph G
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let q : Set (Fin 64) := {x | ¬p x}
  let H := (G.induce c.supp).adjMatrix ℂ
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let E := Matrix.conjTranspose B
  let C := (G.induce {x | ¬p x}).adjMatrix ℂ
  let JHO : Matrix {x // p x} {x // ¬p x} ℤ := fun _ _ ↦ 1
  let JHH := (FriendshipTheoremOQ01.onesMatrix c.supp).map
    (Int.castRingHom ℂ)
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hsqZ := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    G hfree hreg
  have hsqC : G.adjMatrix ℂ * G.adjMatrix ℂ =
      (7 : ℂ) • (1 : Matrix (Fin 64) (Fin 64) ℂ) +
        (FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
          (Int.castRingHom ℂ) - D.adjMatrix ℂ := by
    have h := congrArg (fun M ↦ M.map (Int.castRingHom ℂ)) hsqZ
    calc
      _ = (G.adjMatrix ℤ * G.adjMatrix ℤ).map
          (Int.castRingHom ℂ) := by
        rw [Matrix.map_mul, adjMatrix_map_intCast]
      _ = ((7 : ℤ) • (1 : Matrix (Fin 64) (Fin 64) ℤ) +
          FriendshipTheoremOQ01.onesMatrix (Fin 64) -
            D.adjMatrix ℤ).map (Int.castRingHom ℂ) := h
      _ = _ := by
        ext i j
        by_cases hij : i = j <;>
          simp [SimpleGraph.adjMatrix_apply, Matrix.ofNat_apply, hij]
  have hblock := congrArg
    (fun X ↦ X.toBlock p (fun x ↦ ¬p x)) hsqC
  rw [Matrix.toBlock_mul_eq_add p p (fun x ↦ ¬p x)] at hblock
  have hA11 : (G.adjMatrix ℂ).toBlock p p = H := by
    ext i j
    simp [H, p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hA12 : (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x) = B := rfl
  have hA22 : (G.adjMatrix ℂ).toBlock (fun x ↦ ¬p x)
      (fun x ↦ ¬p x) = C := rfl
  have hright : ((7 : ℂ) • (1 : Matrix (Fin 64) (Fin 64) ℂ) +
        (FriendshipTheoremOQ01.onesMatrix (Fin 64)).map
          (Int.castRingHom ℂ) - D.adjMatrix ℂ).toBlock
          p (fun x ↦ ¬p x) = JHO.map (Int.castRingHom ℂ) := by
    ext i j
    have hij : i.1 ≠ j.1 := fun h ↦ j.2 (h ▸ i.2)
    have hD : ¬D.Adj i.1 j.1 := by
      intro hadj
      exact j.2 ((c.mem_supp_congr_adj hadj).mp i.2)
    simp [p, JHO, Matrix.toBlock_apply,
      FriendshipTheoremOQ01.onesMatrix, SimpleGraph.adjMatrix_apply,
      hij, hD]
  rw [hA11, hA12, hA22, hright] at hblock
  have hout : ∀ u : c.supp,
      ((G.neighborFinset u.1).filter fun x ↦ x ∉ c.supp).card = 6 := by
    intro u
    have hu := htwo u.1
    change ((G.neighborFinset u.1).filter fun y ↦
      D.connectedComponentMk y = c).card = 2 at hu
    have hins : ((G.neighborFinset u.1).filter fun x ↦
        x ∈ c.supp).card = 2 := by
      have heq : (G.neighborFinset u.1).filter (fun x ↦ x ∈ c.supp) =
          (G.neighborFinset u.1).filter fun y ↦
            D.connectedComponentMk y = c := by
        ext y
        simp [D, SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [heq, hu]
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset u.1) (fun x ↦ x ∈ c.supp)
    rw [hins, G.card_neighborFinset_eq_degree, hreg u.1] at hsplit
    omega
  have hreturn : JHO.map (Int.castRingHom ℂ) * E = (6 : ℂ) • JHH := by
    ext i j
    let S : Finset {x // ¬p x} :=
      Finset.univ.filter fun x ↦ G.Adj x.1 j.1
    let ι : {x // ¬p x} ↪ Fin 64 :=
      ⟨Subtype.val, Subtype.val_injective⟩
    have hmap : S.map ι =
        (G.neighborFinset j.1).filter fun x ↦ x ∉ c.supp := by
      ext x
      simp [S, ι, p, G.adj_comm,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    have hScard : S.card = 6 := by
      rw [← Finset.card_map ι, hmap, hout j]
    simp only [Matrix.mul_apply, JHO, JHH, E, B,
      FriendshipTheoremOQ01.onesMatrix, Matrix.map_apply, Matrix.of_apply,
      Matrix.conjTranspose_apply,
      Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply, Complex.star_def,
      Matrix.smul_apply, smul_eq_mul]
    calc
      (∑ x : {x // ¬p x}, (Int.castRingHom ℂ) 1 *
          (starRingEnd ℂ) (if G.Adj j.1 x.1 then 1 else 0)) =
          ∑ x : q, if G.Adj x.1 j.1 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : G.Adj x.1 j.1
        · have hx' : G.Adj j.1 x.1 := (G.adj_comm _ _).mp hx
          simp [hx, hx']
        · have hx' : ¬G.Adj j.1 x.1 :=
            fun h ↦ hx ((G.adj_comm _ _).mp h)
          simp [hx, hx']
      _ = (S.card : ℂ) := by
        rw [Finset.sum_boole]
        rfl
      _ = 6 := by rw [hScard]; norm_num
      _ = (6 : ℂ) * (Int.castRingHom ℂ) 1 := by norm_num
  refine ⟨?_, rectangularOutsideReturn_eq_smul_sub_internal_mul_gram
    H B C E (JHO.map (Int.castRingHom ℂ)) JHH 6 hblock hreturn⟩
  exact hblock.trans (by
    ext i j
    norm_num [JHO])

/-- Combined graph-facing ledger: on the unique H16 block, `M = 6J - HQ`,
and both `M` and `HQ` have natural entries between zero and six. -/
theorem orderSixtyFour_seven_components_outsideReturn_gram_entry_ledger
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
      let H := (G.induce c.supp).adjMatrix ℂ
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      let Q := B * Matrix.conjTranspose B
      let M := (B * C) * Matrix.conjTranspose B
      M = (6 : ℂ) •
          (FriendshipTheoremOQ01.onesMatrix c.supp).map
            (Int.castRingHom ℂ) - H * Q ∧
      ∀ u v : c.supp,
        (∃ n : ℕ, n ≤ 6 ∧ M u v = n) ∧
        (∃ k : ℕ, k ≤ 6 ∧ (H * Q) u v = k) := by
  classical
  obtain ⟨c, hc16, _hcross, hid⟩ :=
    orderSixtyFour_seven_components_outsideReturn_eq_sixJ_sub_HQ
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, hcap⟩ :=
    orderSixtyFour_seven_components_outsideReturn_apply_eq_nat_le_six
      G hfree hmin hcover hcount
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
  refine ⟨c, hc16, hid, ?_⟩
  intro u v
  refine ⟨hcap u v, ?_⟩
  exact internal_mul_gram_apply_eq_nat_le_six_of_outsideReturn
    _ _ _ hid hcap u v

end

end Erdos85
