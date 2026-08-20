import Proofs.Erdos85OrderSixtyFourOutsideFeasibility
import Proofs.Erdos85DefectComponentCrossBlockEquation
import Proofs.Erdos85BinarySquareRegularParity

/-!
# The regular outside feasibility package

Editor repair item (1) of squad msg 13926: the seven-component outside
feasibility wrapper is vacuous under regularity (`2·#components ≤ q`
forces at most four components at `q = 8`).  This replacement derives
the identical finite outside package for ANY size-16 defect component of
a regular order-64 candidate, with no component-count hypothesis:
the uniform equitable law gives every vertex exactly two component
neighbours, C4-freeness gives owner injectivity and the six-regular
exterior-pair graph, degree arithmetic gives the six-regular outside
block, and the banked regular cross-block identity gives
`H·B + B·C = J` (cast from `ℤ` to `ℂ`).
-/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 1600000 in
theorem orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x : Fin 64, G.degree x = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc16 : c.supp.ncard = 16) :
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    let q : Set (Fin 64) := {x | ¬p x}
    let H := (G.induce c.supp).adjMatrix ℂ
    let R := exteriorPairGraph G c.supp
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
    let Cg := G.induce q
    let C := Cg.adjMatrix ℂ
    ∃ _outsideLabel : q ≃ Fin 48,
    Fintype.card q = 48 ∧
    (∀ x : Fin 64,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2) ∧
    Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c) ∧
    ((Finset.univ.filter (fun x : Fin 64 ↦ x ∉ c.supp)).image
      (componentNeighborFinset G (secondOrderDefectGraph G) c)).card = 48 ∧
    (∀ u : c.supp, R.degree u = 6) ∧
    R.edgeFinset.card = 48 ∧
    (∀ z : q, Cg.degree z = 6) ∧
    (¬containsC4 q Cg) ∧
    H * B + B * C = (fun _ _ ↦ (1 : ℂ)) := by
  classical
  have hmin : ∀ x : Fin 64, 8 ≤ G.degree x := fun x ↦ (hreg x).ge
  have hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8 :=
    fun {u v} _ ↦ Or.inl (hreg u)
  have hcardV : Fintype.card (Fin 64) = 8 * 8 := by simp
  -- The uniform equitable law: every vertex has two component neighbours.
  have htwoAll : ∀ x : Fin 64,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2 := by
    intro x
    have hx : x ∈ ((secondOrderDefectGraph G).connectedComponentMk x).supp :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff _ x).mpr rfl
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (by omega) hreg hcardV
      ((secondOrderDefectGraph G).connectedComponentMk x) c hx
    rw [hc16] at h
    omega
  -- The internal two-regularity in induced-degree form.
  have htwoInd : ∀ x : c.supp, (G.induce c.supp).degree x = 2 := by
    intro x
    have hmap := G.map_neighborFinset_induce x
    have hmapCard := congrArg Finset.card hmap
    rw [Finset.card_map] at hmapCard
    have hdeg : (G.induce c.supp).degree x =
        (G.neighborFinset x.1 ∩ c.supp.toFinset).card := by
      calc
        _ = ((G.induce c.supp).neighborFinset x).card :=
          ((G.induce c.supp).card_neighborFinset_eq_degree x).symm
        _ = _ := hmapCard
    have hfilter : G.neighborFinset x.1 ∩ c.supp.toFinset =
        componentNeighborFinset G (secondOrderDefectGraph G) c x.1 := by
      ext y
      simp [componentNeighborFinset,
        SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hdeg, hfilter, htwoAll]
  -- Outside cardinality and label.
  have hqcard : Fintype.card {x : Fin 64 // x ∉ c.supp} = 48 := by
    calc
      Fintype.card {x : Fin 64 // x ∉ c.supp} = c.suppᶜ.ncard := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.card_coe_set_eq c.suppᶜ
      _ = Nat.card (Fin 64) - c.supp.ncard := Set.ncard_compl c.supp
      _ = 48 := by simp [hc16]
  have houtsideLabel : {x : Fin 64 // x ∉ c.supp} ≃ Fin 48 :=
    Fintype.equivOfCardEq (by simpa using hqcard)
  -- Owner injectivity.
  have hinj : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c) := by
    intro y z heq
    by_contra hyz
    let Sy := componentNeighborFinset G (secondOrderDefectGraph G) c y
    have hSycard : Sy.card = 2 := htwoAll y
    have hsub : Sy ⊆ G.neighborFinset y ∩ G.neighborFinset z := by
      intro w hw
      have hwy : G.Adj y w :=
        (G.mem_neighborFinset y w).mp ((Finset.mem_filter.mp hw).1)
      have hwzS : w ∈
          componentNeighborFinset G (secondOrderDefectGraph G) c z := by
        rw [← heq]
        exact hw
      have hwz : G.Adj z w :=
        (G.mem_neighborFinset z w).mp ((Finset.mem_filter.mp hwzS).1)
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y w).mpr hwy,
          (G.mem_neighborFinset z w).mpr hwz⟩
    have hle := Finset.card_le_card hsub
    have hone := common_le_one_of_not_containsC4 hfree y z hyz
    omega
  -- Pair-image cardinality.
  have hpairImage :
      ((Finset.univ.filter (fun x : Fin 64 ↦ x ∉ c.supp)).image
        (componentNeighborFinset G (secondOrderDefectGraph G) c)).card
          = 48 := by
    rw [Finset.card_image_of_injective _ hinj]
    have hfilter :
        (Finset.univ.filter (fun x : Fin 64 ↦ x ∉ c.supp)) =
          Finset.univ \ c.supp.toFinset := by
      ext x
      simp
    rw [hfilter, Finset.card_sdiff, Finset.inter_univ,
      Finset.card_univ, Fintype.card_fin,
      ← Set.ncard_eq_toFinset_card', hc16]
  -- The exterior Gram identity and R-regularity (seven-component-free
  -- replay of the exteriorGram core).
  have hRreg : ∀ x : c.supp, (exteriorPairGraph G c.supp).degree x = 6 := by
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
    let A := (G.induce c.supp).adjMatrix ℂ
    let D := ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℂ
    have hid :=
      orderSixtyFour_defectComponent_internal_sq_add_exteriorGram_complex
        G hfree hmin hcover c
    change A * A + B * Matrix.conjTranspose B =
        (7 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
          (FriendshipTheoremOQ01.onesMatrix c.supp).map
            (Int.castRingHom ℂ) - D at hid
    have hdiag : ∀ u : c.supp,
        (Finset.univ.filter fun z : {z // z ∉ c.supp} ↦
          G.Adj u.1 z.1 ∧ G.Adj u.1 z.1).card = 6 := by
      intro u
      have hAii : (A * A) u u = 2 := by
        dsimp [A]
        rw [(G.induce c.supp).adjMatrix_mul_self_apply_self]
        exact_mod_cast htwoInd u
      have he := congrArg (fun M ↦ M u u) hid
      have hDii : D u u = 0 := by
        simp [D, SimpleGraph.adjMatrix_apply]
      have hQii : (B * Matrix.conjTranspose B) u u = 6 := by
        simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
          Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix,
          SimpleGraph.adjMatrix_apply, hAii, hDii] at he
        linear_combination he
      have hc := exteriorGram_apply_eq_card G c.supp u u
      change (B * Matrix.conjTranspose B) u u = _ at hc
      rw [hQii] at hc
      exact_mod_cast hc.symm
    have hle : ∀ u v : c.supp, u ≠ v →
        (Finset.univ.filter fun z : {z // z ∉ c.supp} ↦
          G.Adj u.1 z.1 ∧ G.Adj v.1 z.1).card ≤ 1 := by
      intro u v huv
      exact exterior_common_card_le_one_of_noC4 G c.supp hfree u v huv
    have hQ := exteriorGram_eq_six_add_pairGraph G c.supp hdiag hle
    change B * Matrix.conjTranspose B =
        (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
          (exteriorPairGraph G c.supp).adjMatrix ℂ at hQ
    have hQone := orderSixtyFour_sixteenBlock_exteriorGram_mulVec_one
      G hfree hmin hcover c hc16 htwoInd
    change (B * Matrix.conjTranspose B).mulVec (fun _ ↦ 1) =
        (12 : ℂ) • (fun _ ↦ 1) at hQone
    intro x
    have he := congrArg (fun M ↦ M.mulVec (fun _ ↦ (1 : ℂ)) x) hQ
    have hx := congrFun hQone x
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] at he
    have hRadj : ((exteriorPairGraph G c.supp).adjMatrix ℂ).mulVec
        (fun _ ↦ 1) x =
        ((exteriorPairGraph G c.supp).degree x : ℂ) := by
      simpa using
        (SimpleGraph.adjMatrix_mulVec_const_apply
          (G := exteriorPairGraph G c.supp) (α := ℂ) (a := 1) (v := x))
    simp only [Pi.add_apply, Pi.smul_apply] at he hx
    rw [hRadj] at he
    simp at he
    norm_num at hx
    rw [hx] at he
    have hre := congrArg Complex.re he
    norm_num at hre
    have hnEq : 12 = 6 + (exteriorPairGraph G c.supp).degree x := by
      exact_mod_cast hre
    omega
  -- R edge count from six-regularity.
  have hRedges : (exteriorPairGraph G c.supp).edgeFinset.card = 48 := by
    have hs := (exteriorPairGraph G c.supp).sum_degrees_eq_twice_card_edges
    simp_rw [hRreg] at hs
    have hcS : Fintype.card c.supp = 16 := by
      simpa [Nat.card_eq_fintype_card] using
        (Nat.card_coe_set_eq c.supp).trans hc16
    simp [hcS] at hs
    omega
  -- The outside block is six-regular.
  have hout : ∀ z : {x : Fin 64 // x ∉ c.supp},
      (G.induce {x | x ∉ c.supp}).degree z = 6 := by
    intro z
    let inside : Finset (Fin 64) :=
      (G.neighborFinset z.1).filter (fun x ↦ x ∈ c.supp)
    let outside : Finset (Fin 64) :=
      (G.neighborFinset z.1).filter (fun x ↦ x ∉ c.supp)
    have hins : inside.card = 2 := by
      have hcz := htwoAll z.1
      change ((G.neighborFinset z.1).filter fun y ↦
        (secondOrderDefectGraph G).connectedComponentMk y = c).card = 2 at hcz
      have heq : inside =
          (G.neighborFinset z.1).filter (fun y ↦
            (secondOrderDefectGraph G).connectedComponentMk y = c) := by
        ext y
        simp [inside, SimpleGraph.ConnectedComponent.mem_supp_iff]
      rw [heq, hcz]
    have htotal : inside.card + outside.card = G.degree z.1 := by
      simpa [inside, outside, G.card_neighborFinset_eq_degree] using
        (Finset.card_filter_add_card_filter_not
          (s := G.neighborFinset z.1) (fun x ↦ x ∈ c.supp))
    have houtc : outside.card = 6 := by
      rw [hins, hreg z.1] at htotal
      omega
    have hmap := G.map_neighborFinset_induce
      (s := ({x : Fin 64 | x ∉ c.supp} : Set (Fin 64))) z
    have hmapCard := congrArg Finset.card hmap
    rw [Finset.card_map] at hmapCard
    have hdegree :
        (G.induce {x | x ∉ c.supp}).degree z = outside.card := by
      calc
        _ = ((G.induce {x | x ∉ c.supp}).neighborFinset z).card :=
          ((G.induce {x | x ∉ c.supp}).card_neighborFinset_eq_degree z).symm
        _ = (G.neighborFinset z.1 ∩
            ({x : Fin 64 | x ∉ c.supp}).toFinset).card := hmapCard
        _ = outside.card := by
          apply congrArg Finset.card
          ext y
          simp [outside]
    rw [hdegree, houtc]
  -- The cross-block equation, cast from the regular integer identity.
  have hcross :
      (G.induce c.supp).adjMatrix ℂ *
          (G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ x ∈ ({x | x ∉ c.supp} : Set (Fin 64))) +
        (G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ x ∈ ({x | x ∉ c.supp} : Set (Fin 64))) *
          (G.induce {x | x ∉ c.supp}).adjMatrix ℂ =
        (fun _ _ ↦ (1 : ℂ)) := by
    have hZ := binarySquare_regular_defectComponent_crossBlock_eq_ones
      G hfree hreg c
    dsimp only at hZ
    funext u w
    have hZuw := congrFun (congrFun hZ u) w
    simp only [Matrix.add_apply, Matrix.mul_apply] at hZuw ⊢
    have hcast1 : ∀ y : c.supp,
        (G.induce c.supp).adjMatrix ℂ u y *
          (G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ x ∈ ({x | x ∉ c.supp} : Set (Fin 64))) y w =
        (((G.induce c.supp).adjMatrix ℤ u y *
          (G.adjMatrix ℤ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ ¬x ∈ c.supp) y w : ℤ) : ℂ) := by
      intro y
      simp only [SimpleGraph.adjMatrix_apply, Matrix.toBlock_apply]
      by_cases h1 : (G.induce c.supp).Adj u y <;>
        by_cases h2 : G.Adj y.1 w.1
      · rw [if_pos h1, if_pos h1, if_pos h2, if_pos h2]
        norm_num
      · rw [if_pos h1, if_pos h1, if_neg h2, if_neg h2]
        norm_num
      · rw [if_neg h1, if_neg h1]
        norm_num
      · rw [if_neg h1, if_neg h1]
        norm_num
    have hcast2 : ∀ z : {x : Fin 64 // x ∉ c.supp},
        (G.adjMatrix ℂ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ x ∈ ({x | x ∉ c.supp} : Set (Fin 64))) u z *
          (G.induce {x | x ∉ c.supp}).adjMatrix ℂ z w =
        (((G.adjMatrix ℤ).toBlock (fun x ↦ x ∈ c.supp)
            (fun x ↦ ¬x ∈ c.supp) u z *
          (G.adjMatrix ℤ).toBlock (fun x ↦ ¬x ∈ c.supp)
            (fun x ↦ ¬x ∈ c.supp) z w : ℤ) : ℂ) := by
      intro z
      simp only [SimpleGraph.adjMatrix_apply, Matrix.toBlock_apply]
      by_cases h1 : G.Adj u.1 z.1 <;>
        by_cases h2 : G.Adj z.1 w.1
      · rw [if_pos h1, if_pos h1,
          if_pos (show (G.induce {x | x ∉ c.supp}).Adj z w from h2),
          if_pos h2]
        norm_num
      · rw [if_pos h1, if_pos h1,
          if_neg (show ¬(G.induce {x | x ∉ c.supp}).Adj z w from h2),
          if_neg h2]
        norm_num
      · rw [if_neg h1, if_neg h1]
        norm_num
      · rw [if_neg h1, if_neg h1]
        norm_num
    calc
      (∑ y, (G.induce c.supp).adjMatrix ℂ u y *
            (G.adjMatrix ℂ).toBlock _ _ y w) +
          ∑ z, (G.adjMatrix ℂ).toBlock _ _ u z *
            (G.induce {x | x ∉ c.supp}).adjMatrix ℂ z w
        = (((∑ y, (G.induce c.supp).adjMatrix ℤ u y *
            (G.adjMatrix ℤ).toBlock (fun x ↦ x ∈ c.supp)
              (fun x ↦ ¬x ∈ c.supp) y w) +
          ∑ z, (G.adjMatrix ℤ).toBlock (fun x ↦ x ∈ c.supp)
              (fun x ↦ ¬x ∈ c.supp) u z *
            (G.adjMatrix ℤ).toBlock (fun x ↦ ¬x ∈ c.supp)
              (fun x ↦ ¬x ∈ c.supp) z w : ℤ) : ℂ) := by
          push_cast
          congr 1
          · refine Finset.sum_congr rfl fun y _ ↦ ?_
            rw [hcast1 y]
            push_cast
            ring
          · refine Finset.sum_congr rfl fun z _ ↦ ?_
            rw [hcast2 z]
            push_cast
            ring
      _ = ((1 : ℤ) : ℂ) := by exact_mod_cast congrArg Int.cast hZuw
      _ = 1 := by norm_num
  -- C4-freeness of the outside block.
  have hC4out : ¬containsC4 {x : Fin 64 | x ∉ c.supp}
      (G.induce {x | x ∉ c.supp}) := by
    intro hC4
    obtain ⟨f, hf, hadj⟩ := hC4
    apply hfree
    refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
    intro i j hij
    exact hadj i j hij
  exact ⟨houtsideLabel, hqcard, htwoAll, hinj, hpairImage,
    hRreg, hRedges, hout, hC4out, hcross⟩

end

end Erdos85

#print axioms Erdos85.orderSixtyFour_regular_sizeSixteen_outsidePair_feasibility
