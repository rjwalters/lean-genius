import Proofs.Erdos85OrderSixtyFourSmallBlockPerfectMatching

/-! # The six small-block matchings on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Each small block pairs the sixteen vertices of the distinguished
component according to their common small-block neighbor.  The resulting
six fixed-point-free involutions are pointwise disjoint. -/
theorem orderSixtyFour_seven_defect_components_H_matchingFamily
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
      ∃ κ : Fin 6 ≃ {k // k ≠ c},
        ∃ μ : Fin 6 → Equiv.Perm c.supp,
          (∀ i, Function.Involutive (μ i)) ∧
          (∀ i u, μ i u ≠ u) ∧
          (∀ i j, i ≠ j → ∀ u, μ i u ≠ μ j u) ∧
          ∀ i u, ∃ x : (κ i).1.supp,
            G.Adj x.1 u.1 ∧ G.Adj x.1 (μ i u).1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hHcard, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  let K := {k : D.ConnectedComponent // k ≠ c}
  have hKcard : Fintype.card K = 6 := by
    rw [Fintype.card_subtype_compl (fun k : D.ConnectedComponent => k = c), hcount]
    simp
  let κ : Fin 6 ≃ K :=
    (finCongr hKcard.symm).trans (Fintype.equivFin K).symm
  let blockSet (i : Fin 6) (u : c.supp) : Finset (Fin 64) :=
    componentNeighborFinset G D (κ i).1 u.1
  have hblockCard (i : Fin 6) (u : c.supp) : (blockSet i u).card = 1 :=
    (hsmall (κ i).1 (κ i).2).2 u.1
  let xVal (i : Fin 6) (u : c.supp) : Fin 64 :=
    Classical.choose (Finset.card_eq_one.mp (hblockCard i u))
  have hx_mem (i : Fin 6) (u : c.supp) : xVal i u ∈ blockSet i u := by
    have hs := Classical.choose_spec (Finset.card_eq_one.mp (hblockCard i u))
    rw [hs]
    simp [xVal]
  have hx_supp (i : Fin 6) (u : c.supp) : xVal i u ∈ (κ i).1.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (Finset.mem_filter.mp (hx_mem i u)).2
  let xBlock (i : Fin 6) (u : c.supp) : (κ i).1.supp :=
    ⟨xVal i u, hx_supp i u⟩
  have hx_adj (i : Fin 6) (u : c.supp) : G.Adj (xBlock i u).1 u.1 := by
    exact ((G.mem_neighborFinset u.1 (xVal i u)).mp
      (Finset.mem_filter.mp (hx_mem i u)).1).symm
  let hSet (i : Fin 6) (u : c.supp) : Finset (Fin 64) :=
    componentNeighborFinset G D c (xBlock i u).1
  have hu_hSet (i : Fin 6) (u : c.supp) : u.1 ∈ hSet i u := by
    apply Finset.mem_filter.mpr
    refine ⟨(G.mem_neighborFinset (xBlock i u).1 u.1).mpr (hx_adj i u), ?_⟩
    exact (ConnectedComponent.mem_supp_iff c u.1).mp u.2
  let otherSet (i : Fin 6) (u : c.supp) : Finset (Fin 64) :=
    (hSet i u).erase u.1
  have hotherCard (i : Fin 6) (u : c.supp) : (otherSet i u).card = 1 := by
    have herase := Finset.card_erase_of_mem (hu_hSet i u)
    have htwo : (hSet i u).card = 2 := hHcard (xBlock i u).1
    simp only [otherSet]
    omega
  let mateVal (i : Fin 6) (u : c.supp) : Fin 64 :=
    Classical.choose (Finset.card_eq_one.mp (hotherCard i u))
  have hmate_mem (i : Fin 6) (u : c.supp) :
      mateVal i u ∈ otherSet i u := by
    have hs := Classical.choose_spec (Finset.card_eq_one.mp (hotherCard i u))
    rw [hs]
    simp [mateVal]
  have hmate_supp (i : Fin 6) (u : c.supp) : mateVal i u ∈ c.supp := by
    have hmH : mateVal i u ∈ hSet i u :=
      Finset.mem_of_mem_erase (hmate_mem i u)
    rw [ConnectedComponent.mem_supp_iff]
    exact (Finset.mem_filter.mp hmH).2
  let mate (i : Fin 6) (u : c.supp) : c.supp :=
    ⟨mateVal i u, hmate_supp i u⟩
  have hmate_ne (i : Fin 6) (u : c.supp) : mate i u ≠ u := by
    intro h
    have hval : mateVal i u = u.1 := congrArg Subtype.val h
    exact (Finset.ne_of_mem_erase (hmate_mem i u)) hval
  have hmate_hSet (i : Fin 6) (u : c.supp) :
      (mate i u).1 ∈ hSet i u :=
    Finset.mem_of_mem_erase (hmate_mem i u)
  have hmate_adj (i : Fin 6) (u : c.supp) :
      G.Adj (xBlock i u).1 (mate i u).1 := by
    exact (G.mem_neighborFinset (xBlock i u).1 (mate i u).1).mp
      (Finset.mem_filter.mp (hmate_hSet i u)).1
  have hxBlock_mate (i : Fin 6) (u : c.supp) :
      xBlock i (mate i u) = xBlock i u := by
    apply Subtype.ext
    let S := blockSet i (mate i u)
    have hxS : (xBlock i u).1 ∈ S := by
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset (mate i u).1 (xBlock i u).1).mpr
        (hmate_adj i u).symm, ?_⟩
      exact (ConnectedComponent.mem_supp_iff (κ i).1 (xBlock i u).1).mp
        (xBlock i u).2
    have hchosen : (xBlock i (mate i u)).1 ∈ S := hx_mem i (mate i u)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hblockCard i (mate i u))
    change blockSet i (mate i u) = {a} at ha
    change (xBlock i u).1 ∈ blockSet i (mate i u) at hxS
    change (xBlock i (mate i u)).1 ∈ blockSet i (mate i u) at hchosen
    rw [ha] at hxS hchosen
    simpa using (show (xBlock i (mate i u)).1 = (xBlock i u).1 by
      have h1 : (xBlock i u).1 = a := by simpa using hxS
      have h2 : (xBlock i (mate i u)).1 = a := by simpa using hchosen
      exact h2.trans h1.symm)
  have hmate_invol (i : Fin 6) : Function.Involutive (mate i) := by
    intro u
    apply Subtype.ext
    have hsets : hSet i (mate i u) = hSet i u := by
      simp only [hSet, hxBlock_mate i u]
    have huOther : u.1 ∈ otherSet i (mate i u) := by
      apply Finset.mem_erase.mpr
      refine ⟨?_, ?_⟩
      · exact fun h => hmate_ne i u (Subtype.ext h.symm)
      · rw [hsets]
        exact hu_hSet i u
    have hmOther := hmate_mem i (mate i u)
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hotherCard i (mate i u))
    rw [ha] at huOther hmOther
    have hu : u.1 = a := by simpa using huOther
    have hm : mateVal i (mate i u) = a := by simpa using hmOther
    exact hm.trans hu.symm
  let μ : Fin 6 → Equiv.Perm c.supp := fun i =>
    { toFun := mate i
      invFun := mate i
      left_inv := hmate_invol i
      right_inv := hmate_invol i }
  have hblocks_ne {i j : Fin 6} (hij : i ≠ j) (u : c.supp) :
      (xBlock i u).1 ≠ (xBlock j u).1 := by
    intro h
    have hi : D.connectedComponentMk (xBlock i u).1 = (κ i).1 :=
      (ConnectedComponent.mem_supp_iff (κ i).1 (xBlock i u).1).mp
        (xBlock i u).2
    have hj : D.connectedComponentMk (xBlock j u).1 = (κ j).1 :=
      (ConnectedComponent.mem_supp_iff (κ j).1 (xBlock j u).1).mp
        (xBlock j u).2
    have hcEq : (κ i).1 = (κ j).1 := by rw [← hi, h, hj]
    exact hij (κ.injective (Subtype.ext hcEq))
  refine ⟨c, hc16, κ, μ, hmate_invol, ?_, ?_, ?_⟩
  · exact hmate_ne
  · intro i j hij u hEq
    change mate i u = mate j u at hEq
    have huv : u.1 ≠ (μ i u).1 := by
      intro h
      exact hmate_ne i u (Subtype.ext h.symm)
    have hxi_u := hx_adj i u
    have hxi_v := hmate_adj i u
    have hxj_u := hx_adj j u
    have hxj_v : G.Adj (xBlock j u).1 (μ i u).1 := by
      change G.Adj (xBlock j u).1 (mate i u).1
      rw [hEq]
      exact hmate_adj j u
    exact hfree (containsC4_of_two_common huv (hblocks_ne hij u)
      hxi_u hxi_v hxj_u hxj_v)
  · intro i u
    exact ⟨xBlock i u, hx_adj i u, hmate_adj i u⟩

end

end Erdos85
