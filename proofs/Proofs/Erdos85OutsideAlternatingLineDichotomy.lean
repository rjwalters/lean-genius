import Proofs.Erdos85OrderSixtyFourOutsideSpectralDichotomy
import Proofs.Erdos85OrderSixtyFourPairQuotient
import Proofs.Erdos85BipartiteRegularSignedEigenvector

/-!
# The exterior-pair bottom branch produces an alternating joint eigenline
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Commutation of graph adjacency matrices descends from `ℂ` to `ℤ`. -/
theorem adjMatrix_comm_int_of_complex
    {V : Type*} [Fintype V] [DecidableEq V]
    (R H : SimpleGraph V) [DecidableRel R.Adj] [DecidableRel H.Adj]
    (hcomm : R.adjMatrix ℂ * H.adjMatrix ℂ =
      H.adjMatrix ℂ * R.adjMatrix ℂ) :
    R.adjMatrix ℤ * H.adjMatrix ℤ =
      H.adjMatrix ℤ * R.adjMatrix ℤ := by
  have hm : (R.adjMatrix ℤ * H.adjMatrix ℤ).map (Int.castRingHom ℂ) =
      (H.adjMatrix ℤ * R.adjMatrix ℤ).map (Int.castRingHom ℂ) := by
    simpa only [Matrix.map_mul, adjMatrix_map_intCast] using hcomm
  ext x y
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℂ)))
  simpa using congrFun (congrFun hm x) y

/-- In the order-64 seven-component branch, bipartiteness of the exterior-pair
graph supplies a signed vector spanning an `R` bottom line which is also an
integral eigenline of the internal ambient two-factor `H`. -/
theorem orderSixtyFour_seven_components_pairBipartite_produces_jointEigenline
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
      let H := G.induce c.supp
      let R := exteriorPairGraph G c.supp
      R.IsBipartite →
      ∃ (mu : ℤ) (s : c.supp → ℤ),
        (∀ x, s x = -1 ∨ s x = 1) ∧
        (∀ x, ∑ y ∈ R.neighborFinset x, s y = -6 * s x) ∧
        (H.adjMatrix ℤ).mulVec s = mu • s := by
  classical
  obtain ⟨c, hc, _label, _hqcard, _hpairTwo, _hinj, _himage,
      hRreg, _hRedges, _hCreg, _hC4, _hcross⟩ :=
    orderSixtyFour_seven_components_outside_feasibility
      G hfree hmin hcover hcount
  obtain ⟨d, hd, hgram, _hdRreg⟩ :=
    orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
      G hfree hmin hcover hcount
  obtain ⟨e, he, hetwo⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  obtain ⟨base, _hbase, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a : (secondOrderDefectGraph G).ConnectedComponent},
      a.supp.ncard = 16 → a = base := by
    intro a ha
    by_contra hne
    have := hsmall a hne
    omega
  have hcd : c = d := (heq_of_16 hc).trans (heq_of_16 hd).symm
  have hce : c = e := (heq_of_16 hc).trans (heq_of_16 he).symm
  subst d
  subst e
  refine ⟨c, hc, ?_⟩
  dsimp only
  intro hbip
  let H := G.induce c.supp
  let R := exteriorPairGraph G c.supp
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let Q := B * Matrix.conjTranspose B
  have hcommQ := orderSixtyFour_defectComponent_exteriorGram_comm
    G hfree hmin hcover c hetwo |>.1
  change H.adjMatrix ℂ * Q = Q * H.adjMatrix ℂ at hcommQ
  change Q = (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
    R.adjMatrix ℂ at hgram
  have hcommC : H.adjMatrix ℂ * R.adjMatrix ℂ =
      R.adjMatrix ℂ * H.adjMatrix ℂ := by
    rw [hgram] at hcommQ
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at hcommQ
    exact add_left_cancel hcommQ
  have hcommZ : H.adjMatrix ℤ * R.adjMatrix ℤ =
      R.adjMatrix ℤ * H.adjMatrix ℤ :=
    adjMatrix_comm_int_of_complex H R hcommC
  have hcardc : Fintype.card c.supp = 16 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq c.supp
      _ = 16 := hc
  letI : Nonempty c.supp := Set.nonempty_coe_sort.mpr c.nonempty_supp
  have hRconn : R.Connected :=
    connected_of_isBipartite_regular_of_card_lt_four_mul
      R 6 (by omega) hRreg hbip (by rw [hcardc]; omega)
  exact commutingGraph_exists_eigenvalue_of_connected_bipartite_regular
    R H hRconn hbip 6 hRreg hcommZ

/-- Final kernel-side packaging: every nonzero nonprincipal internal mode
either transports to the exterior adjacency block, or the pair-graph bottom
branch manufactures an alternating integral joint eigenline. -/
theorem orderSixtyFour_seven_components_outside_transport_or_jointEigenline
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
      let H := G.induce c.supp
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let C := (G.induce q).adjMatrix ℂ
      let R := exteriorPairGraph G c.supp
      ∀ (v : c.supp → ℂ) (lambda : ℂ),
        v ≠ 0 → lambda ≠ 2 →
        (H.adjMatrix ℂ).mulVec v = lambda • v →
        (B.transpose.mulVec v ≠ 0 ∧
          C.mulVec (B.transpose.mulVec v) =
            (-lambda) • B.transpose.mulVec v) ∨
        ∃ (mu : ℤ) (s : c.supp → ℤ),
          (∀ x, s x = -1 ∨ s x = 1) ∧
          (∀ x, ∑ y ∈ R.neighborFinset x, s y = -6 * s x) ∧
          (H.adjMatrix ℤ).mulVec s = mu • s := by
  classical
  obtain ⟨c, hc, hdich⟩ :=
    orderSixtyFour_seven_components_outside_transport_or_pairBipartite
      G hfree hmin hcover hcount
  obtain ⟨d, hd, hbipJoint⟩ :=
    orderSixtyFour_seven_components_pairBipartite_produces_jointEigenline
      G hfree hmin hcover hcount
  obtain ⟨base, _hbase, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a : (secondOrderDefectGraph G).ConnectedComponent},
      a.supp.ncard = 16 → a = base := by
    intro a ha
    by_contra hne
    have := hsmall a hne
    omega
  have hcd : c = d := (heq_of_16 hc).trans (heq_of_16 hd).symm
  subst d
  refine ⟨c, hc, ?_⟩
  dsimp only at hdich hbipJoint ⊢
  intro v lambda hvne hlambda hHv
  rcases hdich v lambda hvne hlambda hHv with htransport | hbip
  · exact Or.inl htransport
  · exact Or.inr (hbipJoint hbip)

end

end Erdos85

#print axioms Erdos85.adjMatrix_comm_int_of_complex
#print axioms Erdos85.orderSixtyFour_seven_components_pairBipartite_produces_jointEigenline
#print axioms Erdos85.orderSixtyFour_seven_components_outside_transport_or_jointEigenline
