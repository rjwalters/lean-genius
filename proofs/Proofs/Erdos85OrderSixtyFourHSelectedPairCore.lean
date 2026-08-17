import Proofs.Erdos85OrderSixtyFourHMatchingInternalDisjoint
import Proofs.Erdos85OrderSixtyFourInternalPairLayer

/-! # The selected-pair core on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The selected pairs on H16 contain six disjoint perfect matchings and
sixteen further, distinct two-element pairs, disjoint from all matching
edges. -/
theorem orderSixtyFour_seven_defect_components_H_selectedPairCore
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
      ∃ μ : Fin 6 → Equiv.Perm c.supp,
        ∃ r : c.supp → Finset c.supp,
          (∀ i, Function.Involutive (μ i)) ∧
          (∀ i u, μ i u ≠ u) ∧
          (∀ i j, i ≠ j → ∀ u, μ i u ≠ μ j u) ∧
          (∀ u, (r u).card = 2) ∧
          Function.Injective r ∧
          ∀ i u y, {u, μ i u} ≠ r y := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _κ, μ, hinvol, hfreePoint, hmatchDisj,
      hinternalDisj⟩ :=
    orderSixtyFour_seven_defect_components_H_matching_internal_disjoint
      G hfree hmin hcover hcount
  obtain ⟨cI, hcI16, heqI, hinjI, _himage⟩ :=
    orderSixtyFour_seven_defect_components_internal_pair_layer
      G hfree hmin hcover hcount
  obtain ⟨d, hd16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have hcd : c = d := by
    by_contra hne
    have hc8 := hsmall c hne
    omega
  subst d
  have hcI : cI = c := by
    by_contra hne
    have hcI8 := hsmall cI hne
    omega
  subst cI
  obtain ⟨cB, hcB16, htwoB, _hsmallB⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  have hcB : c = cB := by
    by_contra hne
    have hc8 := (_hsmallB c hne).1
    omega
  subst cB
  let r : c.supp → Finset c.supp := fun u =>
    (G.induce c.supp).neighborFinset u
  have hrcard (u : c.supp) : (r u).card = 2 := by
    have h := htwoB u.1
    rw [heqI u] at h
    simpa [r] using h
  have hrinj : Function.Injective r := by
    intro u v huv
    apply hinjI
    change componentNeighborFinset G D c u.1 =
      componentNeighborFinset G D c v.1
    rw [heqI u, heqI v]
    simpa [r] using congrArg
      (Finset.map (.subtype (fun z : Fin 64 => z ∈ c.supp))) huv
  refine ⟨c, hc16, μ, r, hinvol, hfreePoint, hmatchDisj,
    hrcard, hrinj, ?_⟩
  intro i u y heq
  apply hinternalDisj i u y
  rw [heqI y]
  let ι : c.supp ↪ Fin 64 :=
    .subtype (fun z : Fin 64 => z ∈ c.supp)
  have hmap := congrArg (Finset.map ι) heq
  simpa [r, ι] using hmap

end

end Erdos85
