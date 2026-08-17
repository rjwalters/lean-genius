import Proofs.Erdos85BinarySquareMixedOwnerRootedPatternBounds

/-! # Upper bound for the rooted two-external-vertices-together pattern -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem orderSixtyFour_ownerNeighbors_sameComponent_card_eq_two
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) (x : Fin 64) :
    (((componentOwnerGraph G (secondOrderDefectGraph G) owner).neighborFinset x).filter
      fun y => (secondOrderDefectGraph G).connectedComponentMk y =
        (secondOrderDefectGraph G).connectedComponentMk x).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  let O := componentOwnerGraph G D owner
  let xd : d.supp := ⟨x, (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hdeg := binarySquare_regular_twoSizeTwoParts_restrictedOwner_degree_two
    G hfree (q := 8) (by norm_num) hreg (by norm_num) d owner
      (by simpa using hall d) (by simpa using hall owner) xd
  let S := (O.neighborFinset x).filter fun y => D.connectedComponentMk y = d
  let T := (restrictedComponentOwnerGraph G d owner).neighborFinset xd
  have hcard : S.card = T.card := by
    apply Finset.card_bij
      (fun y hy => (⟨y, (ConnectedComponent.mem_supp_iff d y).mpr
        (Finset.mem_filter.mp hy).2⟩ : d.supp))
    · intro y hy
      exact ((restrictedComponentOwnerGraph G d owner).mem_neighborFinset _ _).mpr
        ((O.mem_neighborFinset _ _).mp (Finset.mem_filter.mp hy).1)
    · intro y₁ hy₁ y₂ hy₂ h
      exact congrArg Subtype.val h
    · intro y hy
      refine ⟨y.1, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨(O.mem_neighborFinset _ _).mpr
          (((restrictedComponentOwnerGraph G d owner).mem_neighborFinset _ _).mp hy),
        (ConnectedComponent.mem_supp_iff d y.1).mp y.2⟩
  rw [hcard, SimpleGraph.card_neighborFinset_eq_degree, hdeg]

private theorem orderSixtyFour_ownerNeighbors_otherComponents_card_eq_twelve
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) (x : Fin 64) :
    (((componentOwnerGraph G (secondOrderDefectGraph G) owner).neighborFinset x).filter
      fun y => (secondOrderDefectGraph G).connectedComponentMk y ≠
        (secondOrderDefectGraph G).connectedComponentMk x).card = 12 := by
  let D := secondOrderDefectGraph G
  let O := componentOwnerGraph G D owner
  have hall := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount
  have hdegree : O.degree x = 14 := by
    simpa [O, D] using binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) owner
        (m_c := 2) (by norm_num [hall owner]) x
  have hlocal := orderSixtyFour_ownerNeighbors_sameComponent_card_eq_two
    G hfree hreg hcount owner x
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := O.neighborFinset x)
    (p := fun y => D.connectedComponentMk y = D.connectedComponentMk x)
  change ((O.neighborFinset x).filter fun y =>
      D.connectedComponentMk y = D.connectedComponentMk x).card +
    ((O.neighborFinset x).filter fun y =>
      D.connectedComponentMk y ≠ D.connectedComponentMk x).card =
      (O.neighborFinset x).card at hsplit
  rw [SimpleGraph.card_neighborFinset_eq_degree, hdegree] at hsplit
  change ((O.neighborFinset x).filter fun y =>
      D.connectedComponentMk y = D.connectedComponentMk x).card = 2 at hlocal
  simpa [O, D] using (show
    (((O.neighborFinset x).filter fun y =>
      D.connectedComponentMk y ≠ D.connectedComponentMk x).card = 12) by
        omega)

set_option maxRecDepth 10000 in
/-- Pattern three has at most `12·2=24` elements: there are twelve possible
external first steps and two same-component second steps of the next owner
color. -/
theorem orderSixtyFour_regular_fourComponents_rootedPattern_three_card_le_twentyFour
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (a b c : (secondOrderDefectGraph G).ConnectedComponent) (x : Fin 64) :
    (rootedComponentPatternPairs (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) x 3).card ≤ 24 := by
  classical
  let D := secondOrderDefectGraph G
  let OA := componentOwnerGraph G D a
  let OB := componentOwnerGraph G D b
  let OC := componentOwnerGraph G D c
  let Y := (OA.neighborFinset x).filter fun y =>
    D.connectedComponentMk y ≠ D.connectedComponentMk x
  let Z := fun y : Fin 64 => (OB.neighborFinset y).filter fun z =>
    D.connectedComponentMk z = D.connectedComponentMk y
  let T := Y.sigma Z
  let S := rootedComponentPatternPairs D OA OB OC x 3
  let F : (p : ↥S) → Σ _y : Fin 64, Fin 64 := fun p => ⟨p.1.2, p.1.1⟩
  have hFmem : ∀ p : ↥S, F p ∈ T := by
    intro p
    have hp := Finset.mem_filter.mp p.2
    have hcolor := (Finset.mem_filter.mp hp.1).2
    have hpattern := (rootedComponentPattern_eq_three_iff D x p.1).mp hp.2
    change (⟨p.1.2, p.1.1⟩ : Σ _y : Fin 64, Fin 64) ∈ Y.sigma Z
    exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr
      ⟨(OA.mem_neighborFinset _ _).mpr hcolor.1, hpattern.1⟩,
      Finset.mem_filter.mpr
        ⟨(OB.mem_neighborFinset _ _).mpr hcolor.2.1, hpattern.2.2.symm⟩⟩
  let lift : ↥S → ↥T := fun p => ⟨F p, hFmem p⟩
  have hinj : Function.Injective lift := by
    intro p q hpq
    have hval : F p = F q := congrArg Subtype.val hpq
    have hy : p.1.2 = q.1.2 := congrArg Sigma.fst hval
    have hz : p.1.1 = q.1.1 :=
      congrArg (fun r : Σ _ : Fin 64, Fin 64 => r.2) hval
    apply Subtype.ext
    exact Prod.ext hz hy
  have hle : S.card ≤ T.card := Finset.card_le_card_of_injective hinj
  have hY : Y.card = 12 :=
    orderSixtyFour_ownerNeighbors_otherComponents_card_eq_twelve
      G hfree hreg hcount a x
  have hZ : ∀ y : Fin 64, (Z y).card = 2 :=
    orderSixtyFour_ownerNeighbors_sameComponent_card_eq_two
      G hfree hreg hcount b
  calc
    _ = S.card := rfl
    _ ≤ T.card := hle
    _ = 24 := by
      rw [Finset.card_sigma]
      simp [hZ, hY]

end

end Erdos85
