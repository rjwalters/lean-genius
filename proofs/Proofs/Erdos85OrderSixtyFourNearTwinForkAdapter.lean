import Proofs.Erdos85NearTwinOwnerFourCycle
import Proofs.Erdos85NearTwinLiteOwnerDichotomy

/-! # Global-to-component adapter for the order-64 near-twin fork -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Two vertices with positive defect codegree lie in the same defect
component, and their common-neighbor count is unchanged after inducing that
component. -/
theorem defect_codegree_six_component_adapter
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {x y : V}
    (hcode : (D.adjMatrix ℤ * D.adjMatrix ℤ) x y = 6) :
    let d := D.connectedComponentMk x
    ∃ hy : y ∈ d.supp,
      let xs : d.supp := ⟨x, by
        exact (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
      let ys : d.supp := ⟨y, hy⟩
      (((D.induce d.supp).neighborFinset xs) ∩
        ((D.induce d.supp).neighborFinset ys)).card = 6 := by
  classical
  let d := D.connectedComponentMk x
  have hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = 6 := by
    have h := adjMatrix_sq_apply_eq_card_common D x y
    rw [h] at hcode
    exact_mod_cast hcode
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show
      0 < (D.neighborFinset x ∩ D.neighborFinset y).card by omega)
  have hzData := Finset.mem_inter.mp hz
  have hxz : D.Adj x z := (D.mem_neighborFinset x z).mp hzData.1
  have hyz : D.Adj y z := (D.mem_neighborFinset y z).mp hzData.2
  have hcompXZ : D.connectedComponentMk x = D.connectedComponentMk z :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hxz
  have hcompYZ : D.connectedComponentMk y = D.connectedComponentMk z :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hyz
  have hyComp : D.connectedComponentMk y = d := by
    exact hcompYZ.trans hcompXZ.symm
  have hySupp : y ∈ d.supp :=
    (ConnectedComponent.mem_supp_iff d y).mpr hyComp
  refine ⟨hySupp, ?_⟩
  let xs : d.supp := ⟨x,
    (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let ys : d.supp := ⟨y, hySupp⟩
  change (((D.induce d.supp).neighborFinset xs) ∩
    ((D.induce d.supp).neighborFinset ys)).card = 6
  rw [← hcommon]
  apply Finset.card_bij (fun z _ => z.1)
  · intro z hz
    have hzData := Finset.mem_inter.mp hz
    apply Finset.mem_inter.mpr
    constructor
    · have hadj := ((D.induce d.supp).mem_neighborFinset xs z).mp hzData.1
      exact (D.mem_neighborFinset x z.1).mpr hadj
    · have hadj := ((D.induce d.supp).mem_neighborFinset ys z).mp hzData.2
      exact (D.mem_neighborFinset y z.1).mpr hadj
  · intro z₁ _ z₂ _ heq
    exact Subtype.ext heq
  · intro z hz
    have hzData := Finset.mem_inter.mp hz
    have hxz : D.Adj x z := (D.mem_neighborFinset x z).mp hzData.1
    have hzComp : D.connectedComponentMk z = d :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm
    let zs : d.supp := ⟨z,
      (ConnectedComponent.mem_supp_iff d z).mpr hzComp⟩
    refine ⟨zs, ?_, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · rw [SimpleGraph.mem_neighborFinset]
      exact hxz
    · rw [SimpleGraph.mem_neighborFinset]
      exact (D.mem_neighborFinset y z).mp hzData.2

/-- Positive codegree is enough for the component part of the preceding
adapter.  Moreover the exact codegree is preserved after inducing the common
connected component. -/
theorem defect_positive_codegree_component_adapter
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {x y : V} (k : ℕ) (hk : 0 < k)
    (hcode : (D.adjMatrix ℤ * D.adjMatrix ℤ) x y = (k : ℤ)) :
    let d := D.connectedComponentMk x
    ∃ hy : y ∈ d.supp,
      let xs : d.supp := ⟨x, by
        exact (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
      let ys : d.supp := ⟨y, hy⟩
      (((D.induce d.supp).neighborFinset xs) ∩
        ((D.induce d.supp).neighborFinset ys)).card = k := by
  classical
  let d := D.connectedComponentMk x
  have hcommon : (D.neighborFinset x ∩ D.neighborFinset y).card = k := by
    have h := adjMatrix_sq_apply_eq_card_common D x y
    rw [h] at hcode
    exact_mod_cast hcode
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (show
      0 < (D.neighborFinset x ∩ D.neighborFinset y).card by omega)
  have hzData := Finset.mem_inter.mp hz
  have hxz : D.Adj x z := (D.mem_neighborFinset x z).mp hzData.1
  have hyz : D.Adj y z := (D.mem_neighborFinset y z).mp hzData.2
  have hcompXZ : D.connectedComponentMk x = D.connectedComponentMk z :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hxz
  have hcompYZ : D.connectedComponentMk y = D.connectedComponentMk z :=
    ConnectedComponent.connectedComponentMk_eq_of_adj hyz
  have hyComp : D.connectedComponentMk y = d :=
    hcompYZ.trans hcompXZ.symm
  have hySupp : y ∈ d.supp :=
    (ConnectedComponent.mem_supp_iff d y).mpr hyComp
  refine ⟨hySupp, ?_⟩
  let xs : d.supp := ⟨x,
    (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let ys : d.supp := ⟨y, hySupp⟩
  change (((D.induce d.supp).neighborFinset xs) ∩
    ((D.induce d.supp).neighborFinset ys)).card = k
  rw [← hcommon]
  apply Finset.card_bij (fun z _ => z.1)
  · intro z hz
    have hzData := Finset.mem_inter.mp hz
    apply Finset.mem_inter.mpr
    constructor
    · exact (D.mem_neighborFinset x z.1).mpr
        (((D.induce d.supp).mem_neighborFinset xs z).mp hzData.1)
    · exact (D.mem_neighborFinset y z.1).mpr
        (((D.induce d.supp).mem_neighborFinset ys z).mp hzData.2)
  · intro z₁ _ z₂ _ heq
    exact Subtype.ext heq
  · intro z hz
    have hzData := Finset.mem_inter.mp hz
    have hxz : D.Adj x z := (D.mem_neighborFinset x z).mp hzData.1
    have hzComp : D.connectedComponentMk z = d :=
      (ConnectedComponent.connectedComponentMk_eq_of_adj hxz).symm
    let zs : d.supp := ⟨z,
      (ConnectedComponent.mem_supp_iff d z).mpr hzComp⟩
    refine ⟨zs, ?_, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · exact ((D.induce d.supp).mem_neighborFinset xs zs).mpr hxz
    · exact ((D.induce d.supp).mem_neighborFinset ys zs).mpr
        ((D.mem_neighborFinset y z).mp hzData.2)

/-- Codegree-five specialization used by the near-twin-lite `[16]` route. -/
theorem defect_codegree_five_component_adapter
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    {x y : V}
    (hcode : (D.adjMatrix ℤ * D.adjMatrix ℤ) x y = 5) :
    let d := D.connectedComponentMk x
    ∃ hy : y ∈ d.supp,
      let xs : d.supp := ⟨x, by
        exact (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
      let ys : d.supp := ⟨y, hy⟩
      (((D.induce d.supp).neighborFinset xs) ∩
        ((D.induce d.supp).neighborFinset ys)).card = 5 := by
  simpa using defect_positive_codegree_component_adapter D 5 (by norm_num) hcode

/-- Graph-facing composition of the component adapter with the near-twin
owner-fork theorem: a global codegree-six defect nonedge forces the repeated
non-base owner fork in its defect component whenever that component is in the
no-rainbow branch. -/
theorem orderSixtyFour_global_codegreeSix_forces_repeatedOwnerFork
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {x y : Fin 64} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y)
    (hcode : ((secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) x y = 6)
    (hno : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
        ¬ routingOwnerRainbow G d a b c) :
    ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      ∃ xs ys : d.supp,
        xs.1 = x ∧ ys.1 = y ∧
        let base := nondefectPairOwner G hfree
          hxy (by simpa using hnotD)
        let R :=
          ((((secondOrderDefectGraph G).induce d.supp)ᶜ.neighborFinset xs) ∩
            (((secondOrderDefectGraph G).induce d.supp)ᶜ.neighborFinset ys))
        ∃ owner r₁ r₂, owner ≠ base ∧ r₁ ≠ r₂ ∧
          r₁ ∈ R ∧ r₂ ∈ R ∧
          (restrictedComponentOwnerGraph G d owner).Adj xs r₁ ∧
          (restrictedComponentOwnerGraph G d owner).Adj ys r₁ ∧
          (restrictedComponentOwnerGraph G d owner).Adj xs r₂ ∧
          (restrictedComponentOwnerGraph G d owner).Adj ys r₂ := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  obtain ⟨hySupp, hindCode⟩ :=
    defect_codegree_six_component_adapter D hcode
  let xs : d.supp := ⟨x,
    (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let ys : d.supp := ⟨y, hySupp⟩
  have hxySub : xs ≠ ys := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hnotInd : ¬ (D.induce d.supp).Adj xs ys := by
    simpa [D, xs, ys] using hnotD
  have hfork := orderSixtyFour_codegreeSix_forces_repeatedOwnerFork
    G hfree hreg hcount d xs ys hxySub hnotInd hindCode (hno d)
  refine ⟨d, xs, ys, rfl, rfl, ?_⟩
  simpa [D, d, xs, ys] using hfork

/-- Condensed global endpoint: in the no-rainbow branch, an ambient defect
near-twin forces a four-cycle in a non-base restricted owner factor of its
defect component. -/
theorem orderSixtyFour_global_codegreeSix_forces_ownerFactor_C4
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {x y : Fin 64} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y)
    (hcode : ((secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) x y = 6)
    (hno : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
        ¬ routingOwnerRainbow G d a b c) :
    ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      ∃ xs ys : d.supp,
        xs.1 = x ∧ ys.1 = y ∧
        ∃ owner,
          owner ≠ nondefectPairOwner G hfree hxy (by simpa using hnotD) ∧
          containsC4 d.supp
            (restrictedComponentOwnerGraph G d owner) := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  obtain ⟨hySupp, hindCode⟩ :=
    defect_codegree_six_component_adapter D hcode
  let xs : d.supp := ⟨x,
    (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let ys : d.supp := ⟨y, hySupp⟩
  have hxySub : xs ≠ ys := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hnotInd : ¬ (D.induce d.supp).Adj xs ys := by
    simpa [D, xs, ys] using hnotD
  obtain ⟨owner, howner, hC4⟩ :=
    orderSixtyFour_codegreeSix_forces_ownerFactor_C4
      G hfree hreg hcount d xs ys hxySub hnotInd hindCode (hno d)
  refine ⟨d, xs, ys, rfl, rfl, owner, ?_, hC4⟩
  simpa [D, d, xs, ys] using howner

/-- Global λ=5 endpoint for the near-twin-lite route.  An ambient
codegree-five defect nonedge either forces a repeated non-base owner fork in
its component or lands on the sharp exact-three owner-color boundary. -/
theorem orderSixtyFour_global_codegreeFive_ownerFork_or_exactThree
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {x y : Fin 64} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y)
    (hcode : ((secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) x y = 5)
    (hno : ∀ d : (secondOrderDefectGraph G).ConnectedComponent,
      ∀ a b c, a ≠ b → a ≠ c → b ≠ c →
        ¬ routingOwnerRainbow G d a b c) :
    ∃ d : (secondOrderDefectGraph G).ConnectedComponent,
      ∃ xs ys : d.supp,
        xs.1 = x ∧ ys.1 = y ∧
        let base := nondefectPairOwner G hfree hxy (by simpa using hnotD)
        let left := fun r : d.supp =>
          nondefectPairOwnerOrBase G hfree base xs.1 r.1
        let right := fun r : d.supp =>
          nondefectPairOwnerOrBase G hfree base ys.1 r.1
        let R :=
          ((((secondOrderDefectGraph G).induce d.supp)ᶜ.neighborFinset xs) ∩
            (((secondOrderDefectGraph G).induce d.supp)ᶜ.neighborFinset ys))
        (∃ owner r₁ r₂, owner ≠ base ∧ r₁ ≠ r₂ ∧
          r₁ ∈ R ∧ r₂ ∈ R ∧
          (restrictedComponentOwnerGraph G d owner).Adj xs r₁ ∧
          (restrictedComponentOwnerGraph G d owner).Adj ys r₁ ∧
          (restrictedComponentOwnerGraph G d owner).Adj xs r₂ ∧
          (restrictedComponentOwnerGraph G d owner).Adj ys r₂) ∨
          (R.filter fun r =>
            left r = right r ∧ left r ≠ base).card = 3 := by
  classical
  let D := secondOrderDefectGraph G
  let d := D.connectedComponentMk x
  obtain ⟨hySupp, hindCode⟩ :=
    defect_codegree_five_component_adapter D hcode
  let xs : d.supp := ⟨x,
    (ConnectedComponent.mem_supp_iff d x).mpr rfl⟩
  let ys : d.supp := ⟨y, hySupp⟩
  have hxySub : xs ≠ ys := by
    intro h
    exact hxy (congrArg Subtype.val h)
  have hnotInd : ¬ (D.induce d.supp).Adj xs ys := by
    simpa [D, xs, ys] using hnotD
  have hdichotomy := orderSixtyFour_codegreeFive_ownerFork_or_exactThree
    G hfree hreg hcount d xs ys hxySub hnotInd hindCode (hno d)
  refine ⟨d, xs, ys, rfl, rfl, ?_⟩
  simpa [D, d, xs, ys] using hdichotomy

end

end Erdos85
