import Proofs.Erdos85NearTwinOwnerFork

/-! # A defect near-twin forces an owner-factor four-cycle -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A `K₂,₂` witness gives a four-cycle. -/
theorem containsC4_of_complete_bipartite_two_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) {x y r₁ r₂ : V}
    (hxy : x ≠ y) (hr : r₁ ≠ r₂)
    (hxr₁ : x ≠ r₁) (hxr₂ : x ≠ r₂)
    (hyr₁ : y ≠ r₁) (hyr₂ : y ≠ r₂)
    (hx₁ : H.Adj x r₁) (hy₁ : H.Adj y r₁)
    (hx₂ : H.Adj x r₂) (hy₂ : H.Adj y r₂) :
    containsC4 V H := by
  let f : Fin 4 → V := ![x, r₁, y, r₂]
  refine ⟨f, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [f, Matrix.cons_val_zero, Matrix.cons_val_one]
  · intro i j hij
    have hx₁' := hx₁.symm
    have hy₁' := hy₁.symm
    have hx₂' := hx₂.symm
    have hy₂' := hy₂.symm
    fin_cases i <;> fin_cases j <;>
      simp_all [C4, f, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- In the order-sixty-four no-rainbow branch, a defect codegree-six
nonedge forces a four-cycle in a non-base restricted owner factor. -/
theorem orderSixtyFour_codegreeSix_forces_ownerFactor_C4
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ z, G.degree z = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (x y : d.supp) (hxy : x ≠ y)
    (hnot : ¬ ((secondOrderDefectGraph G).induce d.supp).Adj x y)
    (hcode : ((((secondOrderDefectGraph G).induce d.supp).neighborFinset x) ∩
      (((secondOrderDefectGraph G).induce d.supp).neighborFinset y)).card = 6)
    (hno : ∀ a b c,
      a ≠ b → a ≠ c → b ≠ c → ¬ routingOwnerRainbow G d a b c) :
    ∃ owner,
      owner ≠ nondefectPairOwner G hfree
        (fun h => hxy (Subtype.ext h)) (by simpa using hnot) ∧
      containsC4 d.supp (restrictedComponentOwnerGraph G d owner) := by
  classical
  let H := (secondOrderDefectGraph G).induce d.supp
  let R := Hᶜ.neighborFinset x ∩ Hᶜ.neighborFinset y
  obtain ⟨owner, r₁, r₂, hob, hr, hr₁, hr₂,
      hxr₁, hyr₁, hxr₂, hyr₂⟩ :=
    orderSixtyFour_codegreeSix_forces_repeatedOwnerFork
      G hfree hreg hcount d x y hxy hnot hcode hno
  have hx₁ : x ≠ r₁ := by
    intro heq
    subst r₁
    exact Hᶜ.loopless.irrefl x
      ((Hᶜ.mem_neighborFinset x x).mp (Finset.mem_inter.mp hr₁).1)
  have hx₂ : x ≠ r₂ := by
    intro heq
    subst r₂
    exact Hᶜ.loopless.irrefl x
      ((Hᶜ.mem_neighborFinset x x).mp (Finset.mem_inter.mp hr₂).1)
  have hy₁ : y ≠ r₁ := by
    intro heq
    subst r₁
    exact Hᶜ.loopless.irrefl y
      ((Hᶜ.mem_neighborFinset y y).mp (Finset.mem_inter.mp hr₁).2)
  have hy₂ : y ≠ r₂ := by
    intro heq
    subst r₂
    exact Hᶜ.loopless.irrefl y
      ((Hᶜ.mem_neighborFinset y y).mp (Finset.mem_inter.mp hr₂).2)
  exact ⟨owner, hob,
    containsC4_of_complete_bipartite_two_two
      (restrictedComponentOwnerGraph G d owner)
      hxy hr hx₁ hx₂ hy₁ hy₂ hxr₁ hyr₁ hxr₂ hyr₂⟩

end

end Erdos85
