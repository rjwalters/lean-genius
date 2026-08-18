import Proofs.Erdos85OrderSixtyFourThreeComponentRepeatedClosing
import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters

/-! # Graph-facing adapter for a three-component repeated closing -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A repeated closing in a component block is an explicit owner-colored
fork, with all four vertex component memberships exposed. -/
theorem hasRepeatedClosingInBlock_iff_exists_ownerFork
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent) :
    HasRepeatedClosingInBlock D A B C e f g ↔
      ∃ x y z₁ z₂ : V,
        z₁ ≠ z₂ ∧
        D.connectedComponentMk x = e ∧
        D.connectedComponentMk y = f ∧
        D.connectedComponentMk z₁ = g ∧
        D.connectedComponentMk z₂ = g ∧
        A.Adj x y ∧ B.Adj y z₁ ∧ C.Adj z₁ x ∧
        B.Adj y z₂ ∧ C.Adj z₂ x := by
  classical
  constructor
  · rintro ⟨p, hp, r, hr, _hpr, hx, hy, hz⟩
    have hpBlock := Finset.mem_filter.mp hp
    have hrBlock := Finset.mem_filter.mp hr
    have hpColor := (Finset.mem_filter.mp hpBlock.1).2
    have hrColor := (Finset.mem_filter.mp hrBlock.1).2
    refine ⟨p.1, p.2.2, p.2.1, r.2.1, hz, ?_, ?_, ?_, ?_,
      hpColor.1, hpColor.2.1, hpColor.2.2, ?_, ?_⟩
    · exact (ConnectedComponent.mem_supp_iff e p.1).mp hpBlock.2.1
    · exact (ConnectedComponent.mem_supp_iff f p.2.2).mp hpBlock.2.2.1
    · exact (ConnectedComponent.mem_supp_iff g p.2.1).mp hpBlock.2.2.2
    · exact (ConnectedComponent.mem_supp_iff g r.2.1).mp hrBlock.2.2.2
    · simpa [hy] using hrColor.2.1
    · simpa [hx] using hrColor.2.2
  · rintro ⟨x, y, z₁, z₂, hz, hx, hy, hz₁, hz₂,
      hxy, hyz₁, hz₁x, hyz₂, hz₂x⟩
    let p : V × V × V := (x, z₁, y)
    let r : V × V × V := (x, z₂, y)
    have hp : p ∈ cyclicColoredTriplesInBlocks D A B C e f g := by
      simp [p, cyclicColoredTriplesInBlocks, cyclicColoredTriples,
        hxy, hyz₁, hz₁x, hx, hy, hz₁]
    have hr : r ∈ cyclicColoredTriplesInBlocks D A B C e f g := by
      simp [r, cyclicColoredTriplesInBlocks, cyclicColoredTriples,
        hxy, hyz₂, hz₂x, hx, hy, hz₂]
    refine ⟨p, hp, r, hr, ?_, rfl, rfl, ?_⟩
    · intro h
      apply hz
      simpa [p, r] using congrArg (fun t : V × V × V => t.2.1) h
    · simpa [p, r] using hz

/-- A nonlocal triple of component labels has exactly one of the three
two-equal shapes, or is genuinely rainbow. -/
theorem componentTriple_nonlocal_shape
    {α : Type*} [DecidableEq α] (e f g : α)
    (h : ¬ (e = f ∧ f = g)) :
    (e = f ∧ f ≠ g) ∨
      (f = g ∧ e ≠ f) ∨
      (e = g ∧ e ≠ f) ∨
      (e ≠ f ∧ f ≠ g ∧ e ≠ g) := by
  by_cases hef : e = f
  · exact Or.inl ⟨hef, fun hfg => h ⟨hef, hfg⟩⟩
  by_cases hfg : f = g
  · exact Or.inr (Or.inl ⟨hfg, hef⟩)
  by_cases heg : e = g
  · exact Or.inr (Or.inr (Or.inl ⟨heg, hef⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hef, hfg, heg⟩))

/-- In the rainbow component-pattern branch, the repeated closing feeds the
canonical ambient-fork separation theorem directly. -/
theorem hasRepeatedClosingInBlock_rainbow_canonicalCenter_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (a b c e f g : (secondOrderDefectGraph G).ConnectedComponent)
    (hbc : b ≠ c) (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
    (hrepeat : HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g) :
    ∃ (x : e.supp) (y : f.supp) (z₁ z₂ : g.supp),
      z₁.1 ≠ z₂.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x.1 y.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1 ∧
      (let ub₁ := crossCommonNeighbor G hfree hfg y z₁
       let ub₂ := crossCommonNeighbor G hfree hfg y z₂
       let uc₁ := crossCommonNeighbor G hfree heg x z₁
       let uc₂ := crossCommonNeighbor G hfree heg x z₂
       ub₁ ≠ ub₂ ∨ uc₁ ≠ uc₂) := by
  obtain ⟨x, y, z₁, z₂, hz, hx, hy, hz₁, hz₂,
    haxy, hbyz₁, hcz₁x, hbyz₂, hcz₂x⟩ :=
      (hasRepeatedClosingInBlock_iff_exists_ownerFork
        (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) c) e f g).mp hrepeat
  let xs : e.supp := ⟨x, (ConnectedComponent.mem_supp_iff e x).mpr hx⟩
  let ys : f.supp := ⟨y, (ConnectedComponent.mem_supp_iff f y).mpr hy⟩
  let z₁s : g.supp := ⟨z₁, (ConnectedComponent.mem_supp_iff g z₁).mpr hz₁⟩
  let z₂s : g.supp := ⟨z₂, (ConnectedComponent.mem_supp_iff g z₂).mpr hz₂⟩
  have hsep := ownerFork_canonicalCenter_separation G hfree hef hfg hfg
    heg heg hbc xs ys z₁s z₂s hz hbyz₁ hbyz₂ hcz₁x hcz₂x
  exact ⟨xs, ys, z₁s, z₂s, hz, haxy, hbyz₁, hcz₁x,
    hbyz₂, hcz₂x, hsep⟩

end

end Erdos85

#print axioms Erdos85.hasRepeatedClosingInBlock_iff_exists_ownerFork
#print axioms Erdos85.componentTriple_nonlocal_shape
#print axioms Erdos85.hasRepeatedClosingInBlock_rainbow_canonicalCenter_separation
