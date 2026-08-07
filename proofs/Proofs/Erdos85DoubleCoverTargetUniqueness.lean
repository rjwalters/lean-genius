import Proofs.Erdos85SquareMinimumDoubleCoverEscape

/-!
# A cyclic double-cover target has a unique source component

If a cycle of order `2r` were a cyclic double-cover target of two disjoint
cycles of order `r`, each antipodal pair in the target would have one common
neighbor in each source.  Those two distinct common neighbors form a
four-cycle with the antipodal pair.  This packages that observation using
`cycleCover_halfTurn_commonNeighbor_exclusive`.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- **Two disjoint cycles cannot cover the same doubled target.** -/
theorem false_of_two_disjoint_cycleCovers_same_doubleTarget
    {V : Type*} [Fintype V] [DecidableEq V]
    {r : ℕ} [NeZero r]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u₁ u₂ : ZMod r → V) (v : ZMod (2 * r) → V)
    (hvinj : Function.Injective v)
    (hdisjoint : ∀ x z, u₁ x ≠ u₂ z)
    (f₁ f₂ : ZMod (2 * r) → ZMod r)
    (hadj₁ : ∀ x y, G.Adj (u₁ x) (v y) ↔ x = f₁ y)
    (hadj₂ : ∀ x y, G.Adj (u₂ x) (v y) ↔ x = f₂ y)
    (horient₁ : (∀ y, f₁ (y + 1) = f₁ y + 1) ∨
      (∀ y, f₁ (y + 1) = f₁ y - 1))
    (horient₂ : (∀ y, f₂ (y + 1) = f₂ y + 1) ∨
      (∀ y, f₂ (y + 1) = f₂ y - 1)) : False := by
  let y : ZMod (2 * r) := 0
  let w : V := u₂ (f₂ y)
  have hw : w ≠ u₁ (f₁ y) := by
    exact (hdisjoint (f₁ y) (f₂ y)).symm
  have hexclusive := cycleCover_halfTurn_commonNeighbor_exclusive
    G hfree u₁ v hvinj f₁ hadj₁ horient₁ y w hw
  apply hexclusive
  constructor
  · exact (hadj₂ (f₂ y) y).mpr rfl
  · apply (hadj₂ (f₂ y) (y + (r : ZMod (2 * r)))).mpr
    exact (cycleCoverMap_halfTurn_invariant f₂ horient₂ y).symm

/-- **Graph-facing uniqueness of the source of a doubled target.**  Two
distinct defect components of order `r` cannot both have reverse quotient
entry one from the same defect component labeled by `ZMod (2*r)`. -/
theorem secondOrder_doubleCover_target_source_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r : ℕ} [NeZero r]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r)
    (c₁ c₂ e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcne : c₁ ≠ c₂)
    (u₁ u₂ : ZMod r → V) (v : ZMod (2 * r) → V)
    (hu₁ : Function.Injective u₁) (hu₂ : Function.Injective u₂)
    (hv : Function.Injective v)
    (hu₁Range : Set.range u₁ = c₁.supp)
    (hu₂Range : Set.range u₂ = c₂.supp)
    (hvRange : Set.range v = e.supp)
    (hu₁D : ∀ x, (secondOrderDefectGraph G).neighborFinset (u₁ x) =
      {u₁ (x - 1), u₁ (x + 1)})
    (hu₂D : ∀ x, (secondOrderDefectGraph G).neighborFinset (u₂ x) =
      {u₂ (x - 1), u₂ (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)})
    (hone₁ : componentQuotientMatrix G (secondOrderDefectGraph G) e c₁ = 1)
    (hone₂ : componentQuotientMatrix G (secondOrderDefectGraph G) e c₂ = 1) :
    False := by
  letI : NeZero (2 * r) := ⟨by
    have hrpos : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
    omega⟩
  have htwoR : 3 ≤ 2 * r := by omega
  obtain ⟨f₁, hadj₁, horient₁⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree hd heven hmin hcard hr htwoR c₁ e u₁ v hu₁ hv
        hu₁Range hvRange hu₁D hvD hone₁
  obtain ⟨f₂, hadj₂, horient₂⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree hd heven hmin hcard hr htwoR c₂ e u₂ v hu₂ hv
        hu₂Range hvRange hu₂D hvD hone₂
  have hdisjoint : ∀ x z, u₁ x ≠ u₂ z := by
    intro x z hxz
    have hx₁ : u₁ x ∈ c₁.supp := by
      rw [← hu₁Range]
      exact ⟨x, rfl⟩
    have hz₂ : u₂ z ∈ c₂.supp := by
      rw [← hu₂Range]
      exact ⟨z, rfl⟩
    have hc₁ : (secondOrderDefectGraph G).connectedComponentMk (u₁ x) = c₁ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₁ (u₁ x)).mp hx₁
    have hc₂ : (secondOrderDefectGraph G).connectedComponentMk (u₂ z) = c₂ :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c₂ (u₂ z)).mp hz₂
    apply hcne
    rw [hxz] at hc₁
    exact hc₁.symm.trans hc₂
  exact false_of_two_disjoint_cycleCovers_same_doubleTarget
    G hfree u₁ u₂ v hv hdisjoint f₁ f₂ hadj₁ hadj₂ horient₁ horient₂

end

end Erdos85
