import Proofs.Erdos85BinarySquareSizeTwoCrossOwnerComponentEquiv

/-! # Exact size correspondence for cross and owner components -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Membership on the source side is preserved and reflected by the
owner-to-cross component map. -/
theorem restrictedOwnerComponentToCross_inl_mem_supp_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (a : (restrictedComponentOwnerGraph G source target).ConnectedComponent)
    (y : source.supp) :
    Sum.inl y ∈ (restrictedOwnerComponentToCross G hfree source target a).supp ↔
      y ∈ a.supp := by
  refine ConnectedComponent.ind ?_ a
  intro x
  simp only [restrictedOwnerComponentToCross_mk,
    ConnectedComponent.mem_supp_iff]
  exact (restrictedOwner_connectedComponentMk_eq_iff_cross_inl
    G hfree source target y x).symm

/-- The source half of a mapped cross component has exactly the order of the
owner-factor component. -/
theorem restrictedOwnerComponentToCross_left_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (a : (restrictedComponentOwnerGraph G source target).ConnectedComponent) :
    (crossComponentLeftVertices G source target
      (restrictedOwnerComponentToCross G hfree source target a)).card =
        a.supp.ncard := by
  classical
  let e := restrictedOwnerComponentToCross G hfree source target a
  have hcard : a.supp.toFinset.card = a.supp.ncard :=
    (Set.ncard_eq_toFinset_card' a.supp).symm
  rw [← hcard]
  symm
  apply Finset.card_bij
    (fun y hy => (⟨Sum.inl y,
      (restrictedOwnerComponentToCross_inl_mem_supp_iff
        G hfree source target a y).mpr (Set.mem_toFinset.mp hy)⟩ : e.supp))
  · intro y hy
    simp [crossComponentLeftVertices]
  · intro y₁ h₁ y₂ h₂ heq
    have hsum : (Sum.inl y₁ : source.supp ⊕ target.supp) = Sum.inl y₂ :=
      Subtype.ext_iff.mp heq
    exact Sum.inl.inj hsum
  · intro v hv
    have hvLeft := Finset.mem_filter.mp hv |>.2
    rcases v with ⟨v, hvSupp⟩
    cases v with
    | inl y =>
      have hy : y ∈ a.supp :=
        (restrictedOwnerComponentToCross_inl_mem_supp_iff
          G hfree source target a y).mp hvSupp
      exact ⟨y, Set.mem_toFinset.mpr hy, rfl⟩
    | inr z => simp at hvLeft

/-- The left and right finsets partition the support subtype of every cross
component. -/
theorem crossComponentLeft_union_right_eq_univ
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (e : (componentCrossBipartiteGraph G source target).ConnectedComponent) :
    crossComponentLeftVertices G source target e ∪
        crossComponentRightVertices G source target e = Finset.univ := by
  classical
  ext v
  rcases v with ⟨v, hv⟩
  cases v <;> simp [crossComponentLeftVertices, crossComponentRightVertices]

/-- The two side finsets of a cross component are disjoint. -/
theorem crossComponentLeft_disjoint_right
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (e : (componentCrossBipartiteGraph G source target).ConnectedComponent) :
    Disjoint (crossComponentLeftVertices G source target e)
      (crossComponentRightVertices G source target e) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvL hvR
  rcases v with ⟨v, hv⟩
  cases v <;>
    simp [crossComponentLeftVertices, crossComponentRightVertices] at hvL hvR

/-- A cross component corresponding to an owner-factor component of order
`r` has exactly `2r` vertices. -/
theorem binarySquare_regular_twoSizeTwoParts_crossComponent_ncard_eq_two_mul_owner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2)
    (a : (restrictedComponentOwnerGraph G source target).ConnectedComponent) :
    (restrictedOwnerComponentToCross G hfree source target a).supp.ncard =
      2 * a.supp.ncard := by
  let e := restrictedOwnerComponentToCross G hfree source target a
  let L := crossComponentLeftVertices G source target e
  let R := crossComponentRightVertices G source target e
  have hbalance : L.card = R.card :=
    binarySquare_regular_twoSizeTwoParts_crossComponent_side_card_eq
      G hfree hq hreg hcard source target hsource htarget e
  have hleft : L.card = a.supp.ncard :=
    restrictedOwnerComponentToCross_left_card_eq
      G hfree source target a
  have hunion : L ∪ R = Finset.univ :=
    crossComponentLeft_union_right_eq_univ G source target e
  have hdisj : Disjoint L R :=
    crossComponentLeft_disjoint_right G source target e
  have htotal : Fintype.card e.supp = L.card + R.card := by
    rw [← Finset.card_univ, ← hunion, Finset.card_union_of_disjoint hdisj]
  have hncard : Fintype.card e.supp = e.supp.ncard := by
    simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq e.supp
  change e.supp.ncard = 2 * a.supp.ncard
  omega

end

end Erdos85
