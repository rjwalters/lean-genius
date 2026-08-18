import Proofs.Erdos85OrderSixtyFourTwoComponentEqualRootFork

/-! # Exact residual centers after a two-center routing fragment

The two-center density terminal leaves a completely canonical residual: remove
the two displayed centers from the root's owner-center row, then take the
disjoint union of the target stars of all remaining centers.  This is useful
in the `[5,3]` and `[4,4]` strata, where the residual has respectively three
or two centers rather than an unstructured set of target vertices.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Owner-level density enriched with its exact residual-center
decomposition. -/
def HasTwoCenterRoutingRowDensityWithResidualCentersForOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (owner : (secondOrderDefectGraph G).ConnectedComponent) : Prop :=
  ∃ (source target : (secondOrderDefectGraph G).ConnectedComponent)
      (hst : source ≠ target) (x : source.supp) (u₁ u₂ : owner.supp),
    u₁ ≠ u₂ ∧ G.Adj x.1 u₁.1 ∧ G.Adj x.1 u₂.1 ∧
      let C := componentCrossNeighborFinset G owner x
      let S₁ := componentCrossNeighborFinset G target u₁
      let S₂ := componentCrossNeighborFinset G target u₂
      let R := (Finset.univ : Finset target.supp).filter fun y =>
        owner = crossIntermediateComponent G hfree hst x y
      (C \ {u₁, u₂}).card = m owner - 2 ∧
        R \ (S₁ ∪ S₂) =
          (C \ {u₁, u₂}).biUnion fun u =>
            componentCrossNeighborFinset G target u

/-- **Exact residual-center decomposition, q-generic.**  Every two-center
routing density fragment leaves exactly `m owner - 2` unused centers, and
the unused part of the routing row is precisely the union of their target
stars. -/
theorem twoCenterRoutingRowDensityForOwner_has_residualCenterDecomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (owner : (secondOrderDefectGraph G).ConnectedComponent)
    (h : HasTwoCenterRoutingRowDensityForOwner G hfree m owner) :
    HasTwoCenterRoutingRowDensityWithResidualCentersForOwner
      G hfree m owner := by
  classical
  rcases h with ⟨source, target, hst, x, u₁, u₂, hne, hx₁, hx₂,
    _hdis, _hunionCard, _hsub, _hrowCard⟩
  let C := componentCrossNeighborFinset G owner x
  let S₁ := componentCrossNeighborFinset G target u₁
  let S₂ := componentCrossNeighborFinset G target u₂
  let R := (Finset.univ : Finset target.supp).filter fun y =>
    owner = crossIntermediateComponent G hfree hst x y
  have hu₁C : u₁ ∈ C := by
    change u₁ ∈ componentCrossNeighborFinset G owner x
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx₁⟩
  have hu₂C : u₂ ∈ C := by
    change u₂ ∈ componentCrossNeighborFinset G owner x
    rw [componentCrossNeighborFinset, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hx₂⟩
  have hpairSub : ({u₁, u₂} : Finset owner.supp) ⊆ C := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hu₁C
    · exact hu₂C
  have hCcard : C.card = m owner := by
    change (componentCrossNeighborFinset G owner x).card = m owner
    rw [card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard source owner (x := x.1) x.2
    rw [hm owner] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have hresCard : (C \ {u₁, u₂}).card = m owner - 2 := by
    rw [Finset.card_sdiff_of_subset hpairSub, hCcard]
    simp [hne]
  have hdecomp : R = C.biUnion fun u =>
      componentCrossNeighborFinset G target u := by
    exact routingRow_eq_biUnion_componentCrossNeighborFinset
      G hfree hst owner x
  have hresidual :
      R \ (S₁ ∪ S₂) =
        (C \ {u₁, u₂}).biUnion fun u =>
          componentCrossNeighborFinset G target u := by
    ext y
    constructor
    · intro hy
      have hyR := (Finset.mem_sdiff.mp hy).1
      have hynot := (Finset.mem_sdiff.mp hy).2
      rw [hdecomp] at hyR
      obtain ⟨u, huC, huy⟩ := Finset.mem_biUnion.mp hyR
      have hupair : u ∉ ({u₁, u₂} : Finset owner.supp) := by
        intro hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl
        · exact hynot (Finset.mem_union_left _ huy)
        · exact hynot (Finset.mem_union_right _ huy)
      exact Finset.mem_biUnion.mpr
        ⟨u, Finset.mem_sdiff.mpr ⟨huC, hupair⟩, huy⟩
    · intro hy
      obtain ⟨u, husdiff, huy⟩ := Finset.mem_biUnion.mp hy
      have huC := (Finset.mem_sdiff.mp husdiff).1
      have hupair := (Finset.mem_sdiff.mp husdiff).2
      have hune₁ : u ≠ u₁ := by
        intro hu
        apply hupair
        simp [hu]
      have hune₂ : u ≠ u₂ := by
        intro hu
        apply hupair
        simp [hu]
      apply Finset.mem_sdiff.mpr
      constructor
      · rw [hdecomp]
        exact Finset.mem_biUnion.mpr ⟨u, huC, huy⟩
      · intro hyunion
        rcases Finset.mem_union.mp hyunion with hy₁ | hy₂
        · have hd := routingRow_starRows_pairwise_disjoint
            G hfree hst x huC hu₁C hune₁
          exact Finset.disjoint_left.mp hd huy hy₁
        · have hd := routingRow_starRows_pairwise_disjoint
            G hfree hst x huC hu₂C hune₂
          exact Finset.disjoint_left.mp hd huy hy₂
  exact ⟨source, target, hst, x, u₁, u₂, hne, hx₁, hx₂,
    hresCard, hresidual⟩

/-- The `[5,3]` pressure terminal reaches an exact residual-center
decomposition for one owner: the residual has one center count determined by
`m a = 3` or `m b = 5` (hence respectively one or three centers). -/
theorem orderSixtyFour_threeFive_twoOwner_exists_residualCenterDecomposition
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 3) (hmb : m b = 5)
    (hcross : 6816 ≤
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)).card) :
    HasTwoCenterRoutingRowDensityWithResidualCentersForOwner G hfree m a ∨
      HasTwoCenterRoutingRowDensityWithResidualCentersForOwner G hfree m b := by
  rcases orderSixtyFour_threeFive_twoOwner_exists_ownerDensity
    G hfree hreg hcount m hm a b hab hma hmb hcross with ha | hb
  · exact Or.inl
      (twoCenterRoutingRowDensityForOwner_has_residualCenterDecomposition
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a ha)
  · exact Or.inr
      (twoCenterRoutingRowDensityForOwner_has_residualCenterDecomposition
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b hb)

/-- The `[4,4]` pressure terminal reaches the same exact package; in either
owner orientation exactly two residual centers remain. -/
theorem orderSixtyFour_fourFour_twoOwner_exists_residualCenterDecomposition
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = 8 * m d)
    (a b : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 4) (hmb : m b = 4)
    (hcross : 12288 ≤
      (crossComponentCyclicColoredTriples (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)).card) :
    HasTwoCenterRoutingRowDensityWithResidualCentersForOwner G hfree m a ∨
      HasTwoCenterRoutingRowDensityWithResidualCentersForOwner G hfree m b := by
  rcases orderSixtyFour_fourFour_twoOwner_exists_ownerDensity
    G hfree hreg hcount m hm a b hab hma hmb hcross with ha | hb
  · exact Or.inl
      (twoCenterRoutingRowDensityForOwner_has_residualCenterDecomposition
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm a ha)
  · exact Or.inr
      (twoCenterRoutingRowDensityForOwner_has_residualCenterDecomposition
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm b hb)

end

end Erdos85

#print axioms Erdos85.twoCenterRoutingRowDensityForOwner_has_residualCenterDecomposition
#print axioms Erdos85.orderSixtyFour_threeFive_twoOwner_exists_residualCenterDecomposition
#print axioms Erdos85.orderSixtyFour_fourFour_twoOwner_exists_residualCenterDecomposition
