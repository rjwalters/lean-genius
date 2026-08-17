import Proofs.Erdos85BinarySquareThreeSelectorCubeLines
import Proofs.Erdos85BinarySquareSizeTwoCrossIndexedBlocks

/-!
# Four-coordinate selector hypercubes

Fixing points in two distinct component coordinates determines a unique
ambient label.  In two further normalized size-two coordinates, the remaining
fiber is therefore exactly a Cartesian `2 × 2` rectangle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Support of the four-coordinate selector hypercubes. -/
def fourSelectorHyperCubeSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent) :
    Set (c.supp × (d.supp × (e.supp × f.supp))) :=
  {p | ∃ x : V,
    p.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x ∧
    p.2.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) d x ∧
    p.2.2.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) e x ∧
    p.2.2.2.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) f x}

/-- **CUBE-PLANE/4.**  After fixing points in two distinct coordinates, the
four-selector support in two further size-two coordinates is exactly a
Cartesian product of two two-point sets. -/
theorem binarySquare_regular_fourSelectorHyperCubeSupport_twoFiber_exact_rectangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d)
    (he : e.supp.ncard = q * 2) (hf : f.supp.ncard = q * 2)
    (a : c.supp) (b : d.supp) :
    ∃ u₀ u₁ : e.supp, u₀ ≠ u₁ ∧
      ∃ v₀ v₁ : f.supp, v₀ ≠ v₁ ∧
        ∀ z : e.supp, ∀ w : f.supp,
          (a, (b, (z, w))) ∈ fourSelectorHyperCubeSupport G c d e f ↔
            (z = u₀ ∨ z = u₁) ∧ (w = v₀ ∨ w = v₁) := by
  let D := secondOrderDefectGraph G
  obtain ⟨x, hx, hxUnique⟩ :=
    existsUnique_mem_cross_componentNeighborFinsets G hfree c d hcd a b
  have heCard : (componentNeighborFinset G D e x).card = 2 :=
    binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard e he x
  have hfCard : (componentNeighborFinset G D f x).card = 2 :=
    binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard f hf x
  obtain ⟨u, u', huu', huPair⟩ := Finset.card_eq_two.mp heCard
  obtain ⟨v, v', hvv', hvPair⟩ := Finset.card_eq_two.mp hfCard
  have huMem : u ∈ componentNeighborFinset G D e x := by
    rw [huPair]
    simp [huu']
  have hu'Mem : u' ∈ componentNeighborFinset G D e x := by
    rw [huPair]
    simp
  have hvMem : v ∈ componentNeighborFinset G D f x := by
    rw [hvPair]
    simp [hvv']
  have hv'Mem : v' ∈ componentNeighborFinset G D f x := by
    rw [hvPair]
    simp
  have huSupp : u ∈ e.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff e u).mpr
      (Finset.mem_filter.mp huMem).2
  have hu'Supp : u' ∈ e.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff e u').mpr
      (Finset.mem_filter.mp hu'Mem).2
  have hvSupp : v ∈ f.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff f v).mpr
      (Finset.mem_filter.mp hvMem).2
  have hv'Supp : v' ∈ f.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff f v').mpr
      (Finset.mem_filter.mp hv'Mem).2
  let u₀ : e.supp := ⟨u, huSupp⟩
  let u₁ : e.supp := ⟨u', hu'Supp⟩
  let v₀ : f.supp := ⟨v, hvSupp⟩
  let v₁ : f.supp := ⟨v', hv'Supp⟩
  have huNe : u₀ ≠ u₁ := fun h => huu' (congrArg Subtype.val h)
  have hvNe : v₀ ≠ v₁ := fun h => hvv' (congrArg Subtype.val h)
  refine ⟨u₀, u₁, huNe, v₀, v₁, hvNe, ?_⟩
  intro z w
  constructor
  · rintro ⟨y, hya, hyb, hyz, hyw⟩
    have hyx : y = x := hxUnique y ⟨hya, hyb⟩
    subst y
    rw [huPair] at hyz
    rw [hvPair] at hyw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyz hyw
    constructor
    · rcases hyz with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
    · rcases hyw with h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Subtype.ext h)
  · rintro ⟨hz, hw⟩
    refine ⟨x, hx.1, hx.2, ?_, ?_⟩
    · rw [huPair]
      rcases hz with rfl | rfl
      · simp [u₀]
      · simp [u₁]
    · rw [hvPair]
      rcases hw with rfl | rfl
      · simp [v₀]
      · simp [v₁]

/-- For an internal label, the self-coordinate selector in the four-cube is
exactly its induced ambient-graph neighborhood. -/
theorem fourSelectorHyperCube_selfCoordinate_iff_induced_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent) (x y : c.supp) :
    y.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x.1 ↔
      (G.induce c.supp).Adj x y :=
  mem_componentNeighborFinset_internal_iff_induced_adj G c x y

end

end Erdos85
