import Proofs.Erdos85BinarySquareCrossSelectorUnique
import Proofs.Erdos85BinarySquareSizeTwoStarPerfectMatching

/-! # Three-coordinate selector cubes have two points on every line -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The Cartesian `2 × 2 × 2` selector cube carried by one ambient label. -/
def threeSelectorCube
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e : (secondOrderDefectGraph G).ConnectedComponent) (x : V) :
    Set (c.supp × d.supp × e.supp) :=
  {p |
    p.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x ∧
    p.2.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) d x ∧
    p.2.2.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) e x}

/-- The support of the three-coordinate selector cubes.  A triple of component
points is present when one ambient label selects all three of them. -/
def threeSelectorCubeSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c d e : (secondOrderDefectGraph G).ConnectedComponent) :
    Set (c.supp × d.supp × e.supp) :=
  {p | ∃ x : V,
    p.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) c x ∧
    p.2.1.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) d x ∧
    p.2.2.1 ∈ componentNeighborFinset G (secondOrderDefectGraph G) e x}

/-- Distinct ambient labels carry disjoint selector cubes as soon as two of
the coordinates are distinct.  A common triple would give the same two
cross-coordinate points to both labels, contradicting unique incidence. -/
theorem threeSelectorCubes_pairwise_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    {x y : V} (hxy : x ≠ y) :
    Disjoint (threeSelectorCube G c d e x) (threeSelectorCube G c d e y) := by
  rw [Set.disjoint_left]
  intro p hpx hpy
  have hpx' := hpx
  have hpy' := hpy
  simp only [threeSelectorCube, Set.mem_setOf_eq] at hpx' hpy'
  obtain ⟨z, hz, hzUnique⟩ :=
    existsUnique_mem_cross_componentNeighborFinsets
      G hfree c d hcd p.1 p.2.1
  have hxz : x = z := hzUnique x ⟨hpx'.1, hpx'.2.1⟩
  have hyz : y = z := hzUnique y ⟨hpy'.1, hpy'.2.1⟩
  exact hxy (hxz.trans hyz.symm)

/-- Fixing points in two distinct coordinates selects a unique ambient cube;
if the third coordinate has normalized size two, the resulting axis-parallel
line meets the cube support in exactly its two selector endpoints. -/
theorem binarySquare_regular_threeSelectorCubeSupport_axisLine_exactlyTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (he : e.supp.ncard = q * 2) (a : c.supp) (b : d.supp) :
    ∃ u v : e.supp, u ≠ v ∧
      ∀ z : e.supp,
        (a, b, z) ∈ threeSelectorCubeSupport G c d e ↔ z = u ∨ z = v := by
  let D := secondOrderDefectGraph G
  obtain ⟨x, hx, hxUnique⟩ :=
    existsUnique_mem_cross_componentNeighborFinsets G hfree c d hcd a b
  have htwo : (componentNeighborFinset G D e x).card = 2 :=
    binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard e he x
  obtain ⟨r, s, hrs, hpair⟩ := Finset.card_eq_two.mp htwo
  have hrMem : r ∈ componentNeighborFinset G D e x := by
    rw [hpair]
    simp [hrs]
  have hsMem : s ∈ componentNeighborFinset G D e x := by
    rw [hpair]
    simp
  have hrSupp : r ∈ e.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff e r).mpr
      (Finset.mem_filter.mp hrMem).2
  have hsSupp : s ∈ e.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff e s).mpr
      (Finset.mem_filter.mp hsMem).2
  let u : e.supp := ⟨r, hrSupp⟩
  let v : e.supp := ⟨s, hsSupp⟩
  have huv : u ≠ v := by
    intro huv
    exact hrs (congrArg Subtype.val huv)
  refine ⟨u, v, huv, ?_⟩
  intro z
  constructor
  · rintro ⟨y, hya, hyb, hyz⟩
    have hyx : y = x := hxUnique y ⟨hya, hyb⟩
    subst y
    rw [hpair] at hyz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hyz
    rcases hyz with hzu | hzv
    · exact Or.inl (Subtype.ext hzu)
    · exact Or.inr (Subtype.ext hzv)
  · intro hz
    refine ⟨x, hx.1, hx.2, ?_⟩
    rcases hz with rfl | rfl
    · exact hrMem
    · exact hsMem

/-- For three pairwise distinct normalized size-two coordinates, every line
parallel to any of the three axes meets the selector-cube support in exactly
two points. -/
theorem binarySquare_regular_threeSizeTwoParts_cubeSupport_allAxisLines_exactlyTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (hc : c.supp.ncard = q * 2) (hd : d.supp.ncard = q * 2)
    (he : e.supp.ncard = q * 2) :
    (∀ a : c.supp, ∀ b : d.supp, ∃ u v : e.supp, u ≠ v ∧
      ∀ z : e.supp,
        (a, b, z) ∈ threeSelectorCubeSupport G c d e ↔ z = u ∨ z = v) ∧
    (∀ a : c.supp, ∀ z : e.supp, ∃ u v : d.supp, u ≠ v ∧
      ∀ b : d.supp,
        (a, b, z) ∈ threeSelectorCubeSupport G c d e ↔ b = u ∨ b = v) ∧
    (∀ b : d.supp, ∀ z : e.supp, ∃ u v : c.supp, u ≠ v ∧
      ∀ a : c.supp,
        (a, b, z) ∈ threeSelectorCubeSupport G c d e ↔ a = u ∨ a = v) := by
  constructor
  · intro a b
    exact binarySquare_regular_threeSelectorCubeSupport_axisLine_exactlyTwo
      G hfree hq hreg hcard c d e hcd he a b
  constructor
  · intro a z
    obtain ⟨u, v, huv, hline⟩ :=
      binarySquare_regular_threeSelectorCubeSupport_axisLine_exactlyTwo
        G hfree hq hreg hcard c e d hce hd a z
    refine ⟨u, v, huv, ?_⟩
    intro b
    have hperm :
        (a, b, z) ∈ threeSelectorCubeSupport G c d e ↔
          (a, z, b) ∈ threeSelectorCubeSupport G c e d := by
      simp only [threeSelectorCubeSupport, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hxa, hxb, hxz⟩
        exact ⟨x, hxa, hxz, hxb⟩
      · rintro ⟨x, hxa, hxz, hxb⟩
        exact ⟨x, hxa, hxb, hxz⟩
    exact hperm.trans (hline b)
  · intro b z
    obtain ⟨u, v, huv, hline⟩ :=
      binarySquare_regular_threeSelectorCubeSupport_axisLine_exactlyTwo
        G hfree hq hreg hcard d e c hde hc b z
    refine ⟨u, v, huv, ?_⟩
    intro a
    have hperm :
        (a, b, z) ∈ threeSelectorCubeSupport G c d e ↔
          (b, z, a) ∈ threeSelectorCubeSupport G d e c := by
      simp only [threeSelectorCubeSupport, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hxa, hxb, hxz⟩
        exact ⟨x, hxb, hxz, hxa⟩
      · rintro ⟨x, hxb, hxz, hxa⟩
        exact ⟨x, hxa, hxb, hxz⟩
    exact hperm.trans (hline a)

end

end Erdos85

