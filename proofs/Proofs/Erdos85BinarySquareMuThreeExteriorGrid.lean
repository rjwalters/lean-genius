import Proofs.Erdos85BinarySquareSizeTwoMuThreeCollapse
import Proofs.Erdos85CrossEdgeTriangleDichotomy

/-!
# Grid structure behind the `μ = 3` exterior routing branch

The balanced-pair theorem labels every exterior vertex by one positive and one
negative component vertex.  C4-freeness makes that label injective.  The
equitable size-two law also gives six exterior neighbours in every component
row.  These are the two elementary ingredients of the `8 × 8` grid model:
48 occupied cells, six in each row and column, with a 2-regular missing-cell
graph.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In a C4-free graph, two distinct vertices cannot have the same pair of
distinct common neighbours.  This is the injectivity engine for exterior
pair labels. -/
theorem c4Free_commonNeighborPair_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {p n x y : V} (hpn : p ≠ n)
    (hpx : G.Adj p x) (hpy : G.Adj p y)
    (hnx : G.Adj n x) (hny : G.Adj n y) :
    x = y := by
  apply Finset.card_le_one.mp
    (common_le_one_of_not_containsC4 hfree p n hpn)
  · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hpx, hnx⟩
  · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hpy, hny⟩

/-- Turn the two singleton sign fibres into an explicit ordered signed pair
which exhausts the two-element fibre. -/
theorem signedPair_exists_of_filter_cards
    {V : Type*} [DecidableEq V] (T : Finset V) (s : V → ℤ)
    (hsign : ∀ x ∈ T, s x = -1 ∨ s x = 1)
    (hpos : (T.filter fun x => s x = 1).card = 1)
    (hneg : (T.filter fun x => s x = -1).card = 1) :
    ∃ z z', z ∈ T ∧ z' ∈ T ∧ z ≠ z' ∧ s z = 1 ∧ s z' = -1 ∧
      ∀ y ∈ T, y = z ∨ y = z' := by
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hpos
  obtain ⟨z', hz'⟩ := Finset.card_eq_one.mp hneg
  have hzmem : z ∈ T ∧ s z = 1 := by
    have : z ∈ T.filter fun x => s x = 1 := by simp [hz]
    exact Finset.mem_filter.mp this
  have hz'mem : z' ∈ T ∧ s z' = -1 := by
    have : z' ∈ T.filter fun x => s x = -1 := by simp [hz']
    exact Finset.mem_filter.mp this
  refine ⟨z, z', hzmem.1, hz'mem.1, ?_, hzmem.2, hz'mem.2, ?_⟩
  · intro h
    subst z'
    omega
  · intro y hy
    rcases hsign y hy with hsy | hsy
    · right
      have hymem : y ∈ T.filter fun x => s x = -1 :=
        Finset.mem_filter.mpr ⟨hy, hsy⟩
      simpa [hz'] using hymem
    · left
      have hymem : y ∈ T.filter fun x => s x = 1 :=
        Finset.mem_filter.mpr ⟨hy, hsy⟩
      simpa [hz] using hymem

/-- Graph-facing form of `signedPair_exists_of_filter_cards`: the explicit
signed neighbours exhaust the component-neighbour fibre, exactly matching the
input expected by `exterior_triangle_dichotomy`. -/
theorem componentNeighborFiber_exists_explicit_signedPair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) (x : V)
    (hsign : ∀ y, y ∈ c.supp → s y = -1 ∨ s y = 1)
    (hpos : (((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).filter
        fun y => s y = 1).card = 1)
    (hneg : (((G.neighborFinset x).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).filter
        fun y => s y = -1).card = 1) :
    ∃ z z', G.Adj x z ∧ G.Adj x z' ∧ z ∈ c.supp ∧ z' ∈ c.supp ∧
      z ≠ z' ∧ s z = 1 ∧ s z' = -1 ∧
      ∀ y, G.Adj x y → y ∈ c.supp → y = z ∨ y = z' := by
  let T := (G.neighborFinset x).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
  have hTsign : ∀ y ∈ T, s y = -1 ∨ s y = 1 := by
    intro y hy
    have hyc := (Finset.mem_filter.mp hy).2
    exact hsign y ((ConnectedComponent.mem_supp_iff c y).mpr hyc)
  obtain ⟨z, z', hzT, hz'T, hzz', hsz, hsz', hexhaust⟩ :=
    signedPair_exists_of_filter_cards T s hTsign hpos hneg
  have hzdata := Finset.mem_filter.mp hzT
  have hz'data := Finset.mem_filter.mp hz'T
  refine ⟨z, z', (G.mem_neighborFinset x z).mp hzdata.1,
    (G.mem_neighborFinset x z').mp hz'data.1,
    (ConnectedComponent.mem_supp_iff c z).mpr hzdata.2,
    (ConnectedComponent.mem_supp_iff c z').mpr hz'data.2,
    hzz', hsz, hsz', ?_⟩
  intro y hxy hyc
  apply hexhaust y
  exact Finset.mem_filter.mpr ⟨(G.mem_neighborFinset x y).mpr hxy,
    (ConnectedComponent.mem_supp_iff c y).mp hyc⟩

/-- The explicit signed-pair interface composed with the exact exterior
triangle dichotomy.  This is the graph-facing local normal form used by the
`μ = 3` grid: an occupied cell is split according to whether its signed label
is an internal ambient edge, with no stronger triangle-degree claim. -/
theorem exterior_signedPair_triangleDichotomy_of_filter_cards
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ) (u : V) (hu : u ∉ c.supp)
    (hsign : ∀ y, y ∈ c.supp → s y = -1 ∨ s y = 1)
    (hpos : (((G.neighborFinset u).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).filter
        fun y => s y = 1).card = 1)
    (hneg : (((G.neighborFinset u).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)).filter
        fun y => s y = -1).card = 1) :
    ∃ z z', G.Adj u z ∧ G.Adj u z' ∧ z ∈ c.supp ∧ z' ∈ c.supp ∧
      z ≠ z' ∧ s z = 1 ∧ s z' = -1 ∧
      (∀ y, G.Adj u y → y ∈ c.supp → y = z ∨ y = z') ∧
      (G.Adj z z' →
        ∀ y, G.Adj u y → y ∉ c.supp → ¬ G.Adj z y ∧ ¬ G.Adj z' y) ∧
      (¬ G.Adj z z' →
        (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z y) ∧
        (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z' y)) := by
  obtain ⟨z, z', huz, huz', hz, hz', hzz', hsz, hsz', hpair⟩ :=
    componentNeighborFiber_exists_explicit_signedPair G c s u hsign hpos hneg
  have hdich := exterior_triangle_dichotomy G hfree c hu hz hz' hzz' huz huz' hpair
  exact ⟨z, z', huz, huz', hz, hz', hzz', hsz, hsz', hpair, hdich.1, hdich.2⟩

/-- A normalized size-two component at square order has exactly `q-2`
ambient neighbours outside the component at every vertex.  At `q=8` these
are the six occupied cells in each sign row or column. -/
theorem binarySquare_regular_sizeTwoComponent_exteriorNeighborCard
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcardV : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (x : c.supp) :
    ((G.neighborFinset x.1).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y ≠ c)).card =
        q - 2 := by
  let T := (G.neighborFinset x.1).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
  let U := (G.neighborFinset x.1).filter
    (fun y => (secondOrderDefectGraph G).connectedComponentMk y ≠ c)
  have hT : T.card = 2 := by
    have h := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcardV c c (x := x.1) x.2
    rw [hc] at h
    change q * T.card = q * 2 at h
    exact Nat.eq_of_mul_eq_mul_left (by omega) h
  have hsplit : T.card + U.card = (G.neighborFinset x.1).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := G.neighborFinset x.1)
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c)
    simpa [T, U] using h
  change U.card = q - 2
  rw [G.card_neighborFinset_eq_degree, hreg x.1, hT] at hsplit
  omega

/-- Order-64 specialization: every row and every column of the exterior sign
grid contains exactly six occupied cells. -/
theorem orderSixtyFour_sizeTwoComponent_exteriorNeighborCard_six
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcardV : Fintype.card V = 8 * 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 8 * 2) (x : c.supp) :
    ((G.neighborFinset x.1).filter
      (fun y => (secondOrderDefectGraph G).connectedComponentMk y ≠ c)).card = 6 := by
  simpa using binarySquare_regular_sizeTwoComponent_exteriorNeighborCard
    G hfree (q := 8) (by norm_num) hreg hcardV c hc x

end

end Erdos85

#print axioms Erdos85.c4Free_commonNeighborPair_injective
#print axioms Erdos85.signedPair_exists_of_filter_cards
#print axioms Erdos85.componentNeighborFiber_exists_explicit_signedPair
#print axioms Erdos85.exterior_signedPair_triangleDichotomy_of_filter_cards
#print axioms Erdos85.binarySquare_regular_sizeTwoComponent_exteriorNeighborCard
#print axioms Erdos85.orderSixtyFour_sizeTwoComponent_exteriorNeighborCard_six
