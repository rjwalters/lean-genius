import Proofs.Erdos85BinarySquareRegularParity

/-!
# Cross edges between defect components are triangle edges

Triangle-free neighbours of a vertex lie in its own defect component
(`triangleFreeNeighbors_subset_componentNeighborFinset`).  Hence every ambient
edge joining two different defect components lies in a (unique) triangle.

Consequences for an exterior vertex `u` of a component `c` with `c`-neighbours
`z ≠ z'`:

* **rook property**: two distinct neighbours of any vertex `m` never share a
  `c`-neighbour (they would have two common neighbours);
* if `z ~ z'` then no exterior neighbour of `u` is adjacent to `z` or `z'`
  (the triangle `u z z'` already uses both cross edges);
* if `z ≁ z'` then `u` has exactly one exterior neighbour adjacent to `z`
  and exactly one adjacent to `z'`.

So an exterior vertex is triangle-matched at both of its `c`-neighbours or at
neither, and the second case happens exactly when its selected pair is an
internal ambient edge.  Everything is uniform in `q` and needs no eigenline.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every ambient edge between two different defect components lies in a
triangle. -/
theorem exists_common_neighbor_of_adj_of_component_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    {u z : V} (huz : G.Adj u z)
    (hne : (secondOrderDefectGraph G).connectedComponentMk u ≠
      (secondOrderDefectGraph G).connectedComponentMk z) :
    ∃ y, G.Adj u y ∧ G.Adj z y := by
  by_contra hno
  push Not at hno
  -- then `z` is a triangle-free neighbour of `u`, hence in `u`'s component
  have hz : z ∈ triangleFreeNeighbors G u := by
    rw [mem_triangleFreeNeighbors]
    refine ⟨huz, ?_⟩
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro y hy
    rw [Finset.mem_inter, mem_neighborFinset, mem_neighborFinset] at hy
    exact hno y hy.1 hy.2
  have hsub := triangleFreeNeighbors_subset_componentNeighborFinset G
    ((secondOrderDefectGraph G).connectedComponentMk u) (x := u)
    ((ConnectedComponent.mem_supp_iff _ u).mpr rfl)
  have := hsub hz
  rw [componentNeighborFinset, Finset.mem_filter] at this
  exact hne this.2.symm

/-- **Rook property.**  Two distinct neighbours of `m` have no common neighbour
other than `m` (`C₄`-freeness). -/
theorem not_adj_both_of_adj_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hfree : ¬ containsC4 V G)
    {m y₁ y₂ z : V} (hy₁ : G.Adj m y₁) (hy₂ : G.Adj m y₂) (hne : y₁ ≠ y₂)
    (hz : z ≠ m) : ¬ (G.Adj z y₁ ∧ G.Adj z y₂) := by
  rintro ⟨hz₁, hz₂⟩
  have hle := common_le_one_of_not_containsC4 hfree m z hz.symm
  have h2 : 1 < (G.neighborFinset m ∩ G.neighborFinset z).card := by
    apply Finset.one_lt_card.mpr
    refine ⟨y₁, ?_, y₂, ?_, hne⟩ <;> simp [mem_neighborFinset, *]
  omega

/-- The unique triangle partner of a cross edge `u ~ z` (`u`, `z` in different
defect components), together with its uniqueness. -/
theorem existsUnique_common_neighbor_of_adj_of_component_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {u z : V} (huz : G.Adj u z)
    (hne : (secondOrderDefectGraph G).connectedComponentMk u ≠
      (secondOrderDefectGraph G).connectedComponentMk z) :
    ∃! y, G.Adj u y ∧ G.Adj z y := by
  obtain ⟨y, hy⟩ := exists_common_neighbor_of_adj_of_component_ne G huz hne
  refine ⟨y, hy, ?_⟩
  intro y' hy'
  by_contra hyy'
  exact not_adj_both_of_adj_of_ne G hfree hy'.1 hy.1 hyy' (G.ne_of_adj huz).symm ⟨hy'.2, hy.2⟩

/-- **Exterior triangle dichotomy.**  Let `u` be an exterior vertex of the
defect component `c` whose neighbours in `c` are exactly `z ≠ z'`.  If
`z ~ z'` then no exterior neighbour of `u` is adjacent to `z` or `z'`; if
`z ≁ z'` then `u` has exactly one exterior neighbour adjacent to `z` and
exactly one adjacent to `z'`. -/
theorem exterior_triangle_dichotomy
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {u z z' : V} (hu : u ∉ c.supp) (hz : z ∈ c.supp) (hz' : z' ∈ c.supp)
    (hzz' : z ≠ z') (huz : G.Adj u z) (huz' : G.Adj u z')
    (hpair : ∀ y, G.Adj u y → y ∈ c.supp → y = z ∨ y = z') :
    (G.Adj z z' → ∀ y, G.Adj u y → y ∉ c.supp → ¬ G.Adj z y ∧ ¬ G.Adj z' y) ∧
    (¬ G.Adj z z' →
      (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z y) ∧
      (∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj z' y)) := by
  have hmem : ∀ x, x ∈ c.supp ↔ (secondOrderDefectGraph G).connectedComponentMk x = c :=
    fun x => ConnectedComponent.mem_supp_iff c x
  have hneu : ∀ x, x ∈ c.supp → (secondOrderDefectGraph G).connectedComponentMk u ≠
      (secondOrderDefectGraph G).connectedComponentMk x := by
    intro x hx h
    exact hu ((hmem u).mpr (h.trans ((hmem x).mp hx)))
  constructor
  · -- `z ~ z'`: the triangle `u z z'` is the unique triangle on `u z` and on `u z'`
    intro hadj y huy hyc
    constructor
    · intro hzy
      -- `z'` and `y` are both common neighbours of `u` and `z`
      have hyz' : y ≠ z' := fun h => hyc (h ▸ hz')
      exact not_adj_both_of_adj_of_ne G hfree huy huz' hyz' (G.ne_of_adj huz).symm ⟨hzy, hadj⟩
    · intro hz'y
      have hyz : y ≠ z := fun h => hyc (h ▸ hz)
      exact not_adj_both_of_adj_of_ne G hfree huy huz hyz (G.ne_of_adj huz').symm ⟨hz'y, hadj.symm⟩
  · intro hnadj
    -- generic: the unique triangle partner of `u ~ w` (`w ∈ {z, z'}`) is exterior
    have key : ∀ w w', w ∈ c.supp → w' ∈ c.supp → w ≠ w' → G.Adj u w → G.Adj u w' →
        ¬ G.Adj w w' → (∀ y, G.Adj u y → y ∈ c.supp → y = w ∨ y = w') →
        ∃! y, G.Adj u y ∧ y ∉ c.supp ∧ G.Adj w y := by
      intro w w' hw hw' hww' huw huw' hnww' hpair'
      obtain ⟨y, ⟨huy, hwy⟩, huniq⟩ :=
        existsUnique_common_neighbor_of_adj_of_component_ne G hfree huw (hneu w hw)
      have hyc : y ∉ c.supp := by
        intro hyc
        rcases hpair' y huy hyc with rfl | rfl
        · exact G.irrefl hwy
        · exact hnww' hwy
      refine ⟨y, ⟨huy, hyc, hwy⟩, ?_⟩
      intro y' hy'
      exact huniq y' ⟨hy'.1, hy'.2.2⟩
    refine ⟨key z z' hz hz' hzz' huz huz' hnadj hpair, ?_⟩
    exact key z' z hz' hz hzz'.symm huz' huz (fun h => hnadj h.symm)
      (fun y hy hyc => (hpair y hy hyc).symm)

end

end Erdos85
