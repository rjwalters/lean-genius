import Proofs.Erdos85OrderSixtyFourOutsideFeasibility

/-! # Outside vertices as edges of the exterior-pair graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Regard the neighbors of `x` in `c` as vertices of the subtype `c.supp`. -/
def componentNeighborSubtypeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (x : V) : Finset c.supp := by
  exact (componentNeighborFinset G D c x).subtype fun y => y ∈ c.supp

@[simp] theorem componentNeighborSubtypeFinset_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)] (x : V) :
    (componentNeighborSubtypeFinset G D c x).card =
      (componentNeighborFinset G D c x).card := by
  classical
  rw [componentNeighborSubtypeFinset, Finset.card_subtype,
    Finset.filter_eq_self.2]
  intro y hy
  exact (ConnectedComponent.mem_supp_iff c y).mpr
    (Finset.mem_filter.mp hy).2

/-- The unordered pair canonically represented by a two-element finset. -/
noncomputable def sym2OfFinsetCardTwo
    {α : Type*} [DecidableEq α] (S : Finset α) (hS : S.card = 2) : Sym2 α :=
  s(Classical.choose (Finset.card_eq_two.mp hS),
    Classical.choose (Classical.choose_spec (Finset.card_eq_two.mp hS)))

@[simp] theorem sym2OfFinsetCardTwo_toFinset
    {α : Type*} [DecidableEq α] (S : Finset α) (hS : S.card = 2) :
    (sym2OfFinsetCardTwo S hS).toFinset = S := by
  classical
  let h := Finset.card_eq_two.mp hS
  let x := Classical.choose h
  let hx := Classical.choose_spec h
  let y := Classical.choose hx
  have hSxy : S = {x, y} := (Classical.choose_spec hx).2
  rw [sym2OfFinsetCardTwo, Sym2.toFinset_mk_eq]
  exact hSxy.symm

/-- The two neighbors in `c` selected by an outside vertex, as an unordered pair. -/
noncomputable def outsidePair
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2)
    (z : {x : V // x ∉ c.supp}) : Sym2 c.supp :=
  sym2OfFinsetCardTwo (componentNeighborSubtypeFinset G D c z.1) (by
    simpa using hcard z.1)

@[simp] theorem outsidePair_toFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2)
    (z : {x : V // x ∉ c.supp}) :
    (outsidePair G D c hcard z).toFinset =
      componentNeighborSubtypeFinset G D c z.1 := by
  simp [outsidePair]

/-- Endpoint membership in the owned pair is exactly ambient adjacency to
the outside owner.  This is the incidence-matrix bridge used by the CNF
label transport. -/
theorem mem_outsidePair_toFinset_iff_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2)
    (z : {x : V // x ∉ c.supp}) (u : c.supp) :
    u ∈ (outsidePair G D c hcard z).toFinset ↔ G.Adj u.1 z.1 := by
  rw [outsidePair_toFinset, componentNeighborSubtypeFinset,
    Finset.mem_subtype]
  constructor
  · intro hu
    exact ((G.mem_neighborFinset z.1 u.1).mp
      (Finset.mem_filter.mp hu).1).symm
  · intro huz
    apply Finset.mem_filter.mpr
    exact ⟨(G.mem_neighborFinset z.1 u.1).mpr huz.symm,
      (ConnectedComponent.mem_supp_iff c u.1).mp u.2⟩

theorem outsidePair_mem_exteriorPairGraph_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2)
    (z : {x : V // x ∉ c.supp}) :
    outsidePair G D c hcard z ∈ (exteriorPairGraph G c).edgeFinset := by
  generalize he : outsidePair G D c hcard z = e
  rw [SimpleGraph.mem_edgeFinset]
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet]
      constructor
      · intro huv
        subst v
        have hpair := outsidePair_toFinset G D c hcard z
        rw [he] at hpair
        have htwo : (componentNeighborSubtypeFinset G D c z.1).card = 2 := by
          simpa using hcard z.1
        rw [← hpair] at htwo
        simp [Sym2.toFinset_mk_eq] at htwo
      · refine ⟨z.1, z.2, ?_, ?_⟩
        · have huSub : u ∈ componentNeighborSubtypeFinset G D c z.1 := by
            rw [← outsidePair_toFinset G D c hcard z, he]
            simp [Sym2.toFinset_mk_eq]
          have hu := Finset.mem_subtype.mp huSub
          exact ((G.mem_neighborFinset z.1 u.1).mp
            (Finset.mem_filter.mp hu).1).symm
        · have hvSub : v ∈ componentNeighborSubtypeFinset G D c z.1 := by
            rw [← outsidePair_toFinset G D c hcard z, he]
            simp [Sym2.toFinset_mk_eq]
          have hv := Finset.mem_subtype.mp hvSub
          exact ((G.mem_neighborFinset z.1 v.1).mp
            (Finset.mem_filter.mp hv).1).symm

/-- The edge of the exterior-pair graph owned by an outside vertex. -/
noncomputable def outsidePairEdge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2) :
    {x : V // x ∉ c.supp} → (exteriorPairGraph G c).edgeFinset :=
  fun z => ⟨outsidePair G D c hcard z,
    outsidePair_mem_exteriorPairGraph_edgeFinset G D c hcard z⟩

theorem outsidePairEdge_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2)
    (hinc : Function.Injective (componentNeighborFinset G D c)) :
    Function.Injective (outsidePairEdge G D c hcard) := by
  intro z w hzw
  have hpairs : outsidePair G D c hcard z = outsidePair G D c hcard w :=
    congrArg Subtype.val hzw
  have hsub : componentNeighborSubtypeFinset G D c z.1 =
      componentNeighborSubtypeFinset G D c w.1 := by
    rw [← outsidePair_toFinset G D c hcard z,
      ← outsidePair_toFinset G D c hcard w, hpairs]
  have horig : componentNeighborFinset G D c z.1 =
      componentNeighborFinset G D c w.1 := by
    ext y
    constructor
    · intro hy
      have hysupp : y ∈ c.supp :=
        (ConnectedComponent.mem_supp_iff c y).mpr (Finset.mem_filter.mp hy).2
      have hySub : (⟨y, hysupp⟩ : c.supp) ∈
          componentNeighborSubtypeFinset G D c z.1 :=
        Finset.mem_subtype.mpr hy
      rw [hsub] at hySub
      exact Finset.mem_subtype.mp hySub
    · intro hy
      have hysupp : y ∈ c.supp :=
        (ConnectedComponent.mem_supp_iff c y).mpr (Finset.mem_filter.mp hy).2
      have hySub : (⟨y, hysupp⟩ : c.supp) ∈
          componentNeighborSubtypeFinset G D c w.1 :=
        Finset.mem_subtype.mpr hy
      rw [← hsub] at hySub
      exact Finset.mem_subtype.mp hySub
  exact Subtype.ext (hinc horig)

/-- Equal cardinalities promote the canonical outside-to-edge injection to an equivalence. -/
noncomputable def outsidePairEdgeEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2)
    (hinc : Function.Injective (componentNeighborFinset G D c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48) :
    {x : V // x ∉ c.supp} ≃ (exteriorPairGraph G c).edgeFinset :=
  Equiv.ofBijective (outsidePairEdge G D c hcard)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      outsidePairEdge_injective G D c hcard hinc, by
        rw [hqcard, Fintype.card_coe]
        exact hRedges.symm⟩)

@[simp] theorem outsidePairEdgeEquiv_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V, (componentNeighborFinset G D c x).card = 2)
    (hinc : Function.Injective (componentNeighborFinset G D c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (z : {x : V // x ∉ c.supp}) :
    outsidePairEdgeEquiv G D c hcard hinc hqcard hRedges z =
      outsidePairEdge G D c hcard z := rfl

/-- In the seven-component order-64 branch, outside vertices are canonically
the 48 edges of the exterior-pair graph on the unique 16-vertex component. -/
theorem orderSixtyFour_seven_components_outside_equiv_exteriorPair_edges
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v → G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      Nonempty ({x : Fin 64 // x ∉ c.supp} ≃
        (exteriorPairGraph G c.supp).edgeFinset) := by
  classical
  obtain ⟨c, hc16, _outsideLabel, hqcard, hcard, hinc, _hpairImage,
      _hRreg, hRedges, _hout, _hC4free, _hcross⟩ :=
    orderSixtyFour_seven_components_outside_feasibility
      G hfree hmin hcover hcount
  exact ⟨c, hc16, ⟨outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
    hcard hinc hqcard hRedges⟩⟩

end

end Erdos85
