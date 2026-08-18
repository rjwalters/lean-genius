import Proofs.Erdos85BinarySquareTwoOwnerRepeatedClosing
import Proofs.Erdos85OrderSixtyFourThreeComponentForkAdapter
import Proofs.Erdos85BinarySquareSameOwnerCenterGridCapacity
import Proofs.Erdos85BinarySquareSeparatedForkRowDensity

/-! # A component-block repeated closing in the `[6,2]` stratum -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Cyclic rotation preserves the global colored-triple census. -/
theorem card_cyclicColoredTriples_rotate
    {V : Type*} [Fintype V] [DecidableEq V]
    (A B C : SimpleGraph V)
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj] :
    (cyclicColoredTriples A B C).card =
      (cyclicColoredTriples B C A).card := by
  classical
  apply Finset.card_bij (fun p _ => (p.2.2, p.1, p.2.1))
  · intro p hp
    simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp ⊢
    exact ⟨hp.2.1, hp.2.2, hp.1⟩
  · intro p hp q hq hpq
    rcases p with ⟨x, z, y⟩
    rcases q with ⟨x', z', y'⟩
    simp only at hpq
    cases hpq
    rfl
  · intro p hp
    refine ⟨(p.2.1, p.2.2, p.1), ?_, ?_⟩
    · simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp ⊢
      exact ⟨hp.2.2, hp.1, hp.2.1⟩
    · rcases p with ⟨x, z, y⟩
      rfl

/-- Reverse the two roots of a repeated-closing fork.  The first owner color
is unchanged, the other two owner colors and the first two component labels
are swapped. -/
theorem hasRepeatedClosingInBlock_reverse
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (e f g : D.ConnectedComponent)
    (h : HasRepeatedClosingInBlock D A B C e f g) :
    HasRepeatedClosingInBlock D A C B f e g := by
  obtain ⟨x, y, z₁, z₂, hz, hx, hy, hz₁, hz₂,
    hxy, hyz₁, hz₁x, hyz₂, hz₂x⟩ :=
      (hasRepeatedClosingInBlock_iff_exists_ownerFork D A B C e f g).mp h
  apply (hasRepeatedClosingInBlock_iff_exists_ownerFork D A C B f e g).mpr
  exact ⟨y, x, z₁, z₂, hz, hy, hx, hz₁, hz₂,
    (A.adj_comm y x).mpr hxy, (C.adj_comm x z₁).mpr hz₁x,
    (B.adj_comm z₁ y).mpr hyz₁, (C.adj_comm x z₂).mpr hz₂x,
    (B.adj_comm z₂ y).mpr hyz₂⟩

/-- If a colored-triple census is more than twice the directed first-edge
space and the defect graph has two components, then three triples share one
first edge; two of their closing vertices share a defect component, producing
a repeated closing inside one component block. -/
theorem exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
    {V : Type*} [Fintype V] [DecidableEq V]
    (D A B C : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    [DecidableRel A.Adj] [DecidableRel B.Adj] [DecidableRel C.Adj]
    (hcount : Fintype.card D.ConnectedComponent = 2)
    (hmore : (directedColoredEdges A).card * 2 <
      (cyclicColoredTriples A B C).card) :
    ∃ e f g : D.ConnectedComponent,
      HasRepeatedClosingInBlock D A B C e f g := by
  classical
  let S := cyclicColoredTriples A B C
  let T := directedColoredEdges A
  let F : V × V × V → (Σ _x : V, V) := fun p => ⟨p.1, p.2.2⟩
  have hmap : ∀ p ∈ S, F p ∈ T := by
    intro p hp
    have hpColor := (Finset.mem_filter.mp hp).2
    simp only [T, F, directedColoredEdges, Finset.mem_sigma,
      Finset.mem_univ, true_and]
    exact (A.mem_neighborFinset p.1 p.2.2).mpr hpColor.1
  obtain ⟨key, _hkey, hfiberCard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := F) hmap hmore
  let P := S.filter fun p => F p = key
  let K : V × V × V → D.ConnectedComponent := fun p =>
    D.connectedComponentMk p.2.1
  have hPcard : Fintype.card D.ConnectedComponent < P.card := by
    rw [hcount]
    exact hfiberCard
  have hKmap : Set.MapsTo K (P : Set (V × V × V))
      ((Finset.univ : Finset D.ConnectedComponent) : Set D.ConnectedComponent) := by
    intro p hp
    exact Finset.mem_univ _
  obtain ⟨p, hp, r, hr, hpr, hK⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hPcard hKmap
  have hpData := Finset.mem_filter.mp hp
  have hrData := Finset.mem_filter.mp hr
  have hF : F p = F r := hpData.2.trans hrData.2.symm
  have hxy : p.1 = r.1 ∧ p.2.2 = r.2.2 := by
    simpa [F] using congrArg (fun z : (Σ _x : V, V) => (z.1, z.2)) hF
  have hz : p.2.1 ≠ r.2.1 := by
    intro hz
    apply hpr
    rcases p with ⟨x, z, y⟩
    rcases r with ⟨x', z', y'⟩
    apply Prod.ext hxy.1
    apply Prod.ext hz hxy.2
  let e := D.connectedComponentMk p.1
  let f := D.connectedComponentMk p.2.2
  let g := D.connectedComponentMk p.2.1
  have hrg : D.connectedComponentMk r.2.1 = g := by
    simpa [K, g] using hK.symm
  refine ⟨e, f, g, p, ?_, r, ?_, hpr, hxy.1, hxy.2, hz⟩
  · apply Finset.mem_filter.mpr
    refine ⟨hpData.1, ?_⟩
    simp [e, f, g]
  · apply Finset.mem_filter.mpr
    refine ⟨hrData.1, ?_⟩
    have hre : D.connectedComponentMk r.1 = e := by
      simpa [e] using congrArg D.connectedComponentMk hxy.1.symm
    have hrf : D.connectedComponentMk r.2.2 = f := by
      simpa [f] using congrArg D.connectedComponentMk hxy.2.symm
    exact ⟨(ConnectedComponent.mem_supp_iff e r.1).mpr hre,
      (ConnectedComponent.mem_supp_iff f r.2.2).mpr hrf,
      (ConnectedComponent.mem_supp_iff g r.2.1).mpr hrg⟩

/-- In the `[6,2]` stratum, orient the repeated owner color toward the
normalized size-two component.  The global mixed census is six times the
directed first-edge space, so the multiplicity theorem forces a genuine
component-block repeated closing despite the weak cross-budget bound. -/
theorem orderSixtyFour_sixTwo_exists_repeatedClosingInBlock
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
    (hab : a ≠ b) (hma : m a = 2) (hmb : m b = 6) :
    ∃ e f g,
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g := by
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  have hAreg : ∀ x, A.degree x = m a * (8 - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
  have hedge : (directedColoredEdges A).card = 64 * (m a * 7) := by
    rw [card_directedColoredEdges_of_regular A (m a * (8 - 1)) hAreg]
    norm_num
  have htri := binarySquare_regular_card_twoOwnerColoredTriples
    G hfree (q := 8) (by norm_num) hreg (by norm_num) a b hab (hm a) (hm b)
  apply exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
    (secondOrderDefectGraph G) A A B hcount
  rw [hedge, htri, hma, hmb]
  norm_num

/-- The same multiplicity argument works before and after one cyclic
rotation, since both orientations still use the small owner `a` on their
first edge. -/
theorem orderSixtyFour_sixTwo_exists_twoCyclicRepeatedClosingInBlocks
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
    (hab : a ≠ b) (hma : m a = 2) (hmb : m b = 6) :
    (∃ e f g,
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f g) ∧
    (∃ e f g,
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b)
        (componentOwnerGraph G (secondOrderDefectGraph G) a) e f g) := by
  refine ⟨orderSixtyFour_sixTwo_exists_repeatedClosingInBlock
    G hfree hreg hcount m hm a b hab hma hmb, ?_⟩
  let A := componentOwnerGraph G (secondOrderDefectGraph G) a
  let B := componentOwnerGraph G (secondOrderDefectGraph G) b
  have hAreg : ∀ x, A.degree x = m a * (8 - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
  have hedge : (directedColoredEdges A).card = 64 * (m a * 7) := by
    rw [card_directedColoredEdges_of_regular A (m a * (8 - 1)) hAreg]
    norm_num
  have htri := binarySquare_regular_card_twoOwnerColoredTriples
    G hfree (q := 8) (by norm_num) hreg (by norm_num) a b hab (hm a) (hm b)
  apply exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
    (secondOrderDefectGraph G) A B A hcount
  rw [← card_cyclicColoredTriples_rotate A A B, hedge, htri, hma, hmb]
  norm_num

set_option maxRecDepth 10000 in
/-- Refine the sixfold small-owner edge multiplicity.  Three closings land in
one defect component; two of their small-owner centers coincide.  Their
large-owner centers must then be distinct by C4-freeness.  Hence either the
fixed root lies in the closing component, or those large-owner centers form a
dense cross-component routing fragment. -/
theorem orderSixtyFour_sixTwo_rootClosingSameComponent_or_largeOwnerDensity
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
    (hab : a ≠ b) (hma : m a = 2) (hmb : m b = 6) :
    (∃ e f,
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f e) ∨
      HasTwoCenterRoutingRowDensityForOwner G hfree m b := by
  classical
  let D := secondOrderDefectGraph G
  let A := componentOwnerGraph G D a
  let B := componentOwnerGraph G D b
  let S := cyclicColoredTriples A A B
  let T := directedColoredEdges A
  let F : Fin 64 × Fin 64 × Fin 64 → (Σ _x : Fin 64, Fin 64) :=
    fun p => ⟨p.1, p.2.2⟩
  have hAreg : ∀ x, A.degree x = m a * (8 - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree (q := 8) (by norm_num) hreg (by norm_num) a (hm a)
  have hedge : T.card = 896 := by
    change (directedColoredEdges A).card = 896
    rw [card_directedColoredEdges_of_regular A (m a * (8 - 1)) hAreg,
      hma]
    norm_num
  have htri := binarySquare_regular_card_twoOwnerColoredTriples
    G hfree (q := 8) (by norm_num) hreg (by norm_num) a b hab (hm a) (hm b)
  have hScard : S.card = 5376 := by
    simpa [S, hma, hmb] using htri
  have hmap : ∀ p ∈ S, F p ∈ T := by
    intro p hp
    have hpColor := (Finset.mem_filter.mp hp).2
    simp only [T, F, directedColoredEdges, Finset.mem_sigma,
      Finset.mem_univ, true_and]
    exact (A.mem_neighborFinset p.1 p.2.2).mpr hpColor.1
  have hmore : T.card * 5 < S.card := by omega
  obtain ⟨key, _hkey, hPcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := F) hmap hmore
  let P := S.filter fun p => F p = key
  change 5 < P.card at hPcard
  let K : Fin 64 × Fin 64 × Fin 64 → D.ConnectedComponent := fun p =>
    D.connectedComponentMk p.2.1
  have hKmap : ∀ p ∈ P, K p ∈ (Finset.univ : Finset D.ConnectedComponent) :=
    fun _p _hp => Finset.mem_univ _
  have hKmore : (Finset.univ : Finset D.ConnectedComponent).card * 2 < P.card := by
    rw [Finset.card_univ, hcount]
    omega
  obtain ⟨g, _hg, hQcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := K) hKmap hKmore
  let Q := P.filter fun p => K p = g
  change 2 < Q.card at hQcard
  let U : Fin 64 × Fin 64 × Fin 64 → Fin 64 := fun p =>
    componentOwnerCenter G D a p.2.2 p.2.1
  let fkey := D.connectedComponentMk key.2
  let Ca := componentNeighborFinset G D a key.2
  have hCaCard : Ca.card = 2 := by
    change (componentNeighborFinset G D a key.2).card = 2
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree (q := 8) (by norm_num) hreg (by norm_num) fkey a
        (x := key.2) ConnectedComponent.connectedComponentMk_mem
    rw [hm a, hma] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 8) hmul
  have hUmap : ∀ p ∈ Q, U p ∈ Ca := by
    intro p hp
    have hpQ := Finset.mem_filter.mp hp
    have hpP := Finset.mem_filter.mp hpQ.1
    have hpColor := (Finset.mem_filter.mp hpP.1).2
    have hpy : p.2.2 = key.2 := by
      exact congrArg Sigma.snd hpP.2
    have hu := componentOwnerCenter_spec G D a hpColor.2.1
    change U p ∈ componentNeighborFinset G D a key.2
    rw [componentNeighborFinset, Finset.mem_filter]
    refine ⟨?_, (ConnectedComponent.mem_supp_iff a _).mp hu.1⟩
    exact (G.mem_neighborFinset key.2 _).mpr (by simpa [U, hpy] using hu.2.1)
  have hUmore : Ca.card * 1 < Q.card := by omega
  have hUmore' : Ca.card < Q.card := by omega
  obtain ⟨p, hp, r, hr, hpr, hUeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hUmore' hUmap
  have hpQ := Finset.mem_filter.mp hp
  have hrQ := Finset.mem_filter.mp hr
  have hpP := Finset.mem_filter.mp hpQ.1
  have hrP := Finset.mem_filter.mp hrQ.1
  have hpColor := (Finset.mem_filter.mp hpP.1).2
  have hrColor := (Finset.mem_filter.mp hrP.1).2
  have hF : F p = F r := hpP.2.trans hrP.2.symm
  have hxy : p.1 = r.1 ∧ p.2.2 = r.2.2 := by
    simpa [F] using congrArg (fun z : (Σ _x : Fin 64, Fin 64) => (z.1, z.2)) hF
  have hzcomp : D.connectedComponentMk p.2.1 = g := hpQ.2
  have hrzcomp : D.connectedComponentMk r.2.1 = g := hrQ.2
  have hz : p.2.1 ≠ r.2.1 := by
    intro hz
    apply hpr
    rcases p with ⟨x, z, y⟩
    rcases r with ⟨x', z', y'⟩
    apply Prod.ext hxy.1
    apply Prod.ext hz hxy.2
  let ua := U p
  let ub₁ := componentOwnerCenter G D b p.2.1 p.1
  let ub₂ := componentOwnerCenter G D b r.2.1 r.1
  have hua := componentOwnerCenter_spec G D a hpColor.2.1
  have hub₁ := componentOwnerCenter_spec G D b hpColor.2.2
  have hub₂ := componentOwnerCenter_spec G D b hrColor.2.2
  have huacomp : D.connectedComponentMk ua = a :=
    (ConnectedComponent.mem_supp_iff a ua).mp hua.1
  have hub₁comp : D.connectedComponentMk ub₁ = b :=
    (ConnectedComponent.mem_supp_iff b ub₁).mp hub₁.1
  have huaub₁ : ua ≠ ub₁ := by
    intro h
    apply hab
    exact huacomp.symm.trans ((congrArg D.connectedComponentMk h).trans hub₁comp)
  have hubne : ub₁ ≠ ub₂ := by
    intro hub
    have huaR : G.Adj r.2.1 ua := by
      have huR := (componentOwnerCenter_spec G D a hrColor.2.1).2.2
      change componentOwnerCenter G D a p.2.2 p.2.1 =
        componentOwnerCenter G D a r.2.2 r.2.1 at hUeq
      rw [← hUeq] at huR
      exact huR
    have hubR : G.Adj r.2.1 ub₁ := by
      simpa [ub₁, ub₂, hub] using hub₂.2.1
    exact hfree (containsC4_of_two_common huaub₁ hz
      hua.2.2 hub₁.2.1 huaR hubR)
  let e := D.connectedComponentMk p.1
  by_cases heg : e = g
  · left
    let f := D.connectedComponentMk p.2.2
    refine ⟨e, f, p, ?_, r, ?_, hpr, hxy.1, hxy.2, hz⟩
    · apply Finset.mem_filter.mpr
      refine ⟨hpP.1, ConnectedComponent.connectedComponentMk_mem,
        ConnectedComponent.connectedComponentMk_mem, ?_⟩
      exact (ConnectedComponent.mem_supp_iff e p.2.1).mpr
        (hzcomp.trans heg.symm)
    · apply Finset.mem_filter.mpr
      have hre : D.connectedComponentMk r.1 = e := by
        simpa [e] using congrArg D.connectedComponentMk hxy.1.symm
      have hrf : D.connectedComponentMk r.2.2 = f := by
        simpa [f] using congrArg D.connectedComponentMk hxy.2.symm
      exact ⟨hrP.1, (ConnectedComponent.mem_supp_iff e r.1).mpr hre,
        (ConnectedComponent.mem_supp_iff f r.2.2).mpr hrf,
        (ConnectedComponent.mem_supp_iff e r.2.1).mpr (hrzcomp.trans heg.symm)⟩
  · right
    have heg' : e ≠ g := heg
    let xs : e.supp := ⟨p.1, ConnectedComponent.connectedComponentMk_mem⟩
    let ub₁s : b.supp := ⟨ub₁, hub₁.1⟩
    let ub₂s : b.supp := ⟨ub₂, hub₂.1⟩
    have hubne' : ub₁s ≠ ub₂s := fun h => hubne (congrArg Subtype.val h)
    refine ⟨e, g, heg', xs, ub₁s, ub₂s, hubne', hub₁.2.2, ?_, ?_⟩
    · simpa [xs, ub₂s, hxy.1] using hub₂.2.2
    · exact binarySquare_regular_twoSeparatedCenters_routingRow_density
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm heg'
          xs ub₁s ub₂s hubne' hub₁.2.2
            (by simpa [xs, ub₂s, hxy.1] using hub₂.2.2)

/-- Link the residual to the once-rotated orientation using reversal of the
same repeated-closing fork. -/
theorem orderSixtyFour_sixTwo_largeOwnerDensity_or_linkedRootClosingResiduals
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
    (hab : a ≠ b) (hma : m a = 2) (hmb : m b = 6) :
    HasTwoCenterRoutingRowDensityForOwner G hfree m b ∨
      ∃ e f,
        HasRepeatedClosingInBlock (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b) e f e ∧
          HasRepeatedClosingInBlock (secondOrderDefectGraph G)
            (componentOwnerGraph G (secondOrderDefectGraph G) a)
            (componentOwnerGraph G (secondOrderDefectGraph G) b)
            (componentOwnerGraph G (secondOrderDefectGraph G) a) f e e := by
  have h := orderSixtyFour_sixTwo_rootClosingSameComponent_or_largeOwnerDensity
    G hfree hreg hcount m hm a b hab hma hmb
  rcases h with ⟨e, f, hr⟩ | hd
  · exact Or.inr ⟨e, f, hr,
      hasRepeatedClosingInBlock_reverse
        (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) e f e hr⟩
  · exact Or.inl hd

end

end Erdos85

#print axioms Erdos85.card_cyclicColoredTriples_rotate
#print axioms Erdos85.hasRepeatedClosingInBlock_reverse
#print axioms Erdos85.exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
#print axioms Erdos85.orderSixtyFour_sixTwo_exists_repeatedClosingInBlock
#print axioms Erdos85.orderSixtyFour_sixTwo_exists_twoCyclicRepeatedClosingInBlocks
#print axioms Erdos85.orderSixtyFour_sixTwo_rootClosingSameComponent_or_largeOwnerDensity
#print axioms Erdos85.orderSixtyFour_sixTwo_largeOwnerDensity_or_linkedRootClosingResiduals
