import Proofs.Erdos85BinarySquareTwoOwnerRepeatedClosing
import Proofs.Erdos85OrderSixtyFourThreeComponentForkAdapter
import Proofs.Erdos85OrderSixtyFourTwoComponentRepeatedClosing
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

/-- An `A,A,B` repeated closing on the alternating component shape `e,f,e`
forces two distinct `A`-centers at the `f`-root.  If the normalized size of
owner `a` is two, they saturate the cross routing row from `f` into `e`. -/
theorem binarySquare_regular_alternatingAABRepeatedClosing_forces_smallOwnerSaturation
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
    (a b e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hef : e ≠ f) (hma : m a = 2)
    (hrepeat : HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) e f e) :
    HasTwoCenterRoutingRowSaturationForOwner G hfree a := by
  let D := secondOrderDefectGraph G
  obtain ⟨x, y, z₁, _z₂, _hz, hx, hy, hz₁, _hz₂,
    haxy, hayz₁, hbz₁x, _hayz₂, _hbz₂x⟩ :=
      (hasRepeatedClosingInBlock_iff_exists_ownerFork D
        (componentOwnerGraph G D a) (componentOwnerGraph G D a)
        (componentOwnerGraph G D b) e f e).mp hrepeat
  let ys : f.supp := ⟨y, (ConnectedComponent.mem_supp_iff f y).mpr hy⟩
  let u₀ : a.supp := ⟨componentOwnerCenter G D a x y,
    (componentOwnerCenter_spec G D a haxy).1⟩
  let u₁ : a.supp := ⟨componentOwnerCenter G D a y z₁,
    (componentOwnerCenter_spec G D a hayz₁).1⟩
  let v : b.supp := ⟨componentOwnerCenter G D b z₁ x,
    (componentOwnerCenter_spec G D b hbz₁x).1⟩
  have hu₀v : u₀.1 ≠ v.1 := by
    intro h
    apply hab
    have hu₀comp := (ConnectedComponent.mem_supp_iff a u₀.1).mp u₀.2
    have hvcomp := (ConnectedComponent.mem_supp_iff b v.1).mp v.2
    exact hu₀comp.symm.trans ((congrArg D.connectedComponentMk h).trans hvcomp)
  have hu : u₀ ≠ u₁ := by
    intro h
    have hxu₁ : G.Adj x u₁.1 := by
      rw [← congrArg Subtype.val h]
      exact (componentOwnerCenter_spec G D a haxy).2.1
    have hz₁u₀ : G.Adj u₀.1 z₁ := by
      apply (G.adj_comm u₀.1 z₁).mpr
      rw [congrArg Subtype.val h]
      exact (componentOwnerCenter_spec G D a hayz₁).2.2
    have hxu₀ : G.Adj u₀.1 x :=
      (G.adj_comm u₀.1 x).mpr
        (by simpa [h] using hxu₁)
    have hz₁v : G.Adj v.1 z₁ :=
      (G.adj_comm v.1 z₁).mpr
        (componentOwnerCenter_spec G D b hbz₁x).2.1
    have hxv : G.Adj v.1 x :=
      (G.adj_comm v.1 x).mpr
        (componentOwnerCenter_spec G D b hbz₁x).2.2
    exact hfree (containsC4_of_two_common hbz₁x.ne hu₀v
      hz₁u₀ hxu₀ hz₁v hxv)
  have hyu₀ : G.Adj ys.1 u₀.1 :=
    (componentOwnerCenter_spec G D a haxy).2.2
  have hyu₁ : G.Adj ys.1 u₁.1 :=
    (componentOwnerCenter_spec G D a hayz₁).2.1
  have hd : HasTwoCenterRoutingRowDensity G hfree m f e a hef.symm ys := by
    refine ⟨u₀, u₁, hu, hyu₀, hyu₁, ?_⟩
    exact binarySquare_regular_twoSeparatedCenters_routingRow_density
      G hfree hq hreg hcard m hm hef.symm ys u₀ u₁ hu hyu₀ hyu₁
  exact twoCenterRoutingRowDensityForOwner_saturates_of_m_eq_two
    G hfree m a hma ⟨f, e, hef.symm, ys, hd⟩

/-- Exact geometry left by an all-same `A,A,B` repeated closing when `A` is
the normalized size-two owner: the two closing `A`-centers collapse to one,
while the fixed-edge `A`-center and the two `B`-centers stay distinct. -/
def HasCollapsedAllSameAABFork
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq D.ConnectedComponent]
    (a b d : D.ConnectedComponent) : Prop :=
  ∃ x y z₁ z₂ u₀ ua v₁ v₂ : V,
    z₁ ≠ z₂ ∧ y ≠ z₁ ∧ y ≠ z₂ ∧
    D.connectedComponentMk x = d ∧ D.connectedComponentMk y = d ∧
    D.connectedComponentMk z₁ = d ∧ D.connectedComponentMk z₂ = d ∧
    D.connectedComponentMk u₀ = a ∧ D.connectedComponentMk ua = a ∧
    D.connectedComponentMk v₁ = b ∧ D.connectedComponentMk v₂ = b ∧
    u₀ ≠ ua ∧ v₁ ≠ v₂ ∧
    G.Adj x u₀ ∧ G.Adj y u₀ ∧
    G.Adj y ua ∧ G.Adj z₁ ua ∧ G.Adj z₂ ua ∧
    G.Adj z₁ v₁ ∧ G.Adj x v₁ ∧
    G.Adj z₂ v₂ ∧ G.Adj x v₂

/-- Every all-same repeated closing has the collapsed-center geometry above. -/
theorem binarySquare_regular_allSameAABRepeatedClosing_forces_collapsedCenters
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
    (a b d : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 2)
    (hrepeat : HasRepeatedClosingInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b) d d d) :
    HasCollapsedAllSameAABFork G (secondOrderDefectGraph G) a b d := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨x, y, z₁, z₂, hz, hx, hy, hz₁, hz₂,
    haxy, hayz₁, hbz₁x, hayz₂, hbz₂x⟩ :=
      (hasRepeatedClosingInBlock_iff_exists_ownerFork D
        (componentOwnerGraph G D a) (componentOwnerGraph G D a)
        (componentOwnerGraph G D b) d d d).mp hrepeat
  let u₀ := componentOwnerCenter G D a x y
  let ua₁ := componentOwnerCenter G D a y z₁
  let ua₂ := componentOwnerCenter G D a y z₂
  let v₁ := componentOwnerCenter G D b z₁ x
  let v₂ := componentOwnerCenter G D b z₂ x
  have hu₀ := componentOwnerCenter_spec G D a haxy
  have hua₁ := componentOwnerCenter_spec G D a hayz₁
  have hua₂ := componentOwnerCenter_spec G D a hayz₂
  have hv₁ := componentOwnerCenter_spec G D b hbz₁x
  have hv₂ := componentOwnerCenter_spec G D b hbz₂x
  have owner_ne {u : V} (hua : u ∈ a.supp) {v : V} (hvb : v ∈ b.supp) :
      u ≠ v := by
    intro h
    apply hab
    have hucomp := (ConnectedComponent.mem_supp_iff a u).mp hua
    have hvcomp := (ConnectedComponent.mem_supp_iff b v).mp hvb
    exact hucomp.symm.trans ((congrArg D.connectedComponentMk h).trans hvcomp)
  have hu₀ua₁ : u₀ ≠ ua₁ := by
    intro h
    have hxu : G.Adj u₀ x := (G.adj_comm u₀ x).mpr hu₀.2.1
    have hzu : G.Adj u₀ z₁ := by
      rw [h]
      exact (G.adj_comm ua₁ z₁).mpr hua₁.2.2
    have hxv : G.Adj v₁ x := (G.adj_comm v₁ x).mpr hv₁.2.2
    have hzv : G.Adj v₁ z₁ := (G.adj_comm v₁ z₁).mpr hv₁.2.1
    exact hfree (containsC4_of_two_common hbz₁x.ne
      (owner_ne hu₀.1 hv₁.1) hzu hxu hzv hxv)
  have hu₀ua₂ : u₀ ≠ ua₂ := by
    intro h
    have hxu : G.Adj u₀ x := (G.adj_comm u₀ x).mpr hu₀.2.1
    have hzu : G.Adj u₀ z₂ := by
      rw [h]
      exact (G.adj_comm ua₂ z₂).mpr hua₂.2.2
    have hxv : G.Adj v₂ x := (G.adj_comm v₂ x).mpr hv₂.2.2
    have hzv : G.Adj v₂ z₂ := (G.adj_comm v₂ z₂).mpr hv₂.2.1
    exact hfree (containsC4_of_two_common hbz₂x.ne
      (owner_ne hu₀.1 hv₂.1) hzu hxu hzv hxv)
  let C := componentNeighborFinset G D a y
  have hCcard : C.card = 2 := by
    change (componentNeighborFinset G D a y).card = 2
    have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
      G hfree hq hreg hcard d a (x := y)
        ((ConnectedComponent.mem_supp_iff d y).mpr hy)
    rw [hm a, hma] at hmul
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
  have hu₀C : u₀ ∈ C := by
    change u₀ ∈ componentNeighborFinset G D a y
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset y u₀).mpr hu₀.2.2,
      (ConnectedComponent.mem_supp_iff a u₀).mp hu₀.1⟩
  have hua₁C : ua₁ ∈ C := by
    change ua₁ ∈ componentNeighborFinset G D a y
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset y ua₁).mpr hua₁.2.1,
      (ConnectedComponent.mem_supp_iff a ua₁).mp hua₁.1⟩
  have hua₂C : ua₂ ∈ C := by
    change ua₂ ∈ componentNeighborFinset G D a y
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset y ua₂).mpr hua₂.2.1,
      (ConnectedComponent.mem_supp_iff a ua₂).mp hua₂.1⟩
  have huaeq : ua₁ = ua₂ := by
    by_contra hne
    have hsub : ({u₀, ua₁, ua₂} : Finset V) ⊆ C := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact hu₀C
      · exact hua₁C
      · exact hua₂C
    have hle := Finset.card_le_card hsub
    simp [hu₀ua₁, hu₀ua₂, hne, hCcard] at hle
  have hvne : v₁ ≠ v₂ := by
    intro h
    have hz₁u : G.Adj ua₁ z₁ := (G.adj_comm ua₁ z₁).mpr hua₁.2.2
    have hz₂u : G.Adj ua₁ z₂ := by
      rw [huaeq]
      exact (G.adj_comm ua₂ z₂).mpr hua₂.2.2
    have hz₁v : G.Adj v₁ z₁ := (G.adj_comm v₁ z₁).mpr hv₁.2.1
    have hz₂v : G.Adj v₁ z₂ := by
      rw [h]
      exact (G.adj_comm v₂ z₂).mpr hv₂.2.1
    exact hfree (containsC4_of_two_common hz
      (owner_ne hua₁.1 hv₁.1) hz₁u hz₂u hz₁v hz₂v)
  refine ⟨x, y, z₁, z₂, u₀, ua₁, v₁, v₂, hz,
    hayz₁.ne, hayz₂.ne, hx, hy, hz₁, hz₂,
    (ConnectedComponent.mem_supp_iff a u₀).mp hu₀.1,
    (ConnectedComponent.mem_supp_iff a ua₁).mp hua₁.1,
    (ConnectedComponent.mem_supp_iff b v₁).mp hv₁.1,
    (ConnectedComponent.mem_supp_iff b v₂).mp hv₂.1,
    hu₀ua₁, hvne, hu₀.2.1, hu₀.2.2, hua₁.2.1, hua₁.2.2, ?_,
    hv₁.2.1, hv₁.2.2, hv₂.2.1, hv₂.2.2⟩
  rw [huaeq]
  exact hua₂.2.2

/-- The collapsed all-same skeleton always returns to small-owner saturation.
If its host component is `a`, its shared `A`-center has three distinct
neighbors inside a component where every vertex has only two.  If its host is
`b`, its two distinct `A`-centers directly saturate the row from `b` to `a`. -/
theorem binarySquare_regular_twoComponents_collapsedAllSame_forces_smallOwnerSaturation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ d, d.supp.ncard = q * m d)
    (a b d : (secondOrderDefectGraph G).ConnectedComponent)
    (hab : a ≠ b) (hma : m a = 2)
    (h : HasCollapsedAllSameAABFork G (secondOrderDefectGraph G) a b d) :
    HasTwoCenterRoutingRowSaturationForOwner G hfree a := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨x, y, z₁, z₂, u₀, ua, v₁, v₂, hz, hyz₁, hyz₂,
    hx, hy, hz₁, hz₂, hu₀a, huaa, hv₁b, hv₂b, hu, _hv,
    hxu₀, hyu₀, hyua, hz₁ua, hz₂ua, _hz₁v₁, _hxv₁,
    _hz₂v₂, _hxv₂⟩ := h
  have hd := eq_first_or_second_of_card_eq_two hcount a b d hab
  rcases hd with hda | hdb
  · let C := componentNeighborFinset G D a ua
    have hCcard : C.card = 2 := by
      change (componentNeighborFinset G D a ua).card = 2
      have hmul := binarySquare_regular_mul_componentNeighborCard_eq_componentCard
        G hfree hq hreg hcard a a (x := ua)
          ((ConnectedComponent.mem_supp_iff a ua).mpr huaa)
      rw [hm a, hma] at hmul
      exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < q) hmul
    have hyC : y ∈ C := by
      change y ∈ componentNeighborFinset G D a ua
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset ua y).mpr
          ((G.adj_comm ua y).mpr hyua), hy.trans hda⟩
    have hz₁C : z₁ ∈ C := by
      change z₁ ∈ componentNeighborFinset G D a ua
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset ua z₁).mpr
          ((G.adj_comm ua z₁).mpr hz₁ua), hz₁.trans hda⟩
    have hz₂C : z₂ ∈ C := by
      change z₂ ∈ componentNeighborFinset G D a ua
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset ua z₂).mpr
          ((G.adj_comm ua z₂).mpr hz₂ua), hz₂.trans hda⟩
    have hsub : ({y, z₁, z₂} : Finset V) ⊆ C := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with hwy | hwz₁ | hwz₂
      · simpa [hwy] using hyC
      · simpa [hwz₁] using hz₁C
      · simpa [hwz₂] using hz₂C
    have hle := Finset.card_le_card hsub
    simp [hyz₁, hyz₂, hz, hCcard] at hle
  · let ys : b.supp := ⟨y,
      (ConnectedComponent.mem_supp_iff b y).mpr (hy.trans hdb)⟩
    let u₀s : a.supp := ⟨u₀, (ConnectedComponent.mem_supp_iff a u₀).mpr hu₀a⟩
    let uas : a.supp := ⟨ua, (ConnectedComponent.mem_supp_iff a ua).mpr huaa⟩
    have hus : u₀s ≠ uas := fun heq => hu (congrArg Subtype.val heq)
    have hdensity : HasTwoCenterRoutingRowDensity G hfree m b a a hab.symm ys := by
      refine ⟨u₀s, uas, hus, hyu₀, hyua, ?_⟩
      exact binarySquare_regular_twoSeparatedCenters_routingRow_density
        G hfree hq hreg hcard m hm hab.symm ys u₀s uas hus hyu₀ hyua
    exact twoCenterRoutingRowDensityForOwner_saturates_of_m_eq_two
      G hfree m a hma ⟨b, a, hab.symm, ys, hdensity⟩

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

/-- Resolve the anonymous `e,f,e` residual against the two normalized
components.  Apart from the density branch, only the all-same block and the
two alternating normalized blocks remain. -/
theorem orderSixtyFour_sixTwo_largeOwnerDensity_or_normalizedResidual
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
      (∃ d,
        HasRepeatedClosingInBlock (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) b) d d d) ∨
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) a b a ∨
      HasRepeatedClosingInBlock (secondOrderDefectGraph G)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) a)
        (componentOwnerGraph G (secondOrderDefectGraph G) b) b a b := by
  have h := orderSixtyFour_sixTwo_largeOwnerDensity_or_linkedRootClosingResiduals
    G hfree hreg hcount m hm a b hab hma hmb
  rcases h with hd | ⟨e, f, hr, _hrrev⟩
  · exact Or.inl hd
  · by_cases hef : e = f
    · subst f
      exact Or.inr (Or.inl ⟨e, hr⟩)
    · have he := eq_first_or_second_of_card_eq_two hcount a b e hab
      have hf := eq_first_or_second_of_card_eq_two hcount a b f hab
      rcases he with rfl | rfl <;> rcases hf with rfl | rfl
      · exact False.elim (hef rfl)
      · exact Or.inr (Or.inr (Or.inl hr))
      · exact Or.inr (Or.inr (Or.inr hr))
      · exact False.elim (hef rfl)

/-- Final consumer of the alternating normalized blocks: only the all-same
repeated-closing block remains beside the large-owner density and small-owner
saturation terminals. -/
theorem orderSixtyFour_sixTwo_largeDensity_or_smallSaturation_or_allSame
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
      HasTwoCenterRoutingRowSaturationForOwner G hfree a ∨
      ∃ d,
        HasRepeatedClosingInBlock (secondOrderDefectGraph G)
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) a)
          (componentOwnerGraph G (secondOrderDefectGraph G) b) d d d := by
  have h := orderSixtyFour_sixTwo_largeOwnerDensity_or_normalizedResidual
    G hfree hreg hcount m hm a b hab hma hmb
  rcases h with hd | hall | haba | hbab
  · exact Or.inl hd
  · exact Or.inr (Or.inr hall)
  · exact Or.inr (Or.inl
      (binarySquare_regular_alternatingAABRepeatedClosing_forces_smallOwnerSaturation
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
          a b a b hab hab hma haba))
  · exact Or.inr (Or.inl
      (binarySquare_regular_alternatingAABRepeatedClosing_forces_smallOwnerSaturation
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
          a b b a hab hab.symm hma hbab))

/-- Replace the last all-same repeated-closing branch by its exact collapsed
center geometry. -/
theorem orderSixtyFour_sixTwo_largeDensity_or_smallSaturation_or_collapsedAllSame
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
      HasTwoCenterRoutingRowSaturationForOwner G hfree a ∨
      ∃ d, HasCollapsedAllSameAABFork G (secondOrderDefectGraph G) a b d := by
  have h := orderSixtyFour_sixTwo_largeDensity_or_smallSaturation_or_allSame
    G hfree hreg hcount m hm a b hab hma hmb
  rcases h with hd | hs | ⟨d, hr⟩
  · exact Or.inl hd
  · exact Or.inr (Or.inl hs)
  · exact Or.inr (Or.inr ⟨d,
      binarySquare_regular_allSameAABRepeatedClosing_forces_collapsedCenters
        G hfree (q := 8) (by norm_num) hreg (by norm_num) m hm
          a b d hab hma hr⟩)

/-- The complete pressure reduction for `[6,2]`: every branch reaches one of
the two shared routing terminals. -/
theorem orderSixtyFour_sixTwo_largeDensity_or_smallSaturation
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
      HasTwoCenterRoutingRowSaturationForOwner G hfree a := by
  have h :=
    orderSixtyFour_sixTwo_largeDensity_or_smallSaturation_or_collapsedAllSame
      G hfree hreg hcount m hm a b hab hma hmb
  rcases h with hd | hs | ⟨d, hc⟩
  · exact Or.inl hd
  · exact Or.inr hs
  · exact Or.inr
      (binarySquare_regular_twoComponents_collapsedAllSame_forces_smallOwnerSaturation
        G hfree (q := 8) (by norm_num) hreg (by norm_num) hcount m hm
          a b d hab hma hc)

end

end Erdos85

#print axioms Erdos85.card_cyclicColoredTriples_rotate
#print axioms Erdos85.hasRepeatedClosingInBlock_reverse
#print axioms Erdos85.binarySquare_regular_alternatingAABRepeatedClosing_forces_smallOwnerSaturation
#print axioms Erdos85.binarySquare_regular_allSameAABRepeatedClosing_forces_collapsedCenters
#print axioms Erdos85.binarySquare_regular_twoComponents_collapsedAllSame_forces_smallOwnerSaturation
#print axioms Erdos85.exists_repeatedClosingInBlock_of_two_mul_directedEdge_card_lt
#print axioms Erdos85.orderSixtyFour_sixTwo_exists_repeatedClosingInBlock
#print axioms Erdos85.orderSixtyFour_sixTwo_exists_twoCyclicRepeatedClosingInBlocks
#print axioms Erdos85.orderSixtyFour_sixTwo_rootClosingSameComponent_or_largeOwnerDensity
#print axioms Erdos85.orderSixtyFour_sixTwo_largeOwnerDensity_or_linkedRootClosingResiduals
#print axioms Erdos85.orderSixtyFour_sixTwo_largeOwnerDensity_or_normalizedResidual
#print axioms Erdos85.orderSixtyFour_sixTwo_largeDensity_or_smallSaturation_or_allSame
#print axioms Erdos85.orderSixtyFour_sixTwo_largeDensity_or_smallSaturation_or_collapsedAllSame
#print axioms Erdos85.orderSixtyFour_sixTwo_largeDensity_or_smallSaturation
