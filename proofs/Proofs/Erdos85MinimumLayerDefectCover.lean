import Proofs.Erdos85MinimumLayerSaturationContradiction
import Proofs.Erdos85CycleCoverLength

/-!
# The saturated exterior defect covering

This file packages the saturated matching lift as a genuine locally
bijective graph map from the parent defect graph on exterior vertices to the
child defect graph.  It is the graph-facing interface needed to transport
connected cycles and apply cyclic-cover length divisibility.
-/

namespace Erdos85

noncomputable section

/-- Vertices outside the selected minimum defect layer. -/
def minimumLayerExteriorVertex
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) :=
  {z : V // z ∉ minimumLayerImageFinset D c₀}

noncomputable instance minimumLayerExteriorVertexFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) :
    Fintype (minimumLayerExteriorVertex D c₀) := by
  unfold minimumLayerExteriorVertex
  infer_instance

/-- The complement of the minimum layer is a union of whole defect
components: reachability from an exterior vertex never enters the minimum
layer. -/
theorem minimumLayerExterior_closed_under_reachable
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent)
    (z : minimumLayerExteriorVertex D c₀) {y : V}
    (hzy : D.Reachable z.1 y) :
    y ∉ minimumLayerImageFinset D c₀ := by
  classical
  intro hy
  rw [minimumLayerImageFinset] at hy
  obtain ⟨a, _ha, hay⟩ := Finset.mem_image.mp hy
  have hyComp : D.connectedComponentMk y = a.1.1 := by
    rw [← hay]
    exact (SimpleGraph.ConnectedComponent.mem_supp_iff a.1.1 a.2.1).mp a.2.2
  have hzComp : D.connectedComponentMk z.1 = a.1.1 :=
    (SimpleGraph.ConnectedComponent.sound hzy).trans hyComp
  have hzMem : z.1 ∈ a.1.1.supp :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff a.1.1 z.1).mpr hzComp
  let az : minimumLayerVertex D c₀ := ⟨a.1, ⟨z.1, hzMem⟩⟩
  apply z.2
  change z.1 ∈ Finset.univ.image
    (minimumLayerVertexValue (D := D) (c₀ := c₀))
  exact Finset.mem_image.mpr ⟨az, Finset.mem_univ _, rfl⟩

/-- Passing to the exterior subtype does not split or shrink any exterior
defect component. -/
theorem minimumLayerExterior_component_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) (z : minimumLayerExteriorVertex D c₀) :
    (((D.comap Subtype.val).connectedComponentMk z).supp.ncard) =
      (D.connectedComponentMk z.1).supp.ncard := by
  classical
  let DX := D.comap (fun x : minimumLayerExteriorVertex D c₀ => x.1)
  let CX := DX.connectedComponentMk z
  let C := D.connectedComponentMk z.1
  let valHom : DX →g D :=
    { toFun := Subtype.val
      map_rel' := fun h => h }
  let lift : C → minimumLayerExteriorVertex D c₀ := fun y =>
    ⟨y.1, minimumLayerExterior_closed_under_reachable D c₀ z
      (C.reachable_of_mem_supp rfl y.2)⟩
  let liftHom : C.toSimpleGraph →g DX :=
    { toFun := lift
      map_rel' := fun h => h }
  let e : CX.supp ≃ C.supp :=
    { toFun := fun w =>
        ⟨w.1.1, by
          have hcomp : DX.connectedComponentMk w.1 = DX.connectedComponentMk z :=
            (SimpleGraph.ConnectedComponent.mem_supp_iff CX w.1).mp w.2
          exact (SimpleGraph.ConnectedComponent.mem_supp_iff C w.1.1).mpr
            (SimpleGraph.ConnectedComponent.sound
              ((SimpleGraph.ConnectedComponent.exact hcomp).map valHom))⟩
      invFun := fun y =>
        ⟨lift y, by
          have hr := C.reachable_toSimpleGraph y.2 (show z.1 ∈ C.supp from rfl)
          have hmapped := hr.map liftHom
          have hliftz : lift ⟨z.1, (show z.1 ∈ C.supp from rfl)⟩ = z :=
            Subtype.ext rfl
          change DX.Reachable (lift y)
            (lift ⟨z.1, (show z.1 ∈ C.supp from rfl)⟩) at hmapped
          rw [hliftz] at hmapped
          exact (SimpleGraph.ConnectedComponent.mem_supp_iff CX (lift y)).mpr
            (SimpleGraph.ConnectedComponent.sound hmapped)⟩
      left_inv := fun w => Subtype.ext (Subtype.ext rfl)
      right_inv := fun y => Subtype.ext rfl }
  rw [← Set.fintypeCard_eq_ncard, ← Set.fintypeCard_eq_ncard]
  exact Fintype.card_congr e

/-- A cyclic parametrization in the parent defect graph lifts to the
exterior subtype whenever all of its vertices lie outside the minimum layer. -/
theorem minimumLayer_exteriorCycleParam_neighborFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent)
    {n : ℕ} [NeZero n]
    (u : ZMod n → V)
    (hu : ∀ z, D.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hout : ∀ z, u z ∉ minimumLayerImageFinset D c₀) :
    let ux : ZMod n → minimumLayerExteriorVertex D c₀ :=
      fun z => ⟨u z, hout z⟩
    ∀ z, (D.comap Subtype.val).neighborFinset (ux z) =
      {ux (z - 1), ux (z + 1)} := by
  classical
  dsimp only
  intro z
  ext w
  rw [(D.comap Subtype.val).mem_neighborFinset]
  change D.Adj (u z) w.1 ↔ _
  rw [← D.mem_neighborFinset, hu z]
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.mem_insert.mpr (Or.inl (Subtype.ext h))
    · have h' := Finset.mem_singleton.mp h
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (Subtype.ext h')))
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val h))
    · have h' := Finset.mem_singleton.mp h
      exact Finset.mem_insert.mpr
        (Or.inr (Finset.mem_singleton.mpr (congrArg Subtype.val h')))

/-- **Saturated exterior defect cover.**  There is an owner projection from
the exterior parent vertices to child vertices.  It maps every parent defect
edge to a child defect edge, and every child defect edge out of an owner has
a unique lift out of the exterior vertex. -/
theorem exists_minimumLayer_saturated_defectCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let X := minimumLayerExteriorVertex D c₀
    let H := minimumLayerGraph G D c₀
    let DH := secondOrderDefectGraph H
    let E := minimumLayerExternalNeighborFinset G D c₀
    ∃ owner : X → minimumLayerVertex D c₀,
      (∀ z : X, z.1 ∈ E (owner z)) ∧
      (∀ {z w : X}, D.Adj z.1 w.1 → DH.Adj (owner z) (owner w)) ∧
      (∀ (z : X) (b : minimumLayerVertex D c₀),
        DH.Adj (owner z) b →
          ∃! w : X, D.Adj z.1 w.1 ∧ owner w = b) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  letI : DecidableEq X := Subtype.instDecidableEq
  let H := minimumLayerGraph G D c₀
  let DH := secondOrderDefectGraph H
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hownerExists : ∀ z : X, ∃! a : minimumLayerVertex D c₀, z.1 ∈ E a := by
    intro z
    exact minimumLayer_existsUnique_externalOwner_of_saturated
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat z.2
  let owner : X → minimumLayerVertex D c₀ := fun z =>
    Classical.choose (hownerExists z)
  have hownerMem : ∀ z : X, z.1 ∈ E (owner z) := fun z =>
    (Classical.choose_spec (hownerExists z)).1
  have hownerUnique : ∀ (z : X) (a : minimumLayerVertex D c₀),
      z.1 ∈ E a → a = owner z := by
    intro z a hza
    exact (Classical.choose_spec (hownerExists z)).2 a hza
  have hmap : ∀ {z w : X}, D.Adj z.1 w.1 →
      DH.Adj (owner z) (owner w) := by
    intro z w hzw
    obtain ⟨b, hbD, hwb⟩ :=
      minimumLayer_saturated_defectNeighbor_has_childOwner
        G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
          (owner z) (hownerMem z) hzw
    simpa [hownerUnique w b hwb] using hbD
  refine ⟨owner, hownerMem, hmap, ?_⟩
  intro z b hzbD
  obtain ⟨y, hyD, hyuniq⟩ :=
    minimumLayer_saturated_childDefect_lifts_matching
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        (owner z) b hzbD z.1 (hownerMem z)
  have hyOutside : y.1 ∉ minimumLayerImageFinset D c₀ :=
    (Finset.mem_sdiff.mp y.2).2
  let w : X := ⟨y.1, hyOutside⟩
  have hwowner : owner w = b := by
    exact (hownerUnique w b y.2).symm
  refine ⟨w, ⟨hyD, hwowner⟩, ?_⟩
  intro w' hw'
  apply Subtype.ext
  change w'.1 = y.1
  have hw'mem : w'.1 ∈ E b := by
    rw [← hw'.2]
    exact hownerMem w'
  exact congrArg Subtype.val (hyuniq ⟨w'.1, hw'mem⟩ hw'.1)

/-- Every connected component of the parent defect graph on the minimum
layer is exactly one tagged minimum component, hence has the common minimum
cardinality. -/
theorem minimumLayerParentDefect_component_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) (a : minimumLayerVertex D c₀) :
    ((minimumLayerParentDefect D c₀).connectedComponentMk a).supp.ncard =
      c₀.supp.ncard := by
  classical
  let P := minimumLayerParentDefect D c₀
  let C := P.connectedComponentMk a
  have hSupp : C.supp = {b | b.1 = a.1} := by
    ext b
    constructor
    · intro hb
      have hcomp : P.connectedComponentMk b = P.connectedComponentMk a :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff C b).mp hb
      have hreach : P.Reachable b a :=
        SimpleGraph.ConnectedComponent.exact hcomp
      let π : P →g D :=
        { toFun := minimumLayerVertexValue
          map_rel' := fun h => h }
      have hvalueComp :
          D.connectedComponentMk b.2.1 = D.connectedComponentMk a.2.1 :=
        SimpleGraph.ConnectedComponent.sound (hreach.map π)
      have hbComp : D.connectedComponentMk b.2.1 = b.1.1 :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff b.1.1 b.2.1).mp b.2.2
      have haComp : D.connectedComponentMk a.2.1 = a.1.1 :=
        (SimpleGraph.ConnectedComponent.mem_supp_iff a.1.1 a.2.1).mp a.2.2
      apply Subtype.ext
      exact hbComp.symm.trans (hvalueComp.trans haComp)
    · intro htag
      have hbMem : b.2.1 ∈ a.1.1.supp := by
        rw [← htag]
        exact b.2.2
      let ia : a.1.1 := ⟨a.2.1, a.2.2⟩
      let ib : a.1.1 := ⟨b.2.1, hbMem⟩
      let ι : a.1.1.toSimpleGraph →g P :=
        { toFun := fun y => ⟨a.1, y⟩
          map_rel' := fun h => h }
      have hr := a.1.1.reachable_toSimpleGraph a.2.2 hbMem
      have hmapped := hr.map ι
      have hia : ι ia = a := minimumLayerVertexValue_injective rfl
      have hib : ι ib = b := minimumLayerVertexValue_injective rfl
      rw [hia, hib] at hmapped
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff C b).mpr
        (SimpleGraph.ConnectedComponent.sound hmapped).symm
  let e : C.supp ≃ a.1.1.supp :=
    { toFun := fun x =>
        ⟨x.1.2.1, by
          have hxTag : x.1.1 = a.1 := by
            simpa [hSupp] using x.2
          rw [← hxTag]
          exact x.1.2.2⟩
      invFun := fun y => ⟨⟨a.1, y⟩, by
        rw [hSupp]
        rfl⟩
      left_inv := fun x => Subtype.ext (minimumLayerVertexValue_injective rfl)
      right_inv := fun y => Subtype.ext rfl }
  rw [← Set.fintypeCard_eq_ncard]
  calc
    Fintype.card C.supp = Fintype.card a.1.1.supp :=
      Fintype.card_congr e
    _ = a.1.1.supp.ncard := Set.fintypeCard_eq_ncard _
    _ = c₀.supp.ncard := a.1.2

/-- **Component-size divisibility for the saturated defect cover.**  No
cycle labeling or orientation data is required: the common minimum defect
component cardinality divides every exterior cover-component cardinality. -/
theorem minimumLayer_saturated_component_card_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let X := minimumLayerExteriorVertex D c₀
    let DX := D.comap (fun z : X => z.1)
    ∀ z : X, c₀.supp.ncard ∣
      (DX.connectedComponentMk z).supp.ncard := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let DX := D.comap (fun z : X => z.1)
  let H := minimumLayerGraph G D c₀
  let DH := secondOrderDefectGraph H
  let P := minimumLayerParentDefect D c₀
  obtain ⟨owner, _howner, hmap, hlift⟩ :=
    exists_minimumLayer_saturated_defectCover
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hdefectEq : P = DH :=
    minimumLayerParentDefect_eq_childDefect
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hdegP : ∀ a, P.degree a = 2 := by
    intro a
    exact minimumLayerParentDefect_degree D 2
      (secondOrderDefectGraph_degree_eq_two
        G hfree hd heven hmin hcard) c₀ a
  have hmapP : ∀ {x y : X}, DX.Adj x y → P.Adj (owner x) (owner y) := by
    intro x y hxy
    rw [hdefectEq]
    exact hmap hxy
  have hliftP : ∀ (x : X) (b : minimumLayerVertex D c₀),
      P.Adj (owner x) b → ∃! w : X, DX.Adj x w ∧ owner w = b := by
    intro x b hxb
    apply hlift x b
    change DH.Adj (owner x) b
    rw [← hdefectEq]
    exact hxb
  intro z
  have hdiv := cycleCover_component_card_dvd_of_localBijection
    DX P owner hdegP hmapP hliftP z
  rw [minimumLayerParentDefect_component_card D c₀ (owner z)] at hdiv
  exact hdiv

/-- **Global divisibility in the saturated branch.**  The cardinality of the
chosen minimum layer component divides the cardinality of every component
of the ambient second-order defect graph.  Equal-sized components are
immediate; every other component lies in the exterior and is handled by the
saturated graph covering. -/
theorem minimumLayer_saturated_minimum_card_dvd_all_components
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c₀.supp.ncard ∣ c.supp.ncard := by
  classical
  let D := secondOrderDefectGraph G
  intro c
  by_cases hc : c.supp.ncard = c₀.supp.ncard
  · rw [hc]
  obtain ⟨x, hx⟩ := c.nonempty_supp
  have hxOutside : x ∉ minimumLayerImageFinset D c₀ := by
    intro hxLayer
    rw [minimumLayerImageFinset] at hxLayer
    obtain ⟨a, _ha, hax⟩ := Finset.mem_image.mp hxLayer
    have hxComp : D.connectedComponentMk x = c :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp hx
    have haComp : D.connectedComponentMk a.2.1 = a.1.1 :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff a.1.1 a.2.1).mp a.2.2
    have hca : c = a.1.1 := by
      rw [← hxComp, ← hax]
      exact haComp
    apply hc
    rw [hca]
    exact a.1.2
  let z : minimumLayerExteriorVertex D c₀ := ⟨x, hxOutside⟩
  have hdiv := minimumLayer_saturated_component_card_dvd
    G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat z
  change c₀.supp.ncard ∣
    (((D.comap Subtype.val).connectedComponentMk z).supp.ncard) at hdiv
  rw [minimumLayerExterior_component_card D c₀ z] at hdiv
  have hzComp : D.connectedComponentMk z.1 = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c z.1).mp hx
  simpa [hzComp] using hdiv

/-- Graph-specific cyclic-cover consequence.  Once an exterior parent cycle
and a child cycle are parametrized and one starting exterior point is known
to lie over the child cycle, the child length divides the parent length. -/
theorem minimumLayer_saturated_cycle_length_dvd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3)
    {n r : ℕ} [NeZero n] [NeZero r]
    (hr : 3 ≤ r)
    (u : ZMod n → minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)
    (v : ZMod r → minimumLayerVertex (secondOrderDefectGraph G) c₀)
    (hvinj : Function.Injective v)
    (hu : ∀ z,
      ((secondOrderDefectGraph G).comap Subtype.val).neighborFinset (u z) =
        {u (z - 1), u (z + 1)})
    (hv : ∀ z,
      (secondOrderDefectGraph
        (minimumLayerGraph G (secondOrderDefectGraph G) c₀)).neighborFinset (v z) =
        {v (z - 1), v (z + 1)})
    (t₀ : ZMod r)
    (hstart : (u 0).1 ∈ minimumLayerExternalNeighborFinset
      G (secondOrderDefectGraph G) c₀ (v t₀)) :
    r ∣ n := by
  classical
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  letI : DecidableEq X := Subtype.instDecidableEq
  let H := minimumLayerGraph G D c₀
  let DH := secondOrderDefectGraph H
  let E := minimumLayerExternalNeighborFinset G D c₀
  let DX := D.comap (fun z : X => z.1)
  obtain ⟨owner, hownerMem, hmap, hlift⟩ :=
    exists_minimumLayer_saturated_defectCover
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hownerStart : owner (u 0) = v t₀ := by
    by_contra hne
    have hdisj := hpair (Finset.mem_univ (owner (u 0)))
      (Finset.mem_univ (v t₀)) hne
    exact (Finset.disjoint_left.mp hdisj (hownerMem (u 0)) hstart).elim
  have hstartRange : owner (u 0) ∈ Set.range v :=
    ⟨t₀, hownerStart.symm⟩
  apply cycleCover_length_dvd_of_localBijection_of_start
    DX DH owner hr u v hvinj hu hv
  · intro x y hxy
    exact hmap hxy
  · intro x b hxb
    obtain ⟨w, hw, _huniq⟩ := hlift x b hxb
    exact ⟨w, hw⟩
  · exact hstartRange

end

end Erdos85
