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
