import Proofs.Erdos85MinimumLayerSaturatedClassification

/-!
# The saturated exterior as a positive-excess boundary graph

In the saturated minimum-layer branch every exterior vertex has exactly one
neighbor in the minimum layer.  Removing that layer therefore leaves a
`C₄`-free `(d-1)`-regular graph.  This packages the direct bridge from the
exact-boundary descent to the positive-excess plateau problem.
-/

namespace Erdos85

noncomputable section

/-- Restricting a `C₄`-free graph to the exterior subtype preserves
`C₄`-freeness. -/
theorem minimumLayerExteriorGraph_c4Free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G D : SimpleGraph V)
    [Fintype D.ConnectedComponent] [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) (hfree : ¬ containsC4 V G) :
    ¬ containsC4 (minimumLayerExteriorVertex D c₀)
      (G.comap Subtype.val) := by
  intro h
  obtain ⟨f, hf, hadj⟩ := h
  apply hfree
  refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

/-- In a saturated extension, every exterior vertex has exactly one
neighbor in the minimum layer. -/
theorem minimumLayer_saturated_exterior_internalNeighbor_eq_singleton
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
    (z : minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀) :
    ∃ a : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      G.neighborFinset z.1 ∩
          minimumLayerImageFinset (secondOrderDefectGraph G) c₀ =
        {a.2.1} := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  obtain ⟨a, hza, haUnique⟩ :=
    minimumLayer_existsUnique_externalOwner_of_saturated
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
        hspos hsd hsat z.2
  refine ⟨a, ?_⟩
  ext y
  constructor
  · intro hy
    obtain ⟨hyG, hyLayer⟩ := Finset.mem_inter.mp hy
    rw [minimumLayerImageFinset] at hyLayer
    obtain ⟨b, _hb, hby⟩ := Finset.mem_image.mp hyLayer
    have hzb : z.1 ∈ E b := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, z.2⟩
      change b.2.1 = y at hby
      apply (G.mem_neighborFinset b.2.1 z.1).mpr
      rw [hby]
      exact ((G.mem_neighborFinset z.1 y).mp hyG).symm
    have hba : b = a := haUnique b hzb
    rw [Finset.mem_singleton]
    subst b
    exact hby.symm
  · intro hy
    rw [Finset.mem_singleton] at hy
    subst y
    apply Finset.mem_inter.mpr
    constructor
    · apply (G.mem_neighborFinset z.1 a.2.1).mpr
      exact ((G.mem_neighborFinset a.2.1 z.1).mp
        (Finset.mem_sdiff.mp hza).1).symm
    · rw [minimumLayerImageFinset]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩

/-- **Saturated exterior regularity.**  Removing the minimum layer lowers
every exterior degree by exactly one. -/
theorem minimumLayer_saturated_exterior_regular
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
    ∀ z : minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀,
      (G.comap Subtype.val).degree z = d - 1 := by
  classical
  let D := secondOrderDefectGraph G
  let U := minimumLayerImageFinset D c₀
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  intro z
  obtain ⟨a, hinter⟩ :=
    minimumLayer_saturated_exterior_internalNeighbor_eq_singleton
      G hfree hd heven hmin hcard c₀ hregChild hcardChild
        hspos hsd hsat z
  have himage :
      ((G.comap Subtype.val).neighborFinset z).image Subtype.val =
        G.neighborFinset z.1 \ U := by
    ext y
    constructor
    · intro hy
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_sdiff.mpr
        ⟨(G.mem_neighborFinset z.1 w.1).mpr
            ((G.comap Subtype.val).mem_neighborFinset z w |>.mp hw), w.2⟩
    · intro hy
      obtain ⟨hyG, hyU⟩ := Finset.mem_sdiff.mp hy
      let w : minimumLayerExteriorVertex D c₀ := ⟨y, hyU⟩
      exact Finset.mem_image.mpr ⟨w,
        ((G.comap Subtype.val).mem_neighborFinset z w).mpr
          ((G.mem_neighborFinset z.1 y).mp hyG), rfl⟩
  have hcardImage :
      ((G.comap Subtype.val).neighborFinset z).card =
        (G.neighborFinset z.1 \ U).card := by
    rw [← himage, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [← (G.comap Subtype.val).card_neighborFinset_eq_degree, hcardImage]
  have hsplit := Finset.card_sdiff_add_card_inter
    (G.neighborFinset z.1) U
  rw [hinter, Finset.card_singleton, G.card_neighborFinset_eq_degree,
    hregParent z.1] at hsplit
  omega

/-- The saturated exterior has the ambient order minus the exact-boundary
child order. -/
theorem card_minimumLayer_saturated_exterior
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) {d s : ℕ}
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hcardChild : Fintype.card (minimumLayerVertex D c₀) =
      s * (s - 1) + 3) :
    Fintype.card (minimumLayerExteriorVertex D c₀) =
      d * (d - 1) + 3 - (s * (s - 1) + 3) := by
  classical
  let U := minimumLayerImageFinset D c₀
  change Fintype.card {z : V // ¬ z ∈ U} = _
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have hU := card_minimumLayerImageFinset D c₀
  rw [hcard, hU, hcardChild]

/-- Under the saturation equation, the exterior is a `(d-1)`-boundary
graph with explicit positive excess `(s-1)(s-2)+1`. -/
theorem card_minimumLayer_saturated_exterior_eq_boundary_add_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) {d s : ℕ}
    (hd : 4 ≤ d) (hspos : 0 < s)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hcardChild : Fintype.card (minimumLayerVertex D c₀) =
      s * (s - 1) + 3)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    Fintype.card (minimumLayerExteriorVertex D c₀) =
      (d - 1) * (d - 2) + 3 + ((s - 1) * (s - 2) + 1) := by
  rw [card_minimumLayer_saturated_exterior D c₀ hcard hcardChild]
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, s = t + 1 :=
    ⟨s - 1, by omega⟩
  norm_num at hsat ⊢
  subst d
  have ht : 1 ≤ t := by
    by_contra h
    have : t = 0 := by omega
    subst t
    norm_num at hd
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, t = q + 1 :=
    ⟨t - 1, by omega⟩
  norm_num
  have hm1 : (q + 1 + 1 - 1 : ℕ) = q + 1 := by omega
  have hm2 : (q + 1 + 1 - 2 : ℕ) = q := by omega
  have hs1 : ((q + 1) * (q + 1) + 3 - 1 : ℕ) =
      (q + 1) * (q + 1) + 2 := by omega
  have hs2 : ((q + 1) * (q + 1) + 3 - 2 : ℕ) =
      (q + 1) * (q + 1) + 1 := by omega
  rw [hs2, hm2]
  have hid :
      (((q + 1) * (q + 1) + 3) *
          ((q + 1) * (q + 1) + 2) + 3) =
        ((q + 2) * (q + 1) + 3) +
          (((q + 1) * (q + 1) + 2) *
            ((q + 1) * (q + 1) + 1) + 3 +
              ((q + 1) * q + 1)) := by
    ring
  have hle :
      ((q + 2) * (q + 1) + 3) ≤
        (((q + 1) * (q + 1) + 3) *
          ((q + 1) * (q + 1) + 2) + 3) := by
    rw [hid]
    omega
  apply (Nat.sub_eq_iff_eq_add hle).2
  rw [hid]
  omega

/-- The sole saturated residual left by the sharp descent has a concrete
positive-excess exterior: a `C₄`-free `123`-regular graph on `15120`
vertices (excess `111` over the degree-`123` boundary). -/
theorem minimumLayer_saturated_124_exterior_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hmin : 124 ≤ G.minDegree)
    (hcard : Fintype.card V = 124 * (124 - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = 12)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        12 * (12 - 1) + 3) :
    (¬ containsC4
        (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)
        (G.comap Subtype.val)) ∧
      (∀ z : minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀,
        (G.comap Subtype.val).degree z = 123) ∧
      Fintype.card
        (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀) = 15120 := by
  refine ⟨minimumLayerExteriorGraph_c4Free G (secondOrderDefectGraph G) c₀ hfree,
    ?_, ?_⟩
  · simpa using minimumLayer_saturated_exterior_regular
      G hfree (d := 124) (s := 12) (by norm_num) (by norm_num) hmin hcard
        c₀ hregChild hcardChild (by norm_num) (by norm_num) (by norm_num)
  · simpa using card_minimumLayer_saturated_exterior
      (secondOrderDefectGraph G) c₀ hcard hcardChild

end

end Erdos85
