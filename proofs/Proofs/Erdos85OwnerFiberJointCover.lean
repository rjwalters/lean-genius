import Proofs.Erdos85OwnerFiberTraceSplit

/-!
# A common owner map for the two saturated exterior covers

The saturated exterior carries two locally bijective covers: the restriction
of the parent defect graph covers the child defect graph, while the original
exterior adjacency covers the reflexive complement of the child adjacency.
Both constructions choose the unique deleted neighbour of an exterior
vertex.  This file records that they may therefore be witnessed by one and
the same owner map.  Keeping that owner fixed is essential when the two
operator identities are restricted to the fiber-sum-zero sector.
-/

namespace Erdos85

noncomputable section

/-- The defect cover and the reflexive-complement adjacency cover of a
saturated exterior admit a common owner projection. -/
theorem exists_minimumLayer_saturated_jointCovers
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
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
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
    let P := D.comap (fun z : X => z.1)
    let A := G.comap (fun z : X => z.1)
    let E := minimumLayerExternalNeighborFinset G D c₀
    ∃ owner : X → minimumLayerVertex D c₀,
      (∀ z, z.1 ∈ E (owner z)) ∧
      (∀ {z w}, P.Adj z w → DH.Adj (owner z) (owner w)) ∧
      (∀ (z : X) (b : minimumLayerVertex D c₀),
        DH.Adj (owner z) b →
          ∃! w : X, P.Adj z w ∧ owner w = b) ∧
      (∀ {z w}, A.Adj z w → ¬H.Adj (owner z) (owner w)) ∧
      (∀ (z : X) (b : minimumLayerVertex D c₀),
        ¬H.Adj (owner z) b →
          ∃! w : X, A.Adj z w ∧ owner w = b) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let H := minimumLayerGraph G D c₀
  obtain ⟨ownerD, hmemD, hmapD, hliftD⟩ :=
    exists_minimumLayer_saturated_defectCover
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  obtain ⟨ownerA, hmemA, hmapA, hliftA⟩ :=
    exists_minimumLayer_saturated_exteriorRelationCover
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have howner : ownerA = ownerD := by
    funext z
    obtain ⟨a, ha, haUnique⟩ :=
      minimumLayer_existsUnique_externalOwner_of_saturated
        G hfree hd heven hmin hcard c₀ hregChild hcardChild
          hspos hsd hsat z.2
    exact (haUnique (ownerA z) (hmemA z)).trans
      (haUnique (ownerD z) (hmemD z)).symm
  subst ownerA
  exact ⟨ownerD, hmemD, hmapD, hliftD, hmapA, hliftA⟩

/-- A single normalized owner projection simultaneously reduces the exterior
adjacency and the lifted parent-defect adjacency.  Its complementary sector
has trace minus the number of child vertices. -/
theorem exists_minimumLayer_saturated_jointOwnerOperators
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
    [DecidableEq (minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀)]
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
    let P := (D.comap (fun z : X => z.1)).adjMatrix ℚ
    let A := (G.comap (fun z : X => z.1)).adjMatrix ℚ
    ∃ owner : X → minimumLayerVertex D c₀,
      (∀ z, z.1 ∈ minimumLayerExternalNeighborFinset G D c₀ (owner z)) ∧
      (∀ a, (ownerFiberFinset owner a).card = d - s) ∧
      A * normalizedOwnerProjection owner (d - s) =
        normalizedOwnerProjection owner (d - s) * A ∧
      P * normalizedOwnerProjection owner (d - s) =
        normalizedOwnerProjection owner (d - s) * P ∧
      Matrix.trace (A * (1 - normalizedOwnerProjection owner (d - s))) =
        -(Fintype.card (minimumLayerVertex D c₀) : ℚ) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let H := minimumLayerGraph G D c₀
  let DH := secondOrderDefectGraph H
  let PG := D.comap (fun z : X => z.1)
  let AG := G.comap (fun z : X => z.1)
  let E := minimumLayerExternalNeighborFinset G D c₀
  obtain ⟨owner, hownerMem, hmapP, hliftP, hmapA, hliftA⟩ :=
    exists_minimumLayer_saturated_jointCovers
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  have hownerUnique : ∀ (z : X) (a : minimumLayerVertex D c₀),
      z.1 ∈ E a → a = owner z := by
    intro z a hza
    obtain ⟨q, hq, hqunique⟩ :=
      minimumLayer_existsUnique_externalOwner_of_saturated
        G hfree hd heven hmin hcard c₀ hregChild hcardChild
          hspos hsd hsat z.2
    exact (hqunique a hza).trans (hqunique (owner z) (hownerMem z)).symm
  have huniform : ∀ a, (ownerFiberFinset owner a).card = d - s := by
    intro a
    calc
      (ownerFiberFinset owner a).card = (E a).card := by
        apply Finset.card_bij (fun z _ => z.1)
        · intro z hz
          have hza : owner z = a := (Finset.mem_filter.mp hz).2
          simpa [hza] using hownerMem z
        · intro z₁ _ z₂ _ heq
          exact Subtype.ext heq
        · intro y hy
          have hyOut : y ∉ minimumLayerImageFinset D c₀ :=
            (Finset.mem_sdiff.mp hy).2
          let z : X := ⟨y, hyOut⟩
          have hza : owner z = a := (hownerUnique z a hy).symm
          refine ⟨z, ?_, rfl⟩
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza⟩
      _ = d - s := card_minimumLayerExternalNeighborFinset
        G D c₀ hregParent hregChild a
  have hsymmA : Symmetric (fun a b : minimumLayerVertex D c₀ =>
      ¬H.Adj a b) := by
    intro a b hab hba
    exact hab hba.symm
  have hcommA := adjMatrix_comm_normalizedOwnerProjection_relation
    (K := ℚ) AG (fun a b : minimumLayerVertex D c₀ => ¬H.Adj a b)
      owner hsymmA (d - s) hmapA hliftA
  have hcommP := adjMatrix_comm_normalizedOwnerProjection_relation
    (K := ℚ) PG DH.Adj owner (fun _ _ h => h.symm) (d - s) hmapP hliftP
  let B := relationMatrix (K := ℚ)
    (fun a b : minimumLayerVertex D c₀ => ¬H.Adj a b)
  have hintertwine : AG.adjMatrix ℚ * Matrix.transpose
        (ownerIncidenceMatrix (K := ℚ) owner) =
      Matrix.transpose (ownerIncidenceMatrix (K := ℚ) owner) * B :=
    adjMatrix_mul_ownerIncidence_transpose_relation
      AG (fun a b : minimumLayerVertex D c₀ => ¬H.Adj a b)
        owner hmapA hliftA
  have hm : ((d - s : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.sub_pos_of_lt hsd |>.ne'
  have htrace := trace_mul_complement_normalizedOwnerProjection
    (AG.adjMatrix ℚ) B owner (d - s) hm hintertwine huniform
  have htraceA : Matrix.trace (AG.adjMatrix ℚ) = 0 :=
    adjMatrix_trace_rat_eq_zero AG
  have htraceB : Matrix.trace B =
      (Fintype.card (minimumLayerVertex D c₀) : ℚ) :=
    trace_relationMatrix_not_adj H
  refine ⟨owner, hownerMem, huniform, hcommA, hcommP, ?_⟩
  rw [htrace, htraceA, htraceB, zero_sub]

end

end Erdos85
