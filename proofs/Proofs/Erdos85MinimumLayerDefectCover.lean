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

noncomputable instance minimumLayerExteriorVertexDecidableEq
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [Fintype D.ConnectedComponent]
    [DecidableEq D.ConnectedComponent]
    (c₀ : D.ConnectedComponent) :
    DecidableEq (minimumLayerExteriorVertex D c₀) := Classical.decEq _

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

end

end Erdos85
