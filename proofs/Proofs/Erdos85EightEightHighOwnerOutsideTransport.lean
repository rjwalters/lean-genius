import Proofs.Erdos85EightEightHighOwnerGraphRealization

/-! # Ambient outside vertices indexed by enabled high owners -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

theorem mem_eightEightHighOwnerSym2_iff (e : Fin 64) (v : Fin 16) :
    v ∈ (eightEightHighOwnerSym2 e).toFinset ↔
      eightEightHighOwnerContains e v = true := by
  revert e v
  native_decide

theorem eightEightHighOwnerTarget_not_cycleAdj_of_contains
    (e : Fin 64) (v w : Fin 16)
    (htarget : eightEightHighOwnerTargetContains e v = true)
    (hmem : eightEightHighOwnerContains e w = true) :
    eightEightHighCycleAdj v w = false := by
  revert e v w
  native_decide

noncomputable def highOwnerOutsideEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (hfixed : ∀ e : Fin 64,
      eightEightHighActiveVariable? e = none →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hsub : ∀ a b, R.Adj a b →
      eightEightHighCandidatePair a b = true ∨
        eightEightHighCandidatePair b a = true)
    (modelIso : exteriorPairGraph G c ≃g R) :
    EightEightHighEnabledOwner (eightEightHighCoordinateActive R) ≃
      {x : V // x ∉ c.supp} :=
  let hedge := eightEightHighCoordinateActive_enabled_edge R hfixed
  let hpairCover := eightEightHighCoordinateActive_pairCover R hsub
  let hcover := eightEightHighEnabledOwnerEdge_surjective_of_pairCover
    R (eightEightHighCoordinateActive R) hedge hpairCover
  eightEightHighEnabledOwnerOutsideEquivOfCover
    (exteriorPairGraph G c) R (eightEightHighCoordinateActive R)
      hedge hcover modelIso
      (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
        hcard hinc hqcard hRedges)

noncomputable def outsideHighOwnerIndexEquiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (hfixed : ∀ e : Fin 64,
      eightEightHighActiveVariable? e = none →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hsub : ∀ a b, R.Adj a b →
      eightEightHighCandidatePair a b = true ∨
        eightEightHighCandidatePair b a = true)
    (modelIso : exteriorPairGraph G c ≃g R) :
    {x : V // x ∉ c.supp} ≃
      EightEightHighEnabledOwner (eightEightHighCoordinateActive R) :=
  (highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso).symm

theorem outsidePair_map_highModelIso_eq_ownerSym2
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (hfixed : ∀ e : Fin 64,
      eightEightHighActiveVariable? e = none →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hsub : ∀ a b, R.Adj a b →
      eightEightHighCandidatePair a b = true ∨
        eightEightHighCandidatePair b a = true)
    (modelIso : exteriorPairGraph G c ≃g R)
    (z : {x : V // x ∉ c.supp}) :
    (outsidePair G (secondOrderDefectGraph G) c hcard z).map modelIso =
      eightEightHighOwnerSym2
        ((outsideHighOwnerIndexEquiv G c hcard hinc hqcard hRedges R
          hfixed hsub modelIso z).1) := by
  let hedge := eightEightHighCoordinateActive_enabled_edge R hfixed
  let hpairCover := eightEightHighCoordinateActive_pairCover R hsub
  let hcover := eightEightHighEnabledOwnerEdge_surjective_of_pairCover
    R (eightEightHighCoordinateActive R) hedge hpairCover
  let ownerEdge := eightEightHighEnabledOwnerEdgeEquivOfCover
    R (eightEightHighCoordinateActive R) hedge hcover
  have h := congrArg Subtype.val
    (ownerEdge.apply_symm_apply
      ((edgeFinsetEquivEdgeSet R).symm
        (modelIso.mapEdgeSet
          ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c))
            (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
              hcard hinc hqcard hRedges z)))))
  change ((modelIso.mapEdgeSet
      ((edgeFinsetEquivEdgeSet (exteriorPairGraph G c))
        (outsidePairEdgeEquiv G (secondOrderDefectGraph G) c
          hcard hinc hqcard hRedges z))).1) =
    (eightEightHighEnabledOwnerEdge R
      (eightEightHighCoordinateActive R) hedge
      (outsideHighOwnerIndexEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso z)).1
  exact h.symm

theorem outsideHighOwnerCoordinates_incident_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (hfixed : ∀ e : Fin 64,
      eightEightHighActiveVariable? e = none →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hsub : ∀ a b, R.Adj a b →
      eightEightHighCandidatePair a b = true ∨
        eightEightHighCandidatePair b a = true)
    (modelIso : exteriorPairGraph G c ≃g R)
    (e : EightEightHighEnabledOwner (eightEightHighCoordinateActive R))
    (v : Fin 16) :
    G.Adj (modelIso.symm v).1
        ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
          hfixed hsub modelIso) e).1 ↔
      eightEightHighOwnerContains e.1 v = true := by
  let idx := outsideHighOwnerIndexEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso
  let z := idx.symm e
  have hpair := outsidePair_map_highModelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges R hfixed hsub modelIso z
  have hidx : idx z = e := idx.apply_symm_apply e
  calc
    G.Adj (modelIso.symm v).1 z.1 ↔
        modelIso.symm v ∈
          outsidePair G (secondOrderDefectGraph G) c hcard z := by
      rw [← Sym2.mem_toFinset]
      exact (mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard z (modelIso.symm v)).symm
    _ ↔ v ∈ (outsidePair G (secondOrderDefectGraph G) c hcard z).map
          modelIso := by
      rw [Sym2.mem_map]
      constructor
      · intro hv
        exact ⟨modelIso.symm v, hv, modelIso.apply_symm_apply v⟩
      · rintro ⟨u, hu, huv⟩
        have : u = modelIso.symm v := modelIso.injective
          (huv.trans (modelIso.apply_symm_apply v).symm)
        simpa [this] using hu
    _ ↔ v ∈ eightEightHighOwnerSym2 e.1 := by
      rw [hpair, hidx]
    _ ↔ eightEightHighOwnerContains e.1 v = true := by
      rw [← Sym2.mem_toFinset]
      exact mem_eightEightHighOwnerSym2_iff e.1 v

theorem outsideHighOwnerCoordinates_target_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [DecidablePred (· ∈ c.supp)]
    (hcard : ∀ x : V,
      (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2)
    (hinc : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c))
    (hqcard : Fintype.card {x : V // x ∉ c.supp} = 48)
    (hRedges : (exteriorPairGraph G c).edgeFinset.card = 48)
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (hfixed : ∀ e : Fin 64,
      eightEightHighActiveVariable? e = none →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hsub : ∀ a b, R.Adj a b →
      eightEightHighCandidatePair a b = true ∨
        eightEightHighCandidatePair b a = true)
    (modelIso : exteriorPairGraph G c ≃g R)
    (hcycle : ∀ x y : c.supp,
      G.Adj x.1 y.1 ↔
        eightEightHighCycleAdj (modelIso x).val (modelIso y).val = true)
    (e : EightEightHighEnabledOwner (eightEightHighCoordinateActive R))
    (v : Fin 16)
    (htarget : eightEightHighOwnerTargetContains e.1 v = true) :
    outsideCertificateTarget G c (modelIso.symm v)
        ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
          hfixed hsub modelIso) e) = 1 := by
  classical
  let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso
  let z := out e
  unfold outsideCertificateTarget
  have empty_target (t : Finset V) (ht : t = ∅) : 1 - t.card = 1 := by
    simp [ht]
  apply empty_target
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hwdata : w ∈
      (G.neighborFinset (modelIso.symm v).1 ∩ G.neighborFinset z.1) ∧
      w ∈ c.supp := by
    simpa only [Finset.mem_filter] using hw
  have hwcommon := Finset.mem_inter.mp hwdata.1
  let ws : c.supp := ⟨w, hwdata.2⟩
  have hvw : G.Adj (modelIso.symm v).1 ws.1 :=
    (G.mem_neighborFinset _ _).mp hwcommon.1
  have hzw : G.Adj z.1 ws.1 :=
    (G.mem_neighborFinset _ _).mp hwcommon.2
  have hwinc : eightEightHighOwnerContains e.1 (modelIso ws) = true :=
    (outsideHighOwnerCoordinates_incident_iff
      G c hcard hinc hqcard hRedges R hfixed hsub modelIso
        e (modelIso ws)).mp (by simpa [out, z] using hzw.symm)
  have hfalse := eightEightHighOwnerTarget_not_cycleAdj_of_contains
    e.1 v (modelIso ws) htarget hwinc
  have htrue : eightEightHighCycleAdj v (modelIso ws) = true := by
    simpa using (hcycle (modelIso.symm v) ws).mp hvw
  simp_all

end

end Erdos85

#print axioms Erdos85.outsidePair_map_highModelIso_eq_ownerSym2
