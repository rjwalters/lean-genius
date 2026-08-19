import Proofs.Erdos85EightEightHighOwnerGraphRealization

/-! # Ambient outside vertices indexed by enabled high owners -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 0

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

end

end Erdos85

#print axioms Erdos85.outsidePair_map_highModelIso_eq_ownerSym2
