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

theorem eightEightHighOwnerTarget_false_witness
    (e : Fin 64) (v : Fin 16)
    (h : eightEightHighOwnerTargetContains e v = false) :
    ∃ w : Fin 16, eightEightHighOwnerContains e w = true ∧
      eightEightHighCycleAdj w v = true := by
  revert e v
  native_decide

theorem eightEightHighOwnersIntersect_iff_sym2 (e f : Fin 64) :
    eightEightHighOwnersIntersect e f = true ↔
      ∃ v : Fin 16, v ∈ eightEightHighOwnerSym2 e ∧
        v ∈ eightEightHighOwnerSym2 f := by
  revert e f
  native_decide

theorem eightEightHighOwnerCompatible_iff_endpoints (e f : Fin 64) :
    eightEightHighOwnerCompatible e f = true ↔
      e ≠ f ∧ ∀ u v : Fin 16,
        u ∈ eightEightHighOwnerSym2 e →
        v ∈ eightEightHighOwnerSym2 f →
        eightEightHighCycleAdj u v = false := by
  revert e f
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

theorem outsideHighOwnerCoordinates_internal_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
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
    (e f : EightEightHighEnabledOwner (eightEightHighCoordinateActive R))
    (v : Fin 16)
    (htarget : eightEightHighOwnerTargetContains e.1 v = false)
    (hfcontains : eightEightHighOwnerContains f.1 v = true)
    (hef : G.Adj
      ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso) e).1
      ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso) f).1) : False := by
  let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso
  let ze := out e
  let zf := out f
  obtain ⟨w, hecontains, hwvCycle⟩ :=
    eightEightHighOwnerTarget_false_witness e.1 v htarget
  let wi : c.supp := modelIso.symm w
  let vi : c.supp := modelIso.symm v
  have hzew : G.Adj ze.1 wi.1 := by
    exact (outsideHighOwnerCoordinates_incident_iff
      G c hcard hinc hqcard hRedges R hfixed hsub modelIso e w).mpr
        hecontains |>.symm
  have hzfv : G.Adj zf.1 vi.1 := by
    exact (outsideHighOwnerCoordinates_incident_iff
      G c hcard hinc hqcard hRedges R hfixed hsub modelIso f v).mpr
        hfcontains |>.symm
  have hwv : G.Adj wi.1 vi.1 := by
    exact (hcycle wi vi).mpr (by simpa [wi, vi] using hwvCycle)
  have hzevi : ze.1 ≠ vi.1 := fun h => ze.2 (h ▸ vi.2)
  have hzfwi : zf.1 ≠ wi.1 := fun h => zf.2 (h ▸ wi.2)
  have hwvi : wi.1 ≠ vi.1 := fun h => G.loopless.irrefl wi.1 (h ▸ hwv)
  have hefd : ze.1 ≠ zf.1 := fun h => G.loopless.irrefl ze.1 (h ▸ hef)
  have hef' : G.Adj ze.1 zf.1 := by
    simpa [ze, zf, out] using hef
  apply hfree
  refine ⟨![ze.1, wi.1, vi.1, zf.1], ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;>
      simp_all [C4, SimpleGraph.Adj.symm]

theorem outsideHighOwnerCoordinates_intersecting_no_common
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
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
    (e f : EightEightHighEnabledOwner (eightEightHighCoordinateActive R))
    (hef : e.1 ≠ f.1)
    (hintersect : eightEightHighOwnersIntersect e.1 f.1 = true)
    (k : {x : V // x ∉ c.supp})
    (hek : G.Adj
      ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso) e).1 k.1)
    (hfk : G.Adj
      ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso) f).1 k.1) : False := by
  let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso
  let a := out e
  let b := out f
  have hab : a ≠ b := by
    intro h
    apply hef
    exact congrArg Subtype.val (out.injective h)
  obtain ⟨v, hve, hvf⟩ :=
    (eightEightHighOwnersIntersect_iff_sym2 e.1 f.1).mp hintersect
  let u : c.supp := modelIso.symm v
  have hpaira := outsidePair_map_highModelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges R hfixed hsub modelIso a
  have hpairb := outsidePair_map_highModelIso_eq_ownerSym2
    G c hcard hinc hqcard hRedges R hfixed hsub modelIso b
  have hia : outsideHighOwnerIndexEquiv G c hcard hinc hqcard hRedges R
      hfixed hsub modelIso a = e := by
    change out.symm a = e
    exact out.symm_apply_apply e
  have hib : outsideHighOwnerIndexEquiv G c hcard hinc hqcard hRedges R
      hfixed hsub modelIso b = f := by
    change out.symm b = f
    exact out.symm_apply_apply f
  have hua : u ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard a).toFinset := by
    rw [Sym2.mem_toFinset]
    have hvmap : v ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard a).map modelIso := by
      rw [hpaira, hia]
      exact hve
    rw [Sym2.mem_map] at hvmap
    obtain ⟨w, hw, hwv⟩ := hvmap
    have hwu : w = u := modelIso.injective
      (hwv.trans (modelIso.apply_symm_apply v).symm)
    simpa [hwu] using hw
  have hub : u ∈
      (outsidePair G (secondOrderDefectGraph G) c hcard b).toFinset := by
    rw [Sym2.mem_toFinset]
    have hvmap : v ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard b).map modelIso := by
      rw [hpairb, hib]
      exact hvf
    rw [Sym2.mem_map] at hvmap
    obtain ⟨w, hw, hwv⟩ := hvmap
    have hwu : w = u := modelIso.injective
      (hwv.trans (modelIso.apply_symm_apply v).symm)
    simpa [hwu] using hw
  apply outsidePair_intersects_no_exterior_common
    G hfree c hcard a b k hab ⟨u, hua, hub⟩
  · simpa [out, a] using hek
  · simpa [out, b] using hfk

/-- Every ambient adjacency transported to enabled high owners survives the
generator's endpoint-compatibility filter. -/
theorem outsideHighOwnerCoordinates_compatible
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
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
    (e f : EightEightHighEnabledOwner (eightEightHighCoordinateActive R))
    (hef : G.Adj
      ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso) e).1
      ((highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso) f).1) :
    eightEightHighOwnerCompatible e.1 f.1 = true := by
  let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso
  let a := out e
  let b := out f
  have hab : G.Adj a.1 b.1 := by
    simpa [a, b, out] using hef
  apply (eightEightHighOwnerCompatible_iff_endpoints e.1 f.1).mpr
  refine ⟨?_, ?_⟩
  · intro h
    have hef' : e = f := Subtype.ext h
    subst f
    exact G.loopless.irrefl a.1 hab
  · intro u v hue hvf
    let us : c.supp := modelIso.symm u
    let vs : c.supp := modelIso.symm v
    have hua : us ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard a).toFinset := by
      apply (mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard a us).mpr
      have hincu := (outsideHighOwnerCoordinates_incident_iff
        G c hcard hinc hqcard hRedges R hfixed hsub modelIso e u).mpr
          ((mem_eightEightHighOwnerSym2_iff e.1 u).mp
            (Sym2.mem_toFinset.mpr hue))
      simpa [a, out, us] using hincu
    have hvb : vs ∈
        (outsidePair G (secondOrderDefectGraph G) c hcard b).toFinset := by
      apply (mem_outsidePair_toFinset_iff_adj
        G (secondOrderDefectGraph G) c hcard b vs).mpr
      have hincv := (outsideHighOwnerCoordinates_incident_iff
        G c hcard hinc hqcard hRedges R hfixed hsub modelIso f v).mpr
          ((mem_eightEightHighOwnerSym2_iff f.1 v).mp
            (Sym2.mem_toFinset.mpr hvf))
      simpa [b, out, vs] using hincv
    have hnot := adjacent_outsidePair_endpoint_not_adj
      G hfree c hcard a b hab us vs hua hvb
    cases hcv : eightEightHighCycleAdj u v with
    | false => rfl
    | true =>
      exfalso
      apply hnot
      apply (hcycle us vs).mpr
      simpa [us, vs] using hcv

/-- The ambient outside graph, indexed by enabled high owners, supplies all
five guarded service and C4 laws used by the checked high-owner terminal. -/
theorem highEightOwnerServiceSemantics_of_modelIso
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [hmem : DecidablePred (· ∈ c.supp)]
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
        eightEightHighCycleAdj (modelIso x).val (modelIso y).val = true) :
    EightEightHighOwnerServiceSemantics
      (eightEightHighCoordinateActive R)
      (eightEightHighRealizedRelation
        (eightEightHighCoordinateActive R) (G.induce c.suppᶜ)
        (highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
          hfixed hsub modelIso)) := by
  let active := eightEightHighCoordinateActive R
  let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso
  have hambient : OutsideCClauseSemantics (G.induce c.suppᶜ)
      (fun u z ↦ G.Adj u.1 z.1) (outsideCertificateTarget G c) := by
    let canonicalMem : DecidablePred (· ∈ c.supp) :=
      (secondOrderDefectGraph G).instDecidableMemSupp c
    let canonicalOutside : Fintype {x : V // x ∉ c.supp} :=
      @Subtype.fintype V (fun x ↦ x ∈ c.suppᶜ)
        (fun x ↦ @Set.decidableCompl V c.supp x (canonicalMem x)) inferInstance
    let callerOutside : Fintype {x : V // x ∉ c.supp} :=
      @Subtype.fintype V (fun x ↦ x ∈ c.suppᶜ)
        (fun x ↦ @Set.decidableCompl V c.supp x (hmem x)) inferInstance
    have h : @OutsideCClauseSemantics c.supp {x : V // x ∉ c.supp}
        canonicalOutside (G.induce c.suppᶜ) (fun u z ↦ G.Adj u.1 z.1)
        (outsideCertificateTarget G c) := by
      exact outsideCClauseSemantics_of_ambient G hfree c
    exact @OutsideCClauseSemantics.mk _ _ callerOutside _ _ _
      (@OutsideCClauseSemantics.zero_service _ _ canonicalOutside _ _ _ h)
      (@OutsideCClauseSemantics.one_service_exists _ _ canonicalOutside _ _ _ h)
      (@OutsideCClauseSemantics.one_service_unique _ _ canonicalOutside _ _ _ h)
      (@OutsideCClauseSemantics.no_two_common _ _ canonicalOutside _ _ _ h)
  apply eightEightHighOwnerServiceSemantics_of_enabledEquiv
    active (G.induce c.suppᶜ)
    (fun u z ↦ G.Adj u.1 z.1)
    (outsideCertificateTarget G c)
    modelIso.toEquiv
    hambient out
  · intro e he v htarget
    exact outsideHighOwnerCoordinates_target_eq_one
      G c hcard hinc hqcard hRedges R hfixed hsub modelIso hcycle
        ⟨e, he⟩ v htarget
  · intro e he v
    exact outsideHighOwnerCoordinates_incident_iff
      G c hcard hinc hqcard hRedges R hfixed hsub modelIso ⟨e, he⟩ v
  · intro e he v f hf htarget hfcontains hef
    exact outsideHighOwnerCoordinates_internal_zero
      G hfree c hcard hinc hqcard hRedges R hfixed hsub modelIso hcycle
        ⟨e, he⟩ ⟨f, hf⟩ v htarget hfcontains hef
  · intro e f hef hintersect he hf k hek hfk
    exact outsideHighOwnerCoordinates_intersecting_no_common
      G hfree c hcard hinc hqcard hRedges R hfixed hsub modelIso
        ⟨e, he⟩ ⟨f, hf⟩ hef hintersect k hek hfk

noncomputable def eightEightHighOwnerClassicalVal
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop) (id : Nat) : Bool :=
  @eightEightHighOwnerValOfRelations active X
    (Classical.decPred active) (Classical.decRel X) id

/-- Graph-facing checked high-`8+8` terminal.  All ambient service, C4,
compatibility, symmetry, irreﬂexivity, and endpoint-activity laws are
internal; only the two cross-block arithmetic laws remain as inputs. -/
theorem highEightOwnerModel_false_of_cross_laws
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    [hmem : DecidablePred (· ∈ c.supp)]
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
    (htwo :
      let active := eightEightHighCoordinateActive R
      let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso
      let X := eightEightHighRealizedRelation active (G.induce c.suppᶜ) out
      ∀ left z, z < 8 →
        ((eightEightHighCrossFiberIds left z).filter fun id =>
          eightEightHighOwnerClassicalVal active X id = true).card = 2)
    (hbalance :
      let active := eightEightHighCoordinateActive R
      let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
        hfixed hsub modelIso
      let X := eightEightHighRealizedRelation active (G.induce c.suppᶜ) out
      ∀ x y a b d e,
        eightEightHighCrossIndex? ((x + 7) % 8) y = some a →
        eightEightHighCrossIndex? ((x + 1) % 8) y = some b →
        eightEightHighCrossIndex? x ((y + 1) % 8) = some d →
        eightEightHighCrossIndex? x ((y + 7) % 8) = some e →
        (eightEightHighOwnerClassicalVal active X a).toNat +
            (eightEightHighOwnerClassicalVal active X b).toNat =
          (eightEightHighOwnerClassicalVal active X d).toNat +
            (eightEightHighOwnerClassicalVal active X e).toNat) : False := by
  classical
  let active := eightEightHighCoordinateActive R
  let C := G.induce c.suppᶜ
  let out := highOwnerOutsideEquiv G c hcard hinc hqcard hRedges R
    hfixed hsub modelIso
  let X := eightEightHighRealizedRelation active C out
  letI : DecidablePred active := Classical.decPred active
  letI : DecidableRel X := Classical.decRel X
  have hsem : EightEightHighOwnerServiceSemantics active X := by
    simpa [active, C, out, X] using
      highEightOwnerServiceSemantics_of_modelIso
        G hfree c hcard hinc hqcard hRedges R hfixed hsub modelIso hcycle
  apply eightEightHighOwnerRelations_false active X hsem
  · exact eightEightHighRealizedRelation_symm active C out
  · exact eightEightHighRealizedRelation_irrefl active C out
  · rintro e f ⟨he, hf, hef⟩
    exact outsideHighOwnerCoordinates_compatible
      G hfree c hcard hinc hqcard hRedges R hfixed hsub modelIso hcycle
        ⟨e, he⟩ ⟨f, hf⟩ hef
  · exact eightEightHighRealizedRelation_coordinate_endpoints_active
      R C hfixed out
  · simpa [eightEightHighOwnerClassicalVal, active, C, out, X] using htwo
  · simpa [eightEightHighOwnerClassicalVal, active, C, out, X] using hbalance

end

end Erdos85

#print axioms Erdos85.outsidePair_map_highModelIso_eq_ownerSym2
#print axioms Erdos85.outsideHighOwnerCoordinates_compatible
#print axioms Erdos85.highEightOwnerServiceSemantics_of_modelIso
#print axioms Erdos85.highEightOwnerModel_false_of_cross_laws
