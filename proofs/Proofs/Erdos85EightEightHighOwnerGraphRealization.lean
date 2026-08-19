import Proofs.Erdos85EightEightHighOwnerCnfBridgeTerminal

/-!
# Enabled-owner transport for the high eight-plus-eight instance

The high owner table has 64 potential exterior pairs, but only 48 are
realized.  This file isolates that mismatch: an equivalence from enabled
owners to the actual outside vertices transports the ambient exact-service
and C4 laws to the clean finite relation interface used by the certificate.
-/

namespace Erdos85

open SimpleGraph

set_option maxHeartbeats 0

theorem eightEightHighOwnerAt_lt_sixteen (e : Fin 64) :
    (eightEightHighOwnerAt e).1 < 16 ∧
      (eightEightHighOwnerAt e).2 < 16 := by
  revert e
  native_decide

def eightEightHighOwnerFirst (e : Fin 64) : Fin 16 :=
  ⟨(eightEightHighOwnerAt e).1,
    (eightEightHighOwnerAt_lt_sixteen e).1⟩

def eightEightHighOwnerSecond (e : Fin 64) : Fin 16 :=
  ⟨(eightEightHighOwnerAt e).2,
    (eightEightHighOwnerAt_lt_sixteen e).2⟩

def eightEightHighOwnerSym2 (e : Fin 64) : Sym2 (Fin 16) :=
  s(eightEightHighOwnerFirst e, eightEightHighOwnerSecond e)

theorem eightEightHighOwnerSym2_injective :
    Function.Injective eightEightHighOwnerSym2 := by
  native_decide

theorem eightEightHighOwnerAt_injective :
    Function.Injective (fun e : Fin 64 ↦ eightEightHighOwnerAt e) := by
  native_decide

theorem eightEightHighCandidatePair_owner
    (a b : Fin 16)
    (h : eightEightHighCandidatePair a b = true ∨
      eightEightHighCandidatePair b a = true) :
    ∃ e : Fin 64, eightEightHighOwnerSym2 e = s(a, b) := by
  revert a b
  native_decide

theorem eightEightHighCrossIndex?_le_thirtyTwo
    {x y id : Nat} (h : eightEightHighCrossIndex? x y = some id) :
    id ≤ 32 := by
  simp only [eightEightHighCrossIndex?] at h
  split at h
  · obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hklt, _, _⟩ := List.idxOf?_eq_some_iff.mp hk
    simp only [eightEightHighCrossCandidates_size] at hklt
    omega
  · contradiction

/-- A bounded cross variable identifies the same candidate in the cross
table and the full 64-owner table. -/
theorem eightEightHighCrossIndex?_owner
    (x y : Fin 8) (id : Fin 33)
    (h : eightEightHighCrossIndex? x y = some id) :
    ∃ e : Fin 64,
      eightEightHighOwnerAt e = (x.val, 8 + y.val) ∧
      eightEightHighActiveVariable? e = some id := by
  revert x y id
  native_decide

theorem eightEightHighOwnerVal_crossIndex_iff
    (active : Fin 64 → Prop) (X : Fin 64 → Fin 64 → Prop)
    [DecidablePred active] [DecidableRel X]
    {x y id : Nat} (hx : x < 8) (hy : y < 8)
    (hidx : eightEightHighCrossIndex? x y = some id) :
    eightEightHighOwnerValOfRelations active X id = true ↔
      ∃ e : Fin 64,
        eightEightHighOwnerAt e = (x, 8 + y) ∧ active e := by
  let idf : Fin 33 := ⟨id, by
    exact Nat.lt_succ_iff.mpr (eightEightHighCrossIndex?_le_thirtyTwo hidx)⟩
  obtain ⟨e, heowner, hevar⟩ :=
    eightEightHighCrossIndex?_owner ⟨x, hx⟩ ⟨y, hy⟩ idf (by
      simpa [idf] using hidx)
  constructor
  · intro hval
    exact ⟨e, by simpa using heowner,
      eightEightHighOwnerActive_of_val_true active X
        (by simpa [idf] using hevar) hval⟩
  · rintro ⟨f, hfowner, hfactive⟩
    have hef : e = f := eightEightHighOwnerAt_injective
      (heowner.trans hfowner.symm)
    subst f
    exact eightEightHighOwnerVal_active_true_of active X
      (by simpa [idf] using hevar) hfactive

def eightEightHighCoordinateActive
    (R : SimpleGraph (Fin 16)) (e : Fin 64) : Prop :=
  R.Adj (eightEightHighOwnerFirst e) (eightEightHighOwnerSecond e)

instance (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj] :
    DecidablePred (eightEightHighCoordinateActive R) := by
  intro e
  unfold eightEightHighCoordinateActive
  exact inferInstance

theorem eightEightHighCoordinateActive_enabled_edge
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (hfixed : ∀ e : Fin 64,
      eightEightHighActiveVariable? e = none →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e)) :
    ∀ e : Fin 64,
      eightEightHighOwnerEnabled (eightEightHighCoordinateActive R) e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e) := by
  intro e he
  unfold eightEightHighOwnerEnabled at he
  cases hvar : eightEightHighActiveVariable? e with
  | none => exact hfixed e hvar
  | some id => simpa [hvar, eightEightHighCoordinateActive] using he

theorem eightEightHighCoordinateActive_pairCover
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (hsub : ∀ a b, R.Adj a b →
      eightEightHighCandidatePair a b = true ∨
        eightEightHighCandidatePair b a = true) :
    ∀ a b, R.Adj a b →
      ∃ e : Fin 64,
        eightEightHighOwnerEnabled (eightEightHighCoordinateActive R) e ∧
          eightEightHighOwnerSym2 e = s(a, b) := by
  intro a b hab
  obtain ⟨e, he⟩ := eightEightHighCandidatePair_owner a b (hsub a b hab)
  refine ⟨e, ?_, he⟩
  unfold eightEightHighOwnerEnabled
  cases hvar : eightEightHighActiveVariable? e with
  | none => trivial
  | some id =>
      unfold eightEightHighCoordinateActive
      have hp : s(eightEightHighOwnerFirst e,
          eightEightHighOwnerSecond e) = s(a, b) := by
        simpa [eightEightHighOwnerSym2] using he
      rcases Sym2.eq_iff.mp hp with hp | hp
      · simpa [hp.1, hp.2] using hab
      · simpa [hp.1, hp.2] using hab.symm

theorem eightEightHighOwnerVal_crossIndex_coordinate_iff
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (X : Fin 64 → Fin 64 → Prop) [DecidableRel X]
    {x y id : Nat} (hx : x < 8) (hy : y < 8)
    (hidx : eightEightHighCrossIndex? x y = some id) :
    eightEightHighOwnerValOfRelations
        (eightEightHighCoordinateActive R) X id = true ↔
      R.Adj ⟨x, by omega⟩ ⟨8 + y, by omega⟩ := by
  rw [eightEightHighOwnerVal_crossIndex_iff
    (eightEightHighCoordinateActive R) X hx hy hidx]
  constructor
  · rintro ⟨e, heowner, heactive⟩
    have hfirst : eightEightHighOwnerFirst e = ⟨x, by omega⟩ := by
      apply Fin.ext
      simpa [eightEightHighOwnerFirst] using congrArg Prod.fst heowner
    have hsecond : eightEightHighOwnerSecond e = ⟨8 + y, by omega⟩ := by
      apply Fin.ext
      simpa [eightEightHighOwnerSecond] using congrArg Prod.snd heowner
    simpa [eightEightHighCoordinateActive, hfirst, hsecond] using heactive
  · intro hR
    let idf : Fin 33 := ⟨id, by
      exact Nat.lt_succ_iff.mpr
        (eightEightHighCrossIndex?_le_thirtyTwo hidx)⟩
    obtain ⟨e, heowner, _hevar⟩ :=
      eightEightHighCrossIndex?_owner ⟨x, hx⟩ ⟨y, hy⟩ idf (by
        simpa [idf] using hidx)
    refine ⟨e, by simpa using heowner, ?_⟩
    have hfirst : eightEightHighOwnerFirst e = ⟨x, by omega⟩ := by
      apply Fin.ext
      simpa [eightEightHighOwnerFirst] using congrArg Prod.fst heowner
    have hsecond : eightEightHighOwnerSecond e = ⟨8 + y, by omega⟩ := by
      apply Fin.ext
      simpa [eightEightHighOwnerSecond] using congrArg Prod.snd heowner
    simpa [eightEightHighCoordinateActive, hfirst, hsecond] using hR

def EightEightHighEnabledOwner
    (active : Fin 64 → Prop) :=
  {e : Fin 64 // eightEightHighOwnerEnabled active e}

instance (active : Fin 64 → Prop) [DecidablePred active] :
    DecidablePred (eightEightHighOwnerEnabled active) := by
  intro e
  unfold eightEightHighOwnerEnabled
  split <;> infer_instance

noncomputable instance (active : Fin 64 → Prop) :
    Fintype (EightEightHighEnabledOwner active) := by
  letI : Finite (EightEightHighEnabledOwner active) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

/-- An enabled candidate as an edge of a realized `Fin 16` exterior-pair
graph. -/
def eightEightHighEnabledOwnerEdge
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (active : Fin 64 → Prop)
    (hedge : ∀ e : Fin 64,
      eightEightHighOwnerEnabled active e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (e : EightEightHighEnabledOwner active) : R.edgeFinset :=
  ⟨eightEightHighOwnerSym2 e.1, by
    rw [SimpleGraph.mem_edgeFinset]
    exact hedge e.1 e.2⟩

theorem eightEightHighEnabledOwnerEdge_injective
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (active : Fin 64 → Prop)
    (hedge : ∀ e : Fin 64,
      eightEightHighOwnerEnabled active e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e)) :
    Function.Injective
      (eightEightHighEnabledOwnerEdge R active hedge) := by
  intro e f hef
  apply Subtype.ext
  apply eightEightHighOwnerSym2_injective
  exact congrArg Subtype.val hef

theorem eightEightHighEnabledOwnerEdge_surjective_of_pairCover
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (active : Fin 64 → Prop)
    (hedge : ∀ e : Fin 64,
      eightEightHighOwnerEnabled active e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hcover : ∀ a b, R.Adj a b →
      ∃ e : Fin 64,
        eightEightHighOwnerEnabled active e ∧
          eightEightHighOwnerSym2 e = s(a, b)) :
    Function.Surjective
      (eightEightHighEnabledOwnerEdge R active hedge) := by
  rintro ⟨p, hp⟩
  induction p using Sym2.inductionOn with
  | _ a b =>
      have hab : R.Adj a b := by
        simpa only [SimpleGraph.mem_edgeFinset,
          SimpleGraph.mem_edgeSet] using hp
      obtain ⟨e, he, heq⟩ := hcover a b hab
      refine ⟨⟨e, he⟩, Subtype.ext ?_⟩
      exact heq

/-- Equal cardinality upgrades the typed owner-table injection to the exact
enabled-owner/exterior-edge equivalence needed by the ambient transport. -/
noncomputable def eightEightHighEnabledOwnerEdgeEquiv
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (active : Fin 64 → Prop) [DecidablePred active]
    (hedge : ∀ e : Fin 64,
      eightEightHighOwnerEnabled active e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (henabledCard : Fintype.card (EightEightHighEnabledOwner active) = 48)
    (hRedges : R.edgeFinset.card = 48) :
    EightEightHighEnabledOwner active ≃ R.edgeFinset :=
  Equiv.ofBijective (eightEightHighEnabledOwnerEdge R active hedge)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨
      eightEightHighEnabledOwnerEdge_injective R active hedge, by
        rw [henabledCard, Fintype.card_coe]
        exact hRedges.symm⟩)

/-- Surjective candidate coverage is an alternative to the cardinality
argument and is often easier to prove directly from shore coordinates. -/
noncomputable def eightEightHighEnabledOwnerEdgeEquivOfCover
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (active : Fin 64 → Prop)
    (hedge : ∀ e : Fin 64,
      eightEightHighOwnerEnabled active e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hcover : Function.Surjective
      (eightEightHighEnabledOwnerEdge R active hedge)) :
    EightEightHighEnabledOwner active ≃ R.edgeFinset :=
  Equiv.ofBijective (eightEightHighEnabledOwnerEdge R active hedge)
    ⟨eightEightHighEnabledOwnerEdge_injective R active hedge, hcover⟩

/-- Compose the enabled-owner enumeration with a graph isomorphism and an
independent outside-vertex/edge equivalence.  This is the exact direction
required by `eightEightHighOwnerServiceSemantics_of_enabledEquiv`. -/
noncomputable def eightEightHighEnabledOwnerOutsideEquiv
    {E : Type*} [Fintype E] [DecidableEq E]
    (S : SimpleGraph E) [DecidableRel S.Adj]
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (active : Fin 64 → Prop) [DecidablePred active]
    (hedge : ∀ e : Fin 64,
      eightEightHighOwnerEnabled active e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (henabledCard : Fintype.card (EightEightHighEnabledOwner active) = 48)
    (hRedges : R.edgeFinset.card = 48)
    (modelIso : S ≃g R)
    (outsideEdge : E ≃ S.edgeFinset) :
    EightEightHighEnabledOwner active ≃ E :=
  (eightEightHighEnabledOwnerEdgeEquiv R active hedge
      henabledCard hRedges).trans
    ((edgeFinsetEquivEdgeSet R).trans
      (modelIso.symm.mapEdgeSet.trans
        ((edgeFinsetEquivEdgeSet S).symm.trans outsideEdge.symm)))

noncomputable def eightEightHighEnabledOwnerOutsideEquivOfCover
    {E : Type*} [Fintype E] [DecidableEq E]
    (S : SimpleGraph E) [DecidableRel S.Adj]
    (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (active : Fin 64 → Prop)
    (hedge : ∀ e : Fin 64,
      eightEightHighOwnerEnabled active e →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (hcover : Function.Surjective
      (eightEightHighEnabledOwnerEdge R active hedge))
    (modelIso : S ≃g R)
    (outsideEdge : E ≃ S.edgeFinset) :
    EightEightHighEnabledOwner active ≃ E :=
  (eightEightHighEnabledOwnerEdgeEquivOfCover R active hedge hcover).trans
    ((edgeFinsetEquivEdgeSet R).trans
      (modelIso.symm.mapEdgeSet.trans
        ((edgeFinsetEquivEdgeSet S).symm.trans outsideEdge.symm)))

def eightEightHighRealizedRelation
    {E : Type*} (active : Fin 64 → Prop) (C : SimpleGraph E)
    (idx : EightEightHighEnabledOwner active ≃ E)
    (e f : Fin 64) : Prop :=
  ∃ he : eightEightHighOwnerEnabled active e,
    ∃ hf : eightEightHighOwnerEnabled active f,
      C.Adj (idx ⟨e, he⟩) (idx ⟨f, hf⟩)

theorem eightEightHighRealizedRelation_symm
    {E : Type*} (active : Fin 64 → Prop) (C : SimpleGraph E)
    (idx : EightEightHighEnabledOwner active ≃ E) :
    ∀ e f, eightEightHighRealizedRelation active C idx e f →
      eightEightHighRealizedRelation active C idx f e := by
  rintro e f ⟨he, hf, hef⟩
  exact ⟨hf, he, hef.symm⟩

theorem eightEightHighRealizedRelation_irrefl
    {E : Type*} (active : Fin 64 → Prop) (C : SimpleGraph E)
    (idx : EightEightHighEnabledOwner active ≃ E) :
    ∀ e, ¬ eightEightHighRealizedRelation active C idx e e := by
  rintro e ⟨he, _he', hee⟩
  exact C.loopless.irrefl (idx ⟨e, he⟩) hee

theorem eightEightHighRealizedRelation_coordinate_endpoints_active
    {E : Type*} (R : SimpleGraph (Fin 16)) [DecidableRel R.Adj]
    (C : SimpleGraph E)
    (hfixed : ∀ e : Fin 64,
      eightEightHighActiveVariable? e = none →
        R.Adj (eightEightHighOwnerFirst e)
          (eightEightHighOwnerSecond e))
    (idx : EightEightHighEnabledOwner
      (eightEightHighCoordinateActive R) ≃ E) :
    ∀ e f,
      eightEightHighRealizedRelation
          (eightEightHighCoordinateActive R) C idx e f →
        eightEightHighCoordinateActive R e ∧
          eightEightHighCoordinateActive R f := by
  rintro e f ⟨he, hf, _⟩
  exact ⟨eightEightHighCoordinateActive_enabled_edge R hfixed e he,
    eightEightHighCoordinateActive_enabled_edge R hfixed f hf⟩

/-- Transport an ambient outside-vertex semantic package through an
enabled-owner equivalence.  The two target hypotheses are the exact
one/zero coordinate rewrites; the incidence hypothesis identifies the
owner endpoints. -/
theorem eightEightHighOwnerServiceSemantics_of_enabledEquiv
    {U E : Type*} [Fintype E]
    (active : Fin 64 → Prop)
    (C : SimpleGraph E)
    (incident : U → E → Prop)
    (target : U → E → Nat)
    (coord : U ≃ Fin 16)
    (h : OutsideCClauseSemantics C incident target)
    (idx : EightEightHighEnabledOwner active ≃ E)
    (htargetOne : ∀ (e : Fin 64)
      (he : eightEightHighOwnerEnabled active e) (v : Fin 16),
      eightEightHighOwnerTargetContains e v = true →
        target (coord.symm v) (idx ⟨e, he⟩) = 1)
    (htargetZero : ∀ (e : Fin 64)
      (he : eightEightHighOwnerEnabled active e) (v : Fin 16),
      eightEightHighOwnerTargetContains e v = false →
        target (coord.symm v) (idx ⟨e, he⟩) = 0)
    (hincident : ∀ (e : Fin 64)
      (he : eightEightHighOwnerEnabled active e) (v : Fin 16),
      incident (coord.symm v) (idx ⟨e, he⟩) ↔
        eightEightHighOwnerContains e v = true)
    (hintersect : ∀ (e f : Fin 64),
      e ≠ f → eightEightHighOwnersIntersect e f = true →
      ∀ he hf k,
        C.Adj (idx ⟨e, he⟩) k → C.Adj (idx ⟨f, hf⟩) k → False) :
    EightEightHighOwnerServiceSemantics active
      (eightEightHighRealizedRelation active C idx) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro e v he htarget
    obtain ⟨z, hez, hvz⟩ := h.one_service_exists
      (coord.symm v) (idx ⟨e, he⟩) (htargetOne e he v htarget)
    let f := idx.symm z
    refine ⟨f.1, ⟨he, f.2, ?_⟩, ?_⟩
    · simpa [f] using hez
    · exact (hincident f.1 f.2 v).mp (by simpa [f] using hvz)
  · intro e v f g hef hfv heg hgv
    obtain ⟨he, hf, hefC⟩ := hef
    obtain ⟨_he', hg, hegC⟩ := heg
    have hfg : idx ⟨f, hf⟩ = idx ⟨g, hg⟩ :=
      h.one_service_unique (coord.symm v) (idx ⟨e, he⟩)
        (htargetOne e he v (by
          -- A realized service forces the target-one case supplied to the
          -- semantic package; the caller's service theorem is only used at
          -- generated target positions.
          by_cases ht : eightEightHighOwnerTargetContains e v = true
          · exact ht
          · have hz := htargetZero e he v (Bool.eq_false_iff.mpr ht)
            have hzero := h.zero_service (coord.symm v) (idx ⟨e, he⟩) hz
              (idx ⟨f, hf⟩) hefC
              ((hincident f hf v).mpr hfv)
            exact False.elim hzero))
        (idx ⟨f, hf⟩) (idx ⟨g, hg⟩) hefC
        ((hincident f hf v).mpr hfv) hegC
        ((hincident g hg v).mpr hgv)
    exact congrArg Subtype.val (idx.injective hfg)
  · intro e v f htarget hfv hef
    obtain ⟨he, hf, hefC⟩ := hef
    exact h.zero_service (coord.symm v) (idx ⟨e, he⟩)
      (htargetZero e he v htarget) (idx ⟨f, hf⟩) hefC
      ((hincident f hf v).mpr hfv)
  · intro e f hef hinter k hek hfk
    obtain ⟨he, hk, hekC⟩ := hek
    obtain ⟨hf, _hk', hfkC⟩ := hfk
    exact hintersect e f hef hinter he hf (idx ⟨k, hk⟩) hekC hfkC
  · intro e f hef k l hkl hek hfk hel hfl
    obtain ⟨he, hk, hekC⟩ := hek
    obtain ⟨hf, _hk', hfkC⟩ := hfk
    obtain ⟨_he', hl, helC⟩ := hel
    obtain ⟨_hf', _hl', hflC⟩ := hfl
    apply h.no_two_common (idx ⟨e, he⟩) (idx ⟨f, hf⟩)
      (idx ⟨k, hk⟩) (idx ⟨l, hl⟩)
    · intro hEF
      exact hef (congrArg Subtype.val (idx.injective hEF))
    · intro hKL
      exact hkl (congrArg Subtype.val (idx.injective hKL))
    · exact hekC
    · exact hfkC
    · exact helC
    · exact hflC

end Erdos85

#print axioms Erdos85.eightEightHighOwnerServiceSemantics_of_enabledEquiv
