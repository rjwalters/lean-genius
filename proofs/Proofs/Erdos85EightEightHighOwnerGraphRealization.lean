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

def EightEightHighEnabledOwner
    (active : Fin 64 → Prop) :=
  {e : Fin 64 // eightEightHighOwnerEnabled active e}

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
