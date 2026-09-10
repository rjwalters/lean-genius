import Proofs.Erdos85ThreeHighExternalSearchCertificate

namespace Erdos85
set_option maxRecDepth 100000
attribute [local irreducible] threeHighCrossDomain

abbrev ThreeHighJointExternalSearch :=
  (Fin 15 → Fin 15 → Bool) → (Fin 8 → Fin 8 → Bool) → Bool

/-- Completeness for actual joint witnesses; no arbitrary acceptance callback is required. -/
def ThreeHighJointExternalSearchSound (search : ThreeHighJointExternalSearch) : Prop :=
  ∀ U R cross, cross ∈ threeHighCrossDomain U R →
    encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true →
    ThreeHighJointWitness (threeHighEmptyAdj U R cross) → search U R = true

def threeHighJointExternalOf (search : ThreeHighExternalSearch)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) : ThreeHighJointExternalSearch :=
  fun U R => search U R (fun cross => accept (threeHighEmptyAdj U R cross))

theorem threeHighJointExternalOf_sound (search : ThreeHighExternalSearch)
    (hsearch : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (haccept : ThreeHighTerminalSound accept) :
    ThreeHighJointExternalSearchSound (threeHighJointExternalOf search accept) := by
  intro U R cross hc he hj
  exact hsearch U R _ cross hc he (haccept _ hj)

/-- A gate may choose another cross, but must retain a joint witness at the same U/R pair. -/
def ThreeHighJointCrossGateComplete
    (gate : (Fin 15 → Fin 15 → Bool) → (Fin 8 → Fin 8 → Bool) → ThreeHighCross → Bool) : Prop :=
  ∀ U R cross, cross ∈ threeHighCrossDomain U R →
    encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true →
    ThreeHighJointWitness (threeHighEmptyAdj U R cross) →
    ∃ c : ThreeHighCross, c ∈ threeHighCrossDomain U R ∧
      encodedExternalBlockCap (threeHighEmptyAdj U R c) threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj U R c) ∧ gate U R c = true

def threeHighGatedJointExternal (search : ThreeHighExternalSearch)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool)
    (gate : (Fin 15 → Fin 15 → Bool) → (Fin 8 → Fin 8 → Bool) → ThreeHighCross → Bool) :
    ThreeHighJointExternalSearch :=
  fun U R => search U R (fun cross => gate U R cross && accept (threeHighEmptyAdj U R cross))

theorem threeHighGatedJointExternal_sound (search : ThreeHighExternalSearch)
    (hsearch : ThreeHighExternalSearchSound search)
    (accept : (Fin 24 → Fin 24 → Bool) → Bool) (haccept : ThreeHighTerminalSound accept)
    (gate : (Fin 15 → Fin 15 → Bool) → (Fin 8 → Fin 8 → Bool) → ThreeHighCross → Bool)
    (hgate : ThreeHighJointCrossGateComplete gate) :
    ThreeHighJointExternalSearchSound (threeHighGatedJointExternal search accept gate) := by
  intro U R cross hc he hj
  obtain ⟨c,hc',he',hj',hg⟩ := hgate U R cross hc he hj
  apply hsearch U R _ c hc' he'
  simp only [hg, haccept _ hj', Bool.and_self]

theorem threeHighJointExternal_reject (search : ThreeHighJointExternalSearch)
    (hs : ThreeHighJointExternalSearchSound search)
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (hfalse : search U R = false) (cross : ThreeHighCross)
    (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  intro hj
  have h := hs U R cross hc he hj
  rw [hfalse] at h
  cases h

/-- Consume an actual witness in any finite representative-pair reduction. -/
theorem threeHighJointExternal_reject_candidates {n m : Nat}
    (search : ThreeHighJointExternalSearch) (hs : ThreeHighJointExternalSearchSound search)
    (U : Fin n → Fin 15 → Fin 15 → Bool) (R : Fin m → Fin 8 → Fin 8 → Bool)
    (pairs : Finset (Fin n × Fin m))
    (hfalse : ∀ r q, (r,q) ∈ pairs → search (U r) (R q) = false)
    (hw : ∃ r q cross, (r,q) ∈ pairs ∧ cross ∈ threeHighCrossDomain (U r) (R q) ∧
      encodedExternalBlockCap (threeHighEmptyAdj (U r) (R q) cross) threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj (U r) (R q) cross)) : False := by
  obtain ⟨r,q,cross,hp,hc,he,hj⟩ := hw
  exact threeHighJointExternal_reject search hs (U r) (R q) (hfalse r q hp) cross hc he hj

end Erdos85
#print axioms Erdos85.threeHighJointExternalOf_sound
#print axioms Erdos85.threeHighGatedJointExternal_sound
#print axioms Erdos85.threeHighJointExternal_reject
#print axioms Erdos85.threeHighJointExternal_reject_candidates
