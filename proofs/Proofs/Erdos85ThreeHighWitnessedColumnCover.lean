import Proofs.Erdos85ThreeHighWitnessedColumnDomains

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

/-- Witnessed domain completeness lets a checked caller-domain tree retain an
actual joint witness after choosing an ordered cross at the same U/R pair. -/
theorem threeHighWitnessedColumnCover_joint_cover {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (hv : threeHighRSwapPairsValid R pairs = true)
    (domains : Fin 8 → List (Finset (Fin 15)))
    (reasons : Fin 8 → List ThreeHighColumnDomainReason)
    (hd : threeHighWitnessedColumnDomainsCheck U R domains reasons = true)
    (table : Fin n → ThreeHighCross)
    (cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin n))
    (ht : threeHighColumnCoverCheck U R pairs score domains table cert = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hj : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    ∃ entry, table entry ∈ threeHighCrossDomain U R ∧
      encodedExternalBlockCap (threeHighEmptyAdj U R (table entry)) threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj U R (table entry)) := by
  obtain ⟨c,hc',he',hj',ho⟩ := threeHighRSwapOrdered_complete U R pairs score hv cross hc he hj
  obtain ⟨entry,eq⟩ := threeHighColumnCoverCheck_cover U R pairs score domains table cert ht c hc' ho
    (threeHighWitnessedColumnDomainsCheck_complete U R domains reasons hd c hc' he')
  subst c
  exact ⟨entry,hc',he',hj'⟩

/-- Checked domain reasons, tree coverage, and all listed rejections together
exclude joint witnesses for the entire fixed pair. All three certificates remain explicit. -/
theorem threeHighWitnessedColumnCover_no_joint {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (hv : threeHighRSwapPairsValid R pairs = true)
    (domains : Fin 8 → List (Finset (Fin 15)))
    (reasons : Fin 8 → List ThreeHighColumnDomainReason)
    (hd : threeHighWitnessedColumnDomainsCheck U R domains reasons = true)
    (table : Fin n → ThreeHighCross)
    (cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin n))
    (ht : threeHighColumnCoverCheck U R pairs score domains table cert = true)
    (hn : ∀ entry, ¬ ThreeHighJointWitness (threeHighEmptyAdj U R (table entry)))
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ¬ ThreeHighJointWitness (threeHighEmptyAdj U R cross) := by
  intro hj
  obtain ⟨entry,_,_,hj'⟩ := threeHighWitnessedColumnCover_joint_cover U R pairs score hv
    domains reasons hd table cert ht cross hc he hj
  exact hn entry hj'

end Erdos85
#print axioms Erdos85.threeHighWitnessedColumnCover_joint_cover
#print axioms Erdos85.threeHighWitnessedColumnCover_no_joint
