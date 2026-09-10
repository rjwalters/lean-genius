import Proofs.Erdos85FiniteRowCoverCertificate
import Proofs.Erdos85ThreeHighColumnCutCertificate

namespace Erdos85
attribute [local irreducible] threeHighCrossDomain

def threeHighColumnCoverCheck {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (lists : Fin 8 → List (Finset (Fin 15))) (table : Fin n → ThreeHighCross)
    (cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin n)) : Bool :=
  finiteRowCoverCheck lists
    (fun k columns reason => threeHighColumnCutCheck U R pairs score k (threeHighCrossOfColumns columns) reason)
    (fun columns entry => decide (∀ i j, threeHighCrossOfColumns columns i j = table entry i j))
    8 0 (fun _ => ∅) cert

theorem threeHighColumnCoverCheck_cover {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (lists : Fin 8 → List (Finset (Fin 15))) (table : Fin n → ThreeHighCross)
    (cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin n))
    (hcert : threeHighColumnCoverCheck U R pairs score lists table cert = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (ho : threeHighRSwapOrdered pairs score cross = true)
    (hl : ∀ j, threeHighCrossColumns cross j ∈ lists j) :
    ∃ entry, cross = table entry := by
  have hprefix (k : Nat) :
      threeHighCrossOfColumns (finiteRowPrefix (fun _ => ∅) (threeHighCrossColumns cross) k) =
        threeHighCrossColumnPrefix cross k := by
    funext i j
    by_cases h : j.val < k <;>
      simp [threeHighCrossOfColumns,finiteRowPrefix,threeHighCrossColumns,threeHighCrossColumnPrefix,h]
  obtain ⟨entry,he⟩ := finiteRowCoverCheck_cover lists
    (fun k columns reason => threeHighColumnCutCheck U R pairs score k (threeHighCrossOfColumns columns) reason)
    (fun columns entry => decide (∀ i j, threeHighCrossOfColumns columns i j = table entry i j))
    (fun _ => ∅) (threeHighCrossColumns cross) hl
    (by intro k hk reason; rw [hprefix]; exact threeHighColumnCutCheck_prefix_false U R pairs score cross hc ho k reason)
    cert hcert
  have heq := of_decide_eq_true he
  rw [threeHighCrossOfColumns_columns] at heq
  exact ⟨entry,funext fun i => funext fun j => heq i j⟩

/-- A certified static-domain tree retains a listed joint witness after R ordering. -/
theorem threeHighColumnCoverCheck_joint_cover {n : Nat}
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (pairs : List (Fin 8 × Fin 8)) (score : (Fin 15 → Bool) → Nat)
    (hv : threeHighRSwapPairsValid R pairs = true)
    (table : Fin n → ThreeHighCross)
    (cert : FiniteRowCoverCertificate ThreeHighColumnCut (Fin n))
    (hcert : threeHighColumnCoverCheck U R pairs score (threeHighStaticPrunedColumnList U R) table cert = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true)
    (hj : ThreeHighJointWitness (threeHighEmptyAdj U R cross)) :
    ∃ entry, table entry ∈ threeHighCrossDomain U R ∧
      encodedExternalBlockCap (threeHighEmptyAdj U R (table entry)) threeHighCanonicalRow = true ∧
      ThreeHighJointWitness (threeHighEmptyAdj U R (table entry)) := by
  obtain ⟨c,hc',he',hj',ho⟩ := threeHighRSwapOrdered_complete U R pairs score hv cross hc he hj
  have hcap := he'
  rw [threeHighExternalBlockCap_factor] at hcap
  simp only [Bool.and_eq_true] at hcap
  obtain ⟨entry,eq⟩ := threeHighColumnCoverCheck_cover U R pairs score _ table cert hcert c hc' ho
    (fun j => threeHighStaticPrunedColumnList_complete U R c hc' hcap.2 j)
  subst c
  exact ⟨entry,hc',he',hj'⟩

end Erdos85
#print axioms Erdos85.threeHighColumnCoverCheck_cover
#print axioms Erdos85.threeHighColumnCoverCheck_joint_cover
