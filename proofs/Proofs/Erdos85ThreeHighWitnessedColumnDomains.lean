import Proofs.Erdos85ThreeHighColumnCoverCertificate

namespace Erdos85

inductive ThreeHighColumnDomainReason where
  | kept
  | margin
  | rectangle (x y a b : Fin 24)

def threeHighColumnDomainReasonCheck (U : Fin 15 → Fin 15 → Bool)
    (R : Fin 8 → Fin 8 → Bool) (j : Fin 8) (D : List (Finset (Fin 15)))
    (S : Finset (Fin 15)) : ThreeHighColumnDomainReason → Bool
  | .kept => decide (S ∈ D)
  | .margin => decide (S.card + encodedRowDegree (R j) + (if j.val < 6 then 1 else 0) ≠ 4)
  | .rectangle x y a b =>
      let B := threeHighEmptyAdj U R (threeHighSingleColumn j S)
      decide (x ≠ y ∧ a ≠ b) && B x a && B y a && B x b && B y b

theorem threeHighColumnDomainReasonCheck_sound
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (j : Fin 8) (D : List (Finset (Fin 15))) (S : Finset (Fin 15))
    (reason : ThreeHighColumnDomainReason)
    (hc : threeHighColumnDomainReasonCheck U R j D S reason = true)
    (hm : S.card + encodedRowDegree (R j) + (if j.val < 6 then 1 else 0) = 4)
    (hf : encodedC4Free (threeHighEmptyAdj U R (threeHighSingleColumn j S)) = true) : S ∈ D := by
  cases reason with
  | kept => exact of_decide_eq_true hc
  | margin => exact False.elim ((of_decide_eq_true hc) hm)
  | rectangle x y a b =>
    simp only [threeHighColumnDomainReasonCheck,Bool.and_eq_true,decide_eq_true_eq] at hc
    unfold encodedC4Free at hf
    simp only [decide_eq_true_eq] at hf
    let B := threeHighEmptyAdj U R (threeHighSingleColumn j S)
    have mem (z : Fin 24) (hx : B x z = true) (hy : B y z = true) :
        z ∈ Finset.univ.filter (fun w => B x w && B y w) := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,by simp only [Bool.and_eq_true]; exact ⟨hx,hy⟩⟩
    exact False.elim (hc.1.1.1.1.2 (Finset.card_le_one.mp (hf x y hc.1.1.1.1.1)
      a (mem a hc.1.1.1.2 hc.1.1.2) b (mem b hc.1.2 hc.2)))

def threeHighWitnessedColumnDomainsCheck
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (D : Fin 8 → List (Finset (Fin 15)))
    (reasons : Fin 8 → List ThreeHighColumnDomainReason) : Bool :=
  (List.finRange 8).all fun j => finiteRowChildrenCheck
    (threeHighColumnDomainReasonCheck U R j (D j)) threeHighCompactColumnCandidates (reasons j)

attribute [local irreducible] threeHighCrossDomain

/-- Explicit rejection witnesses suffice for completeness; equality to the
computed static lists and validity of every kept candidate are unnecessary. -/
theorem threeHighWitnessedColumnDomainsCheck_complete
    (U : Fin 15 → Fin 15 → Bool) (R : Fin 8 → Fin 8 → Bool)
    (D : Fin 8 → List (Finset (Fin 15)))
    (reasons : Fin 8 → List ThreeHighColumnDomainReason)
    (hcheck : threeHighWitnessedColumnDomainsCheck U R D reasons = true)
    (cross : ThreeHighCross) (hc : cross ∈ threeHighCrossDomain U R)
    (he : encodedExternalBlockCap (threeHighEmptyAdj U R cross) threeHighCanonicalRow = true) :
    ∀ j, threeHighCrossColumns cross j ∈ D j := by
  have hcap := he
  rw [threeHighExternalBlockCap_factor] at hcap
  simp only [Bool.and_eq_true] at hcap
  intro j
  have hcol := threeHighCrossColumnDomain_complete U R cross hc hcap.2 j
  have hlist := threeHighCompactColumnList_complete R j _ hcol
  have hparts := List.mem_filter.mp hlist
  obtain ⟨reason,_,hr⟩ := finiteRowChildrenCheck_cover _ _ _
    (List.all_eq_true.mp hcheck j (List.mem_finRange j)) _ hparts.1
  apply threeHighColumnDomainReasonCheck_sound U R j (D j) _ reason hr
  · exact of_decide_eq_true hparts.2
  · exact encodedC4Free_of_subgraph _ _ (threeHighSingleColumn_subgraph U R cross j)
      ((mem_threeHighCrossDomain_iff U R cross).mp hc).1

end Erdos85
#print axioms Erdos85.threeHighColumnDomainReasonCheck_sound
#print axioms Erdos85.threeHighWitnessedColumnDomainsCheck_complete
