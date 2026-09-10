import Proofs.Erdos85ThreeHighSecondaryOrbitTable

namespace Erdos85

private def optionCode : Option (Fin 6) → Fin 7
  | none => 0
  | some i => i.succ

private theorem code_cover (t : ThreeHighSecondaryTuple) :
    ∃ m a b e, threeHighSecondaryCode m a b e = t := by
  obtain ⟨m,c,e⟩ := t
  refine ⟨m,optionCode (c 0),optionCode (c 1),e,?_⟩
  have ho (o : Option (Fin 6)) : Fin.cases none some (optionCode o) = o := by
    cases o <;> rfl
  simp only [threeHighSecondaryCode,ho]
  congr 2
  funext k
  fin_cases k <;> rfl

private theorem data_sound (t : ThreeHighSecondaryTuple)
    (w : Fin 21 × (Fin 8 → Fin 8))
    (h : threeHighSecondaryRepresentative w.1 ∈ threeHighSecondaryDomain ∧
      t.1 = (threeHighSecondaryRepresentative w.1).1 ∧ Function.Bijective w.2 ∧
      (∀ i, (w.2 i).val < 6 ↔ i.val < 6) ∧
      ∀ i j, threeHighSecondaryTupleAdj t i j =
        threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative w.1) (w.2 i) (w.2 j)) :
    ∃ k : Fin 21, ∃ ρ : Equiv.Perm (Fin 8),
      threeHighSecondaryRepresentative k ∈ threeHighSecondaryDomain ∧
      t.1 = (threeHighSecondaryRepresentative k).1 ∧
      (∀ i, (ρ i).val < 6 ↔ i.val < 6) ∧
      ∀ i j, threeHighSecondaryTupleAdj t i j =
        threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative k) (ρ i) (ρ j) := by
  exact ⟨w.1,Equiv.ofBijective w.2 h.2.2.1,h.1,h.2.1,h.2.2.2.1,h.2.2.2.2⟩

/-- Every admissible secondary tuple has a near/far-preserving representative
among twenty-one explicitly checked parameter choices. -/
theorem threeHighSecondaryDomain_orbit_cover (t : ThreeHighSecondaryTuple)
    (ht : t ∈ threeHighSecondaryDomain) :
    ∃ k : Fin 21, ∃ ρ : Equiv.Perm (Fin 8),
      threeHighSecondaryRepresentative k ∈ threeHighSecondaryDomain ∧
      t.1 = (threeHighSecondaryRepresentative k).1 ∧
      (∀ i, (ρ i).val < 6 ↔ i.val < 6) ∧
      ∀ i j, threeHighSecondaryTupleAdj t i j =
        threeHighSecondaryTupleAdj (threeHighSecondaryRepresentative k) (ρ i) (ρ j) := by
  obtain ⟨m,a,b,e,rfl⟩ := code_cover t
  exact data_sound _ _ (threeHighSecondaryCode_orbit_certificate m a b e ht)

end Erdos85
#print axioms Erdos85.threeHighSecondaryDomain_orbit_cover
