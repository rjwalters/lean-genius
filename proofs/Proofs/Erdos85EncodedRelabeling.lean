import Proofs.Erdos85ThreeHighCrossMargins

namespace Erdos85

theorem encodedC4Free_comap_injective
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (B : V → V → Bool) (f : W → V) (hf : Function.Injective f)
    (hB : encodedC4Free B = true) : encodedC4Free (fun p q => B (f p) (f q)) = true := by
  simp only [encodedC4Free, decide_eq_true_eq] at hB ⊢
  intro p q hpq
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply hf
  have hc := hB (f p) (f q) (fun h => hpq (hf h))
  apply Finset.card_le_one.mp hc
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hb

theorem encodedC4Free_relabel
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (B : V → V → Bool) (e : W ≃ V) :
    encodedC4Free (fun p q => B (e p) (e q)) = encodedC4Free B := by
  have hi : encodedC4Free (fun p q => B (e p) (e q)) = true ↔ encodedC4Free B = true := by
    constructor
    · intro h
      have hh := encodedC4Free_comap_injective (fun p q => B (e p) (e q)) e.symm
        e.symm.injective h
      simpa only [Equiv.apply_symm_apply] using hh
    · exact encodedC4Free_comap_injective B e e.injective
  cases h₁ : encodedC4Free (fun p q => B (e p) (e q)) <;>
    cases h₂ : encodedC4Free B <;> simp_all

theorem encodedRowDegree_relabel
    {V W : Type*} [Fintype V] [Fintype W]
    (B : V → Bool) (e : W ≃ V) :
    encodedRowDegree (fun q => B (e q)) = encodedRowDegree B := by
  apply Finset.card_bij (fun q _ => e q)
  · intro q hq
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hq
  · intro a ha b hb hab
    exact e.injective hab
  · intro q hq
    refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply] using hq

theorem encodedDegreeProfile_relabel
    {V W : Type*} [Fintype V] [Fintype W]
    (B : V → V → Bool) (d : V → ℕ) (e : W ≃ V) :
    encodedDegreeProfile (fun p q => B (e p) (e q)) (fun p => d (e p)) =
      encodedDegreeProfile B d := by
  unfold encodedDegreeProfile
  apply Bool.decide_congr
  change (∀ p, encodedRowDegree (fun q => B (e p) (e q)) = d (e p)) ↔
    (∀ p, encodedRowDegree (B p) = d p)
  simp only [encodedRowDegree_relabel]
  constructor
  · intro h p
    obtain ⟨q, rfl⟩ := e.surjective p
    exact h q
  · intro h p
    exact h (e p)

end Erdos85
#print axioms Erdos85.encodedC4Free_comap_injective
#print axioms Erdos85.encodedC4Free_relabel
#print axioms Erdos85.encodedRowDegree_relabel
#print axioms Erdos85.encodedDegreeProfile_relabel
