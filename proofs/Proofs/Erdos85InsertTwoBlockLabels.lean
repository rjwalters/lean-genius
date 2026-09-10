import Mathlib

/-! Preserve two disjoint block labelings and append a distinguished vertex. -/
namespace Erdos85
noncomputable section

theorem insert_two_block_labels {V : Type*} [DecidableEq V]
    {m n : ℕ} (A B E : Finset V) (u : V)
    (huA : u ∉ A) (huB : u ∉ B) (hAB : Disjoint A B)
    (hE : E = (A ∪ B) ∪ {u})
    (a : Fin m ≃ (↑A : Set V)) (b : Fin n ≃ (↑B : Set V)) :
    ∃ e : Fin (m + n + 1) ≃ (↑E : Set V),
      (∀ i, (e (Fin.castAdd 1 (Fin.castAdd n i))).val = (a i).val) ∧
      (∀ j, (e (Fin.castAdd 1 (Fin.natAdd m j))).val = (b j).val) ∧
      (e (Fin.natAdd (m + n) (0 : Fin 1))).val = u := by
  classical
  let c : Fin 1 ≃ (↑({u} : Finset V) : Set V) :=
    { toFun := fun _ => ⟨u, Finset.mem_singleton_self u⟩
      invFun := fun _ => 0
      left_inv := fun i => Subsingleton.elim _ _
      right_inv := fun x => Subtype.ext (Finset.mem_singleton.mp x.property).symm }
  let ab : Fin (m + n) ≃ (↑(A ∪ B) : Set V) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr a b)).trans (Equiv.Finset.union A B hAB)
  have hc : Disjoint (A ∪ B) ({u} : Finset V) :=
    Finset.disjoint_singleton_right.mpr (by simpa using And.intro huA huB)
  let e : Fin (m + n + 1) ≃ (↑E : Set V) :=
    ((finSumFinEquiv.symm.trans (Equiv.sumCongr ab c)).trans
      (Equiv.Finset.union (A ∪ B) {u} hc)).trans
      (Equiv.setCongr (congrArg (fun S : Finset V => (↑S : Set V)) hE.symm))
  refine ⟨e, ?_, ?_, ?_⟩
  · intro i
    simp [e, ab, Equiv.setCongr, Equiv.subtypeEquivProp]
  · intro j
    simp [e, ab, Equiv.setCongr, Equiv.subtypeEquivProp]
  · simp [e, c, Equiv.setCongr, Equiv.subtypeEquivProp]

end
end Erdos85
#print axioms Erdos85.insert_two_block_labels
