import Proofs.Erdos85MatchingEdgeDeletion

/-! Split a matching into a labeled edge and its remaining graph. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem pair_remainder_equiv
    {V : Type*} [Fintype V] [DecidableEq V] (a b : V) (hab : a ≠ b) :
    let R := Finset.univ \ ({a,b} : Finset V)
    ∃ e : (Fin 2 ⊕ (↑R : Set V)) ≃ V,
      e (Sum.inl 0) = a ∧ e (Sum.inl 1) = b ∧ ∀ x, e (Sum.inr x) = x.val := by
  classical
  let R := Finset.univ \ ({a,b} : Finset V)
  let f : (Fin 2 ⊕ (↑R : Set V)) → V := fun p =>
    match p with
    | Sum.inl i => if i = 0 then a else b
    | Sum.inr x => x.val
  have hinj : Function.Injective f := by
    intro p q hpq
    rcases p with i | x <;> rcases q with j | y
    · fin_cases i <;> fin_cases j <;> simp_all [f]
    · have hy := (Finset.mem_sdiff.mp y.property).2
      have hm : y.val ∈ ({a,b} : Finset V) := by fin_cases i <;> simp_all [f]
      exact (hy hm).elim
    · have hx := (Finset.mem_sdiff.mp x.property).2
      have hm : x.val ∈ ({a,b} : Finset V) := by fin_cases j <;> simp_all [f]
      exact (hx hm).elim
    · exact congrArg Sum.inr (Subtype.ext hpq)
  have hsurj : Function.Surjective f := by
    intro x
    by_cases hxa : x = a
    · exact ⟨Sum.inl 0, by simp [f, hxa]⟩
    by_cases hxb : x = b
    · exact ⟨Sum.inl 1, by simp [f, hxb]⟩
    exact ⟨Sum.inr ⟨x, by simp [R, hxa, hxb]⟩, rfl⟩
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, rfl, rfl, fun _ => rfl⟩

theorem matching_edge_split
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x ≤ 1) {a b : V} (hab : G.Adj a b) :
    let R := Finset.univ \ ({a,b} : Finset V)
    ∃ e : (Fin 2 ⊕ (↑R : Set V)) ≃ V,
      ∀ p q, G.Adj (e p) (e q) ↔
        match p, q with
        | Sum.inl i, Sum.inl j => i ≠ j
        | Sum.inr x, Sum.inr y => (G.induce (↑R : Set V)).Adj x y
        | _, _ => False := by
  classical
  let R := Finset.univ \ ({a,b} : Finset V)
  obtain ⟨e, h0, h1, hR⟩ := pair_remainder_equiv a b hab.ne
  have hno := (matching_edge_deletion G hdegree hab).2.2.2
  refine ⟨e, ?_⟩
  intro p q
  rcases p with i | x <;> rcases q with j | y
  · fin_cases i <;> fin_cases j <;> simp [h0, h1, hab, hab.symm]
  · fin_cases i
    · simpa [h0, hR] using iff_false_intro (hno y.val y.property).1
    · simpa [h1, hR] using iff_false_intro (hno y.val y.property).2
  · fin_cases j
    · simpa [hR, h0] using iff_false_intro (show ¬ G.Adj x.val a from fun h => (hno x.val x.property).1 h.symm)
    · simpa [hR, h1] using iff_false_intro (show ¬ G.Adj x.val b from fun h => (hno x.val x.property).2 h.symm)
  · rw [hR, hR]
    rfl

end
end Erdos85
#print axioms Erdos85.matching_edge_split
