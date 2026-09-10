import Proofs.Erdos85MatchingEdgeSplit

/-! Structural matching normal form: one two-point summand per edge, followed by isolated vertices. -/
namespace Erdos85
open SimpleGraph
noncomputable section

def matchingNestedVertices : ℕ → ℕ → Type
  | 0, k => Fin k
  | m + 1, k => Fin 2 ⊕ matchingNestedVertices m k

def matchingNestedAdj : (m k : ℕ) → matchingNestedVertices m k → matchingNestedVertices m k → Prop
  | 0, _, _, _ => False
  | _ + 1, _, Sum.inl i, Sum.inl j => i ≠ j
  | m + 1, k, Sum.inr x, Sum.inr y => matchingNestedAdj m k x y
  | _ + 1, _, _, _ => False

instance matchingNestedFintype : (m k : ℕ) → Fintype (matchingNestedVertices m k)
  | 0, k => inferInstanceAs (Fintype (Fin k))
  | m + 1, k => by
    letI := matchingNestedFintype m k
    exact inferInstanceAs (Fintype (Fin 2 ⊕ matchingNestedVertices m k))

theorem matchingNestedVertices_card (m k : ℕ) :
    Fintype.card (matchingNestedVertices m k) = 2 * m + k := by
  induction m with
  | zero =>
    change Fintype.card (Fin k) = 2 * 0 + k
    simpa only [Nat.mul_zero, Nat.zero_add] using Fintype.card_fin k
  | succ m ih =>
    change Fintype.card (Fin 2 ⊕ matchingNestedVertices m k) = _
    rw [Fintype.card_sum, Fintype.card_fin, ih]
    omega

theorem finite_matching_nested_normal_form (m : ℕ) :
    ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ x, G.degree x ≤ 1) → G.edgeFinset.card = m →
      ∃ k, ∃ e : matchingNestedVertices m k ≃ V,
        ∀ x y, G.Adj (e x) (e y) ↔ matchingNestedAdj m k x y := by
  induction m with
  | zero =>
    intro V _ _ G _ hdegree he
    have hbot : G = ⊥ := by
      apply not_ne_iff.mp
      intro hn
      have hp := Finset.card_pos.mpr (SimpleGraph.edgeFinset_nonempty.mpr hn)
      omega
    let e : matchingNestedVertices 0 (Fintype.card V) ≃ V := (Fintype.equivFin V).symm
    refine ⟨Fintype.card V, e, ?_⟩
    intro x y
    simp [hbot, matchingNestedAdj]
  | succ m ih =>
    intro V _ _ G _ hdegree he
    classical
    have hn : G ≠ ⊥ := SimpleGraph.edgeFinset_nonempty.mp
      (Finset.card_pos.mp (show 0 < G.edgeFinset.card by omega))
    obtain ⟨a, b, hab⟩ := SimpleGraph.ne_bot_iff_exists_adj.mp hn
    let R := Finset.univ \ ({a,b} : Finset V)
    let H := G.induce (↑R : Set V)
    have hd := matching_edge_deletion G hdegree hab
    have hcap : ∀ x, H.degree x ≤ 1 := hd.2.2.1
    have hcount : H.edgeFinset.card = m := by
      have hc : H.edgeFinset.card + 1 = G.edgeFinset.card := hd.2.1
      omega
    obtain ⟨k, er, her⟩ := ih H hcap hcount
    obtain ⟨es, hes⟩ := matching_edge_split G hdegree hab
    let e : matchingNestedVertices (m + 1) k ≃ V :=
      (Equiv.sumCongr (Equiv.refl (Fin 2)) er).trans es
    refine ⟨k, e, ?_⟩
    intro x y
    change G.Adj (es ((Equiv.sumCongr (Equiv.refl (Fin 2)) er) x))
      (es ((Equiv.sumCongr (Equiv.refl (Fin 2)) er) y)) ↔ _
    rw [hes]
    rcases x with i | x <;> rcases y with j | y
    · rfl
    · rfl
    · rfl
    · exact her x y

theorem finite_matching_nested_normal_form_with_card
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ x, G.degree x ≤ 1) :
    ∃ k, ∃ e : matchingNestedVertices G.edgeFinset.card k ≃ V,
      2 * G.edgeFinset.card + k = Fintype.card V ∧
      ∀ x y, G.Adj (e x) (e y) ↔ matchingNestedAdj G.edgeFinset.card k x y := by
  obtain ⟨k, e, he⟩ := finite_matching_nested_normal_form G.edgeFinset.card G hdegree rfl
  refine ⟨k, e, ?_, he⟩
  have hc := Fintype.card_congr e
  rw [matchingNestedVertices_card] at hc
  exact hc

end
end Erdos85
#print axioms Erdos85.finite_matching_nested_normal_form

#print axioms Erdos85.matchingNestedVertices_card
#print axioms Erdos85.finite_matching_nested_normal_form_with_card
