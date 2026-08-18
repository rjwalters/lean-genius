import Proofs.Erdos85LambdaSixOwnerFactorTransport

/-! # Packaging graph factors for the lambda-six finite terminal -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000

def relabeledGraphBool {V : Type*} (e : V ≃ Fin 16)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    Fin 16 → Fin 16 → Bool :=
  fun x y => decide (G.Adj (e.symm x) (e.symm y))

private theorem relabeledGraphBool_filter_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (e : V ≃ Fin 16) (p : V → Bool) :
    (Finset.univ.filter fun y : Fin 16 => p (e.symm y)).card =
      (Finset.univ.filter fun y : V => p y).card := by
  apply Finset.card_bij (fun y _ => e.symm y)
  · intro y hy
    simpa using hy
  · intro y₁ hy₁ y₂ hy₂ h
    exact e.symm.injective h
  · intro y hy
    exact ⟨e y, by simpa using hy, by simp⟩

theorem graph_commutingTwoFactor_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (e : V ≃ Fin 16) (D F : SimpleGraph V)
    [DecidableRel D.Adj] [DecidableRel F.Adj]
    (hdeg : ∀ x, F.degree x = 2)
    (hdisjoint : ∀ x y, F.Adj x y → ¬ D.Adj x y)
    (hcomm : F.adjMatrix ℤ * D.adjMatrix ℤ =
      D.adjMatrix ℤ * F.adjMatrix ℤ) :
    LambdaSixBoolCommutingTwoFactor
      (relabeledGraphBool e D) (relabeledGraphBool e F) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    simp [relabeledGraphBool]
  · intro x y
    simp only [relabeledGraphBool, decide_eq_decide]
    exact F.adj_comm _ _
  · intro x
    simp only [relabeledGraphBool]
    rw [relabeledGraphBool_filter_card e
      (fun y => decide (F.Adj (e.symm x) y))]
    calc
      (Finset.univ.filter fun y : V =>
          decide (F.Adj (e.symm x) y) = true).card =
          (F.neighborFinset (e.symm x)).card := by
            congr 1
            ext y
            simp
      _ = F.degree (e.symm x) := F.card_neighborFinset_eq_degree _
      _ = 2 := hdeg _
  · intro x y hxy
    simp only [relabeledGraphBool, decide_eq_true_eq] at hxy ⊢
    exact decide_eq_false_iff_not.mpr (hdisjoint _ _ hxy)
  · intro x y
    simp only [relabeledGraphBool]
    rw [relabeledGraphBool_filter_card e (fun z =>
      decide (F.Adj (e.symm x) z) && decide (D.Adj (e.symm y) z))]
    rw [relabeledGraphBool_filter_card e (fun z =>
      decide (D.Adj (e.symm x) z) && decide (F.Adj (e.symm y) z))]
    have hc := congrFun (congrFun hcomm (e.symm x)) (e.symm y)
    norm_num [Matrix.mul_apply, SimpleGraph.adjMatrix_apply] at hc ⊢
    have hleft :
        (((Finset.univ.filter fun z : V =>
          F.Adj (e.symm x) z ∧ D.Adj (e.symm y) z).card : ℕ) : ℤ) =
        ∑ z : V,
          if D.Adj z (e.symm y) then
            if F.Adj (e.symm x) z then 1 else 0 else 0 := by
      calc
        _ = ∑ z ∈ (Finset.univ : Finset V),
            if F.Adj (e.symm x) z ∧ D.Adj (e.symm y) z
            then (1 : ℤ) else 0 := Finset.natCast_card_filter _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hF : F.Adj (e.symm x) z <;>
            by_cases hD : D.Adj (e.symm y) z <;>
            simp_all [D.adj_comm]
    have hright :
        (((Finset.univ.filter fun z : V =>
          D.Adj (e.symm x) z ∧ F.Adj (e.symm y) z).card : ℕ) : ℤ) =
        ∑ z : V,
          if F.Adj z (e.symm y) then
            if D.Adj (e.symm x) z then 1 else 0 else 0 := by
      calc
        _ = ∑ z ∈ (Finset.univ : Finset V),
            if D.Adj (e.symm x) z ∧ F.Adj (e.symm y) z
            then (1 : ℤ) else 0 := Finset.natCast_card_filter _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro z hz
          by_cases hD : D.Adj (e.symm x) z <;>
            by_cases hF : F.Adj (e.symm y) z <;>
            simp_all [F.adj_comm]
    exact_mod_cast hleft.trans (hc.trans hright.symm)

def GraphFourFactorization {V : Type*} [Fintype V] [DecidableEq V]
    (D F0 F1 F2 F3 : SimpleGraph V)
    [DecidableRel D.Adj] [DecidableRel F0.Adj] [DecidableRel F1.Adj]
    [DecidableRel F2.Adj] [DecidableRel F3.Adj] : Prop :=
  (∀ x, F0.degree x = 2) ∧ (∀ x, F1.degree x = 2) ∧
  (∀ x, F2.degree x = 2) ∧ (∀ x, F3.degree x = 2) ∧
  (∀ x y, F0.Adj x y → ¬D.Adj x y) ∧
  (∀ x y, F1.Adj x y → ¬D.Adj x y) ∧
  (∀ x y, F2.Adj x y → ¬D.Adj x y) ∧
  (∀ x y, F3.Adj x y → ¬D.Adj x y) ∧
  F0.adjMatrix ℤ * D.adjMatrix ℤ = D.adjMatrix ℤ * F0.adjMatrix ℤ ∧
  F1.adjMatrix ℤ * D.adjMatrix ℤ = D.adjMatrix ℤ * F1.adjMatrix ℤ ∧
  F2.adjMatrix ℤ * D.adjMatrix ℤ = D.adjMatrix ℤ * F2.adjMatrix ℤ ∧
  F3.adjMatrix ℤ * D.adjMatrix ℤ = D.adjMatrix ℤ * F3.adjMatrix ℤ ∧
  ∀ x y, x ≠ y →
    if D.Adj x y then
      ¬F0.Adj x y ∧ ¬F1.Adj x y ∧ ¬F2.Adj x y ∧ ¬F3.Adj x y
    else
      (F0.Adj x y ∧ ¬F1.Adj x y ∧ ¬F2.Adj x y ∧ ¬F3.Adj x y) ∨
      (¬F0.Adj x y ∧ F1.Adj x y ∧ ¬F2.Adj x y ∧ ¬F3.Adj x y) ∨
      (¬F0.Adj x y ∧ ¬F1.Adj x y ∧ F2.Adj x y ∧ ¬F3.Adj x y) ∨
      (¬F0.Adj x y ∧ ¬F1.Adj x y ∧ ¬F2.Adj x y ∧ F3.Adj x y)

theorem graph_fourFactorization_relabel
    {V : Type*} [Fintype V] [DecidableEq V]
    (e : V ≃ Fin 16) (D F0 F1 F2 F3 : SimpleGraph V)
    [DecidableRel D.Adj] [DecidableRel F0.Adj] [DecidableRel F1.Adj]
    [DecidableRel F2.Adj] [DecidableRel F3.Adj]
    (h : GraphFourFactorization D F0 F1 F2 F3) :
    LambdaSixBoolFourFactorization (relabeledGraphBool e D)
      (relabeledGraphBool e F0) (relabeledGraphBool e F1)
      (relabeledGraphBool e F2) (relabeledGraphBool e F3) := by
  rcases h with ⟨hdeg0, hdeg1, hdeg2, hdeg3,
    hdis0, hdis1, hdis2, hdis3, hcomm0, hcomm1, hcomm2, hcomm3, hpart⟩
  refine ⟨graph_commutingTwoFactor_relabel e D F0 hdeg0 hdis0 hcomm0,
    graph_commutingTwoFactor_relabel e D F1 hdeg1 hdis1 hcomm1,
    graph_commutingTwoFactor_relabel e D F2 hdeg2 hdis2 hcomm2,
    graph_commutingTwoFactor_relabel e D F3 hdeg3 hdis3 hcomm3, ?_⟩
  intro x y hxy
  have hpre : e.symm x ≠ e.symm y := by
    intro h
    exact hxy (e.symm.injective h)
  have hp := hpart (e.symm x) (e.symm y) hpre
  simp only [relabeledGraphBool]
  split <;> rename_i hd
  · simp only [decide_eq_true_eq] at hd
    rw [if_pos hd] at hp
    simpa only [decide_eq_false_iff_not] using hp
  · simp only [Bool.not_eq_true] at hd
    have hd' : ¬D.Adj (e.symm x) (e.symm y) := by simpa using hd
    rw [if_neg hd'] at hp
    simpa only [decide_eq_true_eq, decide_eq_false_iff_not] using hp

end

end Erdos85
