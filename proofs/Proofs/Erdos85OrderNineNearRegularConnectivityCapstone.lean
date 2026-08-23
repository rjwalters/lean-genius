import Proofs.Erdos85OrderNineNearRegularGraphMoments
import Proofs.Erdos85OddSquareOrderNineNearRegularConnectivityTerminal

/-! # Graph-level q=9 near-regular connectivity capstone

This module composes the generic component selector, the relative-to-ambient
two-cut bridge, the graph moment classifier, and the parity-free `3 : 5`
terminal.  Profile-specific work is reduced to supplying the two color-class
facts on every nonowner relatively closed shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The ordinary induced defect graph is connected once every nonowner
closed shore has the exact two-color partition and `3 : 5` balance.

All cut inequalities and finite arithmetic are derived internally. -/
theorem orderNineNearRegular_ordinaryDefect_connected_of_nonowner_shore_data
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hcard : Fintype.card V = 81)
    (h₁ h₂ h₃ : V) (h₁₂ : h₁ ≠ h₂) (h₁₃ : h₁ ≠ h₃) (h₂₃ : h₂ ≠ h₃)
    (owner : V) (B₀ B₁ : Finset V)
    (hOcard : ((Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V)).card = 78)
    (hownerO : owner ∈ (Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V))
    (hdegOrd : ∀ x ∉ ({h₁, h₂, h₃} : Finset V), G.degree x = 9)
    (hdegHigh : ∀ h ∈ ({h₁, h₂, h₃} : Finset V), G.degree h = 10)
    (hhighIndependent : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      Disjoint (G.neighborFinset h) ({h₁, h₂, h₃} : Finset V))
    (hdefectHighIsolated : ∀ h ∈ ({h₁, h₂, h₃} : Finset V),
      (secondOrderDefectGraph G).neighborFinset h = ∅)
    (hshoreCard : ∀ S : Finset V,
      S ⊆ (Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V) →
      owner ∉ S →
      S.card = (B₀ ∩ S).card + (B₁ ∩ S).card)
    (hshoreBalance : ∀ S : Finset V,
      owner ∉ S →
      (∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
        ((Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V)) ⊆ S) →
      3 * (B₀ ∩ S).card = 5 * (B₁ ∩ S).card) :
    ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V) \ ({h₁, h₂, h₃} : Finset V)) : Set V)).Connected := by
  classical
  let H : Finset V := {h₁, h₂, h₃}
  let O : Finset V := Finset.univ \ H
  let D := secondOrderDefectGraph G
  by_contra hnot
  let owner' : {x // x ∈ O} := ⟨owner, hownerO⟩
  obtain ⟨S, hSpos, hSlt, hownerS, hSsub, hclosed⟩ :=
    exists_nonempty_proper_nonowner_relativeClosedShore_of_induce_not_connected
      D O owner' hnot
  have hcuts := two_zeroBoundarySums_of_relative_closed_and_isolated
    D H S hSsub hclosed hdefectHighIsolated
  have hadm := orderNineNearRegularComponentAdmissible_of_twoZeroCuts_fixedHighTriple
    G hfree hcard h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ S hSsub
      hdegOrd hdegHigh hhighIndependent hcuts.1 hcuts.2
  have hb₁le : (G.neighborFinset h₁ ∩ S).card ≤ 10 := by
    calc
      (G.neighborFinset h₁ ∩ S).card ≤ (G.neighborFinset h₁).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h₁ := G.card_neighborFinset_eq_degree h₁
      _ = 10 := hdegHigh h₁ (by simp)
  have hb₂le : (G.neighborFinset h₂ ∩ S).card ≤ 10 := by
    calc
      (G.neighborFinset h₂ ∩ S).card ≤ (G.neighborFinset h₂).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h₂ := G.card_neighborFinset_eq_degree h₂
      _ = 10 := hdegHigh h₂ (by simp)
  have hb₃le : (G.neighborFinset h₃ ∩ S).card ≤ 10 := by
    calc
      (G.neighborFinset h₃ ∩ S).card ≤ (G.neighborFinset h₃).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = G.degree h₃ := G.card_neighborFinset_eq_degree h₃
      _ = 10 := hdegHigh h₃ (by simp)
  have hslt : S.card < 78 := by simpa [O, H, hOcard] using hSlt
  exact false_of_orderNine_nearRegular_component_balance_nat
    S.card
    (G.neighborFinset h₁ ∩ S).card
    (G.neighborFinset h₂ ∩ S).card
    (G.neighborFinset h₃ ∩ S).card
    (B₀ ∩ S).card (B₁ ∩ S).card
    (Nat.ne_of_gt hSpos) hslt (by omega) (by omega) (by omega)
    (hshoreCard S hSsub hownerS) hadm
    (hshoreBalance S hownerS hclosed)

#print axioms orderNineNearRegular_ordinaryDefect_connected_of_nonowner_shore_data

end

end Erdos85
