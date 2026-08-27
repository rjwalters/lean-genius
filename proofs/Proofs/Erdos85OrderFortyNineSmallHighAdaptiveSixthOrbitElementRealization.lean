import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveSixthOrbitNormalForm
import Proofs.Erdos85OrderFortyNineSmallHighAdaptiveSixthOrbitRealization

/-! # Semantic transport by all sixteen adaptive sixth orbit elements -/

namespace Erdos85

open SimpleGraph

noncomputable section

private def orderFortyNineAdaptiveSixthCellTransform
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (c : OrderFortyNineAdaptiveSixthCell) : OrderFortyNineAdaptiveSixthCell :=
  orderFortyNineAdaptiveSixthTransformGenerator g c

def orderFortyNineAdaptiveSixthOrbitGraph
    (k : Fin 16) (G : SimpleGraph (Fin 49)) : SimpleGraph (Fin 49) :=
  let G := if k.val % 2 = 1 then
    orderFortyNineRelabeledGraph G
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 0) else G
  let G := if k.val / 2 % 2 = 1 then
    orderFortyNineRelabeledGraph G
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 1) else G
  let G := if k.val / 4 % 2 = 1 then
    orderFortyNineRelabeledGraph G
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 2) else G
  if k.val / 8 % 2 = 1 then
    orderFortyNineRelabeledGraph G
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 3) else G

private def orderFortyNineAdaptiveSixthOrbitStateStep
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (s : SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell) :
    SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell :=
  (orderFortyNineRelabeledGraph s.1
      (orderFortyNineAdaptiveSixthOrbitVertexPerm g),
    orderFortyNineAdaptiveSixthCellTransform g s.2)

private def OrderFortyNineAdaptiveSixthOrbitStateAdmissible
    (s : SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell) : Prop :=
  ¬ containsC4 (Fin 49) s.1 ∧
    OrderFortyNineRealizesAdaptiveSixthCell s.1
      s.2.li s.2.ri s.2.ai s.2.bi s.2.ci s.2.di s.2.ei

private theorem orderFortyNineAdaptiveSixthOrbitStateStep_admissible
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (s : SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell)
    (hs : OrderFortyNineAdaptiveSixthOrbitStateAdmissible s) :
    OrderFortyNineAdaptiveSixthOrbitStateAdmissible
      (orderFortyNineAdaptiveSixthOrbitStateStep g s) := by
  rcases s with ⟨G, c⟩
  rcases c with ⟨li, ri, ai, bi, ci, di, ei⟩
  exact ⟨orderFortyNineRelabeledGraph_not_containsC4 G _ hs.1,
    orderFortyNineAdaptiveSixthOrbit_realizes_target
      G g li ri ai bi ci di ei hs.2⟩

private theorem orderFortyNineAdaptiveSixthOrbitStateStep_if_admissible
    (b : Prop) [Decidable b]
    (g : OrderFortyNineAdaptiveSixthOrbitGenerator)
    (s : SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell)
    (hs : OrderFortyNineAdaptiveSixthOrbitStateAdmissible s) :
    OrderFortyNineAdaptiveSixthOrbitStateAdmissible
      (if b then orderFortyNineAdaptiveSixthOrbitStateStep g s else s) := by
  by_cases hb : b
  · rw [if_pos hb]
    exact orderFortyNineAdaptiveSixthOrbitStateStep_admissible g s hs
  · rw [if_neg hb]
    exact hs

private def orderFortyNineAdaptiveSixthOrbitState
    (k : Fin 16)
    (s : SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell) :
    SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell :=
  let s := if k.val % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 0 s else s
  let s := if k.val / 2 % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 1 s else s
  let s := if k.val / 4 % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 2 s else s
  if k.val / 8 % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 3 s else s

private theorem orderFortyNineAdaptiveSixthOrbitState_admissible
    (k : Fin 16)
    (s : SimpleGraph (Fin 49) × OrderFortyNineAdaptiveSixthCell)
    (hs : OrderFortyNineAdaptiveSixthOrbitStateAdmissible s) :
    OrderFortyNineAdaptiveSixthOrbitStateAdmissible
      (orderFortyNineAdaptiveSixthOrbitState k s) := by
  let s₁ := if k.val % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 0 s else s
  let s₂ := if k.val / 2 % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 1 s₁ else s₁
  let s₃ := if k.val / 4 % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 2 s₂ else s₂
  let s₄ := if k.val / 8 % 2 = 1 then
    orderFortyNineAdaptiveSixthOrbitStateStep 3 s₃ else s₃
  have h₁ : OrderFortyNineAdaptiveSixthOrbitStateAdmissible s₁ :=
    orderFortyNineAdaptiveSixthOrbitStateStep_if_admissible
      (k.val % 2 = 1) 0 s hs
  have h₂ : OrderFortyNineAdaptiveSixthOrbitStateAdmissible s₂ :=
    orderFortyNineAdaptiveSixthOrbitStateStep_if_admissible
      (k.val / 2 % 2 = 1) 1 s₁ h₁
  have h₃ : OrderFortyNineAdaptiveSixthOrbitStateAdmissible s₃ :=
    orderFortyNineAdaptiveSixthOrbitStateStep_if_admissible
      (k.val / 4 % 2 = 1) 2 s₂ h₂
  have h₄ : OrderFortyNineAdaptiveSixthOrbitStateAdmissible s₄ :=
    orderFortyNineAdaptiveSixthOrbitStateStep_if_admissible
      (k.val / 8 % 2 = 1) 3 s₃ h₃
  exact h₄

private def OrderFortyNineGraphMinDegreeCard
    (G : SimpleGraph (Fin 49)) (d : Nat) : Prop :=
  ∀ v, d ≤ Nat.card (G.neighborSet v)

private theorem orderFortyNineGraphMinDegreeCard_relabel
    (G : SimpleGraph (Fin 49)) (E : Equiv.Perm (Fin 49)) (d : Nat)
    (h : OrderFortyNineGraphMinDegreeCard G d) :
    OrderFortyNineGraphMinDegreeCard
      (orderFortyNineRelabeledGraph G E) d := by
  classical
  have hd : ∀ v, d ≤ G.degree v := by
    intro v
    simpa only [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree] using h v
  intro v
  simpa only [Nat.card_eq_fintype_card,
    (orderFortyNineRelabeledGraph G E).card_neighborSet_eq_degree] using
      orderFortyNineRelabeledGraph_minDegree G E d hd v

theorem orderFortyNineAdaptiveSixthOrbitElement_semantic_transport
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    (k : Fin 16) (c : OrderFortyNineAdaptiveSixthCell) (d : Nat)
    (hfree : ¬ containsC4 (Fin 49) G)
    (hdegree : ∀ v, d ≤ G.degree v)
    (hreal : OrderFortyNineRealizesAdaptiveSixthCell G
      c.li c.ri c.ai c.bi c.ci c.di c.ei) :
    let H := orderFortyNineAdaptiveSixthOrbitGraph k G
    let t := orderFortyNineAdaptiveSixthOrbitElement k c
    letI : DecidableRel H.Adj := Classical.decRel _
    ¬ containsC4 (Fin 49) H ∧
      (∀ v, d ≤ H.degree v) ∧
      OrderFortyNineRealizesAdaptiveSixthCell H
        t.li t.ri t.ai t.bi t.ci t.di t.ei := by
  classical
  have hs : OrderFortyNineAdaptiveSixthOrbitStateAdmissible (G, c) :=
    ⟨hfree, hreal⟩
  have ht := orderFortyNineAdaptiveSixthOrbitState_admissible k (G, c) hs
  have hgraph : (orderFortyNineAdaptiveSixthOrbitState k (G, c)).1 =
      orderFortyNineAdaptiveSixthOrbitGraph k G := by
    fin_cases k <;> rfl
  have hcell : (orderFortyNineAdaptiveSixthOrbitState k (G, c)).2 =
      orderFortyNineAdaptiveSixthOrbitElement k c := by
    fin_cases k <;> rfl
  have hfree' : ¬ containsC4 (Fin 49)
      (orderFortyNineAdaptiveSixthOrbitGraph k G) := by
    simpa only [hgraph] using ht.1
  have hreal' : OrderFortyNineRealizesAdaptiveSixthCell
      (orderFortyNineAdaptiveSixthOrbitGraph k G)
      (orderFortyNineAdaptiveSixthOrbitElement k c).li
      (orderFortyNineAdaptiveSixthOrbitElement k c).ri
      (orderFortyNineAdaptiveSixthOrbitElement k c).ai
      (orderFortyNineAdaptiveSixthOrbitElement k c).bi
      (orderFortyNineAdaptiveSixthOrbitElement k c).ci
      (orderFortyNineAdaptiveSixthOrbitElement k c).di
      (orderFortyNineAdaptiveSixthOrbitElement k c).ei := by
    rw [← hgraph, ← hcell]
    exact ht.2
  let G₁ := if k.val % 2 = 1 then
    orderFortyNineRelabeledGraph G
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 0) else G
  let G₂ := if k.val / 2 % 2 = 1 then
    orderFortyNineRelabeledGraph G₁
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 1) else G₁
  let G₃ := if k.val / 4 % 2 = 1 then
    orderFortyNineRelabeledGraph G₂
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 2) else G₂
  let G₄ := if k.val / 8 % 2 = 1 then
    orderFortyNineRelabeledGraph G₃
      (orderFortyNineAdaptiveSixthOrbitVertexPerm 3) else G₃
  have hd₀ : OrderFortyNineGraphMinDegreeCard G d := by
    intro v
    simpa only [Nat.card_eq_fintype_card, G.card_neighborSet_eq_degree] using
      hdegree v
  have hd₁ : OrderFortyNineGraphMinDegreeCard G₁ d := by
    dsimp only [G₁]
    by_cases hb : k.val % 2 = 1
    · simp only [if_pos hb]
      exact orderFortyNineGraphMinDegreeCard_relabel G _ d hd₀
    · simpa only [if_neg hb] using hd₀
  have hd₂ : OrderFortyNineGraphMinDegreeCard G₂ d := by
    dsimp only [G₂]
    by_cases hb : k.val / 2 % 2 = 1
    · simp only [if_pos hb]
      exact orderFortyNineGraphMinDegreeCard_relabel G₁ _ d hd₁
    · simpa only [if_neg hb] using hd₁
  have hd₃ : OrderFortyNineGraphMinDegreeCard G₃ d := by
    dsimp only [G₃]
    by_cases hb : k.val / 4 % 2 = 1
    · simp only [if_pos hb]
      exact orderFortyNineGraphMinDegreeCard_relabel G₂ _ d hd₂
    · simpa only [if_neg hb] using hd₂
  have hd₄ : OrderFortyNineGraphMinDegreeCard G₄ d := by
    dsimp only [G₄]
    by_cases hb : k.val / 8 % 2 = 1
    · simp only [if_pos hb]
      exact orderFortyNineGraphMinDegreeCard_relabel G₃ _ d hd₃
    · simpa only [if_neg hb] using hd₃
  have hG₄ : G₄ = orderFortyNineAdaptiveSixthOrbitGraph k G := by rfl
  have hdH : OrderFortyNineGraphMinDegreeCard
      (orderFortyNineAdaptiveSixthOrbitGraph k G) d := by
    simpa only [← hG₄] using hd₄
  refine ⟨hfree', ?_, hreal'⟩
  intro v
  simpa only [Nat.card_eq_fintype_card,
    (orderFortyNineAdaptiveSixthOrbitGraph k G).card_neighborSet_eq_degree] using
      hdH v

end

end Erdos85
