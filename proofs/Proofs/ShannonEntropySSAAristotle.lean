/-
  Aristotle targets for ShannonEntropySSA
  Routine supporting lemmas for automated proof search.
  See ShannonEntropySSA.lean for the main formalization.

  Criteria for inclusion:
  - All results are well-known information theory facts with published proofs
  - Entropy chain rule, subadditivity, strong subadditivity
  - Clean theorem statements with no definition sorries
  - No axioms, no open conjectures
-/
import Mathlib

namespace InformationTheory

open Finset

noncomputable def shannonEntropy' {α : Type*} [Fintype α] [DecidableEq α]
    (p : α → ℝ) : ℝ :=
  -∑ x : α, if p x = 0 then 0 else p x * Real.log (p x)

noncomputable def marginalSnd {α β : Type*} [Fintype α]
    (pXY : α × β → ℝ) : β → ℝ :=
  fun y => ∑ x : α, pXY (x, y)

noncomputable def marginalXY {α β γ : Type*} [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : α × β → ℝ :=
  fun ⟨x, y⟩ => ∑ z : γ, pXYZ (x, y, z)

noncomputable def marginalYZ {α β γ : Type*} [Fintype α]
    (pXYZ : α × β × γ → ℝ) : β × γ → ℝ :=
  fun ⟨y, z⟩ => ∑ x : α, pXYZ (x, y, z)

noncomputable def marginalY_3 {α β γ : Type*} [Fintype α] [Fintype γ]
    (pXYZ : α × β × γ → ℝ) : β → ℝ :=
  fun y => ∑ x : α, ∑ z : γ, pXYZ (x, y, z)

noncomputable def condEntropy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (pXY : α × β → ℝ) : ℝ :=
  -(∑ x : α, ∑ y : β,
    if pXY (x, y) = 0 then 0
    else pXY (x, y) * Real.log (pXY (x, y) / (∑ x' : α, pXY (x', y))))

/-- Entropy Chain Rule: H(X,Y) = H(Y) + H(X|Y). -/
theorem entropy_chain_rule {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    shannonEntropy' pXY =
    shannonEntropy' (marginalSnd pXY) + condEntropy pXY := by
  sorry

/-- Subadditivity: H(X,Y) ≤ H(X) + H(Y). -/
theorem subadditivity {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {pXY : α × β → ℝ} (hp : ∀ xy, 0 ≤ pXY xy)
    (hsum : ∑ xy : α × β, pXY xy = 1) :
    shannonEntropy' pXY ≤
    shannonEntropy' (fun x => ∑ y : β, pXY (x, y)) +
    shannonEntropy' (marginalSnd pXY) := by
  sorry

/-- Strong Subadditivity: H(X,Y,Z) + H(Y) ≤ H(X,Y) + H(Y,Z). -/
theorem strong_subadditivity {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    {pXYZ : α × β × γ → ℝ} (hp : ∀ xyz, 0 ≤ pXYZ xyz)
    (hsum : ∑ xyz : α × β × γ, pXYZ xyz = 1) :
    shannonEntropy' pXYZ + shannonEntropy' (marginalY_3 pXYZ) ≤
    shannonEntropy' (marginalXY pXYZ) + shannonEntropy' (marginalYZ pXYZ) := by
  sorry

end InformationTheory
