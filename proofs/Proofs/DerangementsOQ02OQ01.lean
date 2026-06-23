/-
  Partial Derangements for Arbitrary Finite Types (derangements-oq-02-oq-01)

  Open Question: Generalize the partial derangement formula S(n,k) = C(n,k)·D(n-k)
  from Fin n to arbitrary Fintype α.

  Main result:
    card_perms_with_kfixed_fintype: For any Fintype α and k ≤ |α|,
      |{σ : Perm α | |Fix(σ)| = k}| = C(|α|, k) · D(|α| - k)

  Depends on: Proofs.DerangementsOQ02 (the Fin n case)
-/

import Proofs.DerangementsOQ02

open Finset Fintype Nat Equiv.Perm

namespace PartialDerangementsGeneral

variable {α : Type*} [DecidableEq α] [Fintype α]

/-
## Section I: Permutation Conjugation Preserves Fixed-Point Count
-/

/-- Fixed-point count is preserved by permCongr (subtype formulation). -/
theorem fixedPoint_count_permCongr {β : Type*} [DecidableEq β] [Fintype β]
    (e : α ≃ β) (σ : Equiv.Perm α) :
    Fintype.card {x : α // σ x = x} =
    Fintype.card {y : β // (e.permCongr σ) y = y} :=
  Fintype.card_congr
    { toFun := fun ⟨x, hx⟩ => ⟨e x, by simp [Equiv.permCongr_apply, hx]⟩
      invFun := fun ⟨y, hy⟩ => ⟨e.symm y, by
        simp [Equiv.permCongr_apply] at hy
        exact e.injective (by rwa [e.apply_symm_apply])⟩
      left_inv := by intro ⟨x, _⟩; simp
      right_inv := by intro ⟨y, _⟩; simp }

/-
## Section II: Filter Bijection for k-Fixed Permutations
-/

/-- The k-fixed-point permutation filter bijects between Perm α and Perm β
    via permCongr, giving equal cardinalities. -/
theorem card_kfixed_permCongr {β : Type*} [DecidableEq β] [Fintype β]
    (e : α ≃ β) (k : ℕ) :
    (Finset.univ.filter (fun σ : Equiv.Perm α =>
      (Finset.univ.filter (fun x => σ x = x)).card = k)).card =
    (Finset.univ.filter (fun τ : Equiv.Perm β =>
      (Finset.univ.filter (fun y => τ y = y)).card = k)).card := by
  simp only [← Fintype.card_subtype]
  exact Fintype.card_congr
    { toFun := fun ⟨σ, hσ⟩ =>
        ⟨e.permCongr σ, fixedPoint_count_permCongr e σ ▸ hσ⟩
      invFun := fun ⟨τ, hτ⟩ =>
        ⟨e.symm.permCongr τ, fixedPoint_count_permCongr e.symm τ ▸ hτ⟩
      left_inv := by
        intro ⟨σ, _⟩; ext : 1; ext x; simp [Equiv.permCongr_apply]
      right_inv := by
        intro ⟨τ, _⟩; ext : 1; ext y; simp [Equiv.permCongr_apply] }

/-
## Section III: Main Generalization
-/

/-- **Main Theorem (General)**: S(α, k) = C(|α|, k) · D(|α| - k)

    For any finite type α with decidable equality, the number of
    permutations of α with exactly k fixed points equals
    C(|α|, k) · D(|α| - k).

    Proof: Transport from Fin |α| via Fintype.equivFin. -/
theorem card_perms_with_kfixed_fintype
    (k : ℕ) (hk : k ≤ Fintype.card α) :
    (Finset.univ.filter (fun σ : Equiv.Perm α =>
      (Finset.univ.filter (fun x => σ x = x)).card = k)).card =
    (Fintype.card α).choose k * numDerangements (Fintype.card α - k) := by
  rw [card_kfixed_permCongr (Fintype.equivFin α) k]
  exact PartialDerangements.card_perms_with_kfixed (Fintype.card α) k hk

/-
## Section IV: Corollaries for Arbitrary Fintype
-/

/-- No permutation of a 2+-element type has exactly |α|-1 fixed points. -/
theorem permsWithCardMinus1Fixed_eq_zero
    (hn : 2 ≤ Fintype.card α) :
    (Finset.univ.filter (fun σ : Equiv.Perm α =>
      (Finset.univ.filter (fun x => σ x = x)).card = Fintype.card α - 1)).card = 0 := by
  rw [card_kfixed_permCongr (Fintype.equivFin α)]
  exact PartialDerangements.permsWithNMinus1Fixed_eq_zero hn

/-- The identity is the only permutation that fixes everything. -/
theorem permsWithAllFixed_eq_one :
    (Finset.univ.filter (fun σ : Equiv.Perm α =>
      (Finset.univ.filter (fun x => σ x = x)).card = Fintype.card α)).card = 1 := by
  rw [card_kfixed_permCongr (Fintype.equivFin α)]
  exact PartialDerangements.permsWithAllFixed_card_eq_one

/-- The sum over all k of S(α, k) equals |α|! -/
theorem sum_kfixed_eq_factorial :
    (∑ k ∈ Finset.range (Fintype.card α + 1),
      (Finset.univ.filter fun σ : Equiv.Perm α =>
        (Finset.univ.filter fun x => σ x = x).card = k).card) =
    (Fintype.card α)! := by
  conv_lhs =>
    arg 2; ext k
    rw [card_kfixed_permCongr (Fintype.equivFin α) k]
  exact PartialDerangements.sum_permsWithKFixed_eq_factorial

/-
## Summary

The partial derangement formula generalizes to arbitrary finite types.
For any α : Type* with [Fintype α] [DecidableEq α] and k ≤ |α|:

  |{σ : Perm α | |Fix(σ)| = k}| = C(|α|, k) · D(|α| - k)

Key insight: The generalization reduces to the Fin n case via Fintype.equivFin,
using that permutation conjugation preserves fixed-point counts.
-/

end PartialDerangementsGeneral
