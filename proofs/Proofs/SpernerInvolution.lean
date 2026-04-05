/-
Copyright (c) 2026 RJ Walters. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RJ Walters
-/
import Mathlib

/-!
# Even cardinality from fixed-point-free involutions

A fixed-point-free involution on a finite set produces an even
cardinality, since every element pairs with its distinct image.

This is useful in combinatorial parity arguments including
Sperner's lemma, Tucker's lemma, and various Borsuk-Ulam proofs.

## Main results

* `Finset.even_card_of_fpf_invol`: a fixed-point-free involution on a
  finset yields even cardinality.
-/

namespace Finset

open Finset

/-- A fixed-point-free involution on a finset has even cardinality:
every element pairs with its distinct image. -/
theorem even_card_of_fpf_invol {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α)
    (hInv : ∀ x ∈ S, f (f x) = x)
    (hMem : ∀ x ∈ S, f x ∈ S)
    (hNe : ∀ x ∈ S, f x ≠ x) :
    Even S.card := by
  induction S using Finset.strongInduction with
  | H S ih =>
    by_cases hempty : S = ∅
    · rw [hempty]; simp
    · obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hempty
      set y := f x with hy_def
      have hy : y ∈ S := hMem x hx
      have hxy : x ≠ y := (hNe x hx).symm
      set S' := (S.erase y).erase x
      have hS'_sub : S' ⊂ S := by
        apply ssubset_of_subset_of_ne
        · intro a ha; simp [S'] at ha; exact ha.2.2
        · intro heq; have := heq ▸ hx; simp [S'] at this
      have hcard : S.card = S'.card + 2 := by
        have h1 : (S.erase y).card = S.card - 1 :=
          Finset.card_erase_of_mem hy
        have h2 : x ∈ S.erase y :=
          Finset.mem_erase.mpr ⟨hxy, hx⟩
        have h3 : S'.card = (S.erase y).card - 1 :=
          Finset.card_erase_of_mem h2
        have hcard2 : (S.erase y).card ≥ 1 :=
          Finset.one_le_card.mpr ⟨x, h2⟩
        omega
      rw [hcard]
      have hf_S' : ∀ a ∈ S', f a ∈ S' := by
        intro a ha
        simp only [S', Finset.mem_erase] at ha ⊢
        refine ⟨?_, ?_, hMem a ha.2.2⟩
        · intro h
          have hinv_a := hInv a ha.2.2
          rw [h] at hinv_a; exact ha.2.1 (hy_def.symm ▸ hinv_a).symm
        · intro h
          have hinv_a := hInv a ha.2.2
          rw [h, show f y = x from by rw [hy_def]; exact hInv x hx] at hinv_a
          exact ha.1 hinv_a.symm
      exact (ih S' hS'_sub
        (fun a ha => hInv a (hS'_sub.subset ha))
        hf_S'
        (fun a ha => hNe a (hS'_sub.subset ha))).add ⟨1, rfl⟩

end Finset
