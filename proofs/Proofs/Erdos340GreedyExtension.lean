/-
Copyright (c) 2026 LeanGenius Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanGenius AI Research
-/
import Proofs.Erdos340GreedySidon

/-
# Erdős Problem #340 (oq-01): The greedy construction never gets stuck

The main file `Erdos340GreedySidon.lean` *axiomatizes* the greedy Sidon sequence:

    axiom greedySidonSeq : ℕ → ℕ
    axiom greedySidonSeq_strictMono : StrictMono greedySidonSeq
    axiom greedySidonSeq_isSidon (n : ℕ) : IsSidon (… first n+1 terms …)

Those axioms are well-founded only if a finite Sidon set can *always* be extended by a
new, strictly larger element while staying Sidon — otherwise the greedy recursion would
terminate and the sequence would not be total. This file discharges that well-definedness
obligation with a fully machine-checked proof (0 sorries, 0 axioms).

## The key estimate

For a finite Sidon set `A`, adding an element `m` strictly above every element of `A`
can only break the Sidon property through a collision of the form

  `m + a = c + d`   with `a, c, d ∈ A`.

(The other collision shapes either keep `m` out of the equation, in which case `A` itself
is already Sidon, or force `m` to coincide with itself.) Such a collision requires

  `m = c + d − a ≤ c + d ≤ 2 · sup(A)`.

So **every** `m > 2 · sup(A)` extends `A`. No finiteness-counting of the forbidden set is
needed — the forbidden values are simply bounded by `2 · sup(A)`. Consequently the set of
valid extension points is infinite, and the greedy construction always has a next move.

This is the verified content behind the existence axiom `greedySidonSeq`. It does *not*
touch the open growth conjecture `|A ∩ [1,N]| ≫ N^{1/2−ε}` (Erdős #340), which remains open.
-/

open Finset

namespace Erdos340

/-- If `m` is strictly larger than every element of the Sidon set `A`, and no triple
`a, c, d ∈ A` realises a collision `m + a = c + d`, then `insert m A` is again Sidon.

This is the structural extension step: the only way adding a top element can break the
Sidon property is via the forbidden collision `m + a = c + d`. -/
theorem sidon_insert_of_large {A : Finset ℕ} (hA : IsSidon A) {m : ℕ}
    (hm : ∀ a ∈ A, a < m)
    (hbad : ∀ a ∈ A, ∀ c ∈ A, ∀ d ∈ A, m + a ≠ c + d) :
    IsSidon (insert m A) := by
  -- Every element of `insert m A` is `≤ m`; record this up front so `omega` can use it.
  have hbnd : ∀ x ∈ insert m A, x ≤ m := by
    intro x hx
    rcases Finset.mem_insert.1 hx with hxm | hxA
    · exact hxm.le
    · exact (hm x hxA).le
  intro a b c d ha hb hc hd hab hcd heq
  have ha' := hbnd a ha
  have hb' := hbnd b hb
  have hc' := hbnd c hc
  have hd' := hbnd d hd
  rcases Finset.mem_insert.1 ha with rfl | haA <;>
    rcases Finset.mem_insert.1 hb with rfl | hbA <;>
    rcases Finset.mem_insert.1 hc with rfl | hcA <;>
    rcases Finset.mem_insert.1 hd with rfl | hdA
  -- Sixteen leaves.  With the `≤ m` bounds in hand, every leaf closes by `omega`
  -- except: the all-in-`A` leaf (use `hA`) and the genuine forbidden-collision leaves
  -- `m + (elt) = (elt) + (elt)` (contradicted by `hbad`, in whichever orientation).
  all_goals first
    | (exact hA a b c d haA hbA hcA hdA hab hcd heq)
    | omega
    | (exfalso; first
        | exact hbad a haA c hcA d hdA (by omega)
        | exact hbad a haA d hdA c hcA (by omega)
        | exact hbad b hbA c hcA d hdA (by omega)
        | exact hbad b hbA d hdA c hcA (by omega)
        | exact hbad c hcA a haA b hbA (by omega)
        | exact hbad d hdA a haA b hbA (by omega)
        | exact hbad c hcA b hbA a haA (by omega)
        | exact hbad d hdA b hbA a haA (by omega))

/-- **Extension theorem.** Every finite Sidon set can be extended, by an element above any
prescribed bound `B`, to a strictly larger Sidon set. In particular the greedy Sidon
construction never gets stuck: there is always a next, strictly increasing choice. -/
theorem sidon_exists_extension (A : Finset ℕ) (hA : IsSidon A) (B : ℕ) :
    ∃ m, B < m ∧ (∀ a ∈ A, a < m) ∧ IsSidon (insert m A) := by
  -- Pick `m` above both `B` and twice the supremum of `A`.
  refine ⟨max (B + 1) (2 * A.sup id + 1), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self B) (le_max_left _ _)
  · intro a ha
    have ha_le : a ≤ A.sup id := Finset.le_sup (f := id) ha
    have hge : 2 * A.sup id + 1 ≤ max (B + 1) (2 * A.sup id + 1) := le_max_right _ _
    omega
  · refine sidon_insert_of_large hA ?_ ?_
    · intro a ha
      have ha_le : a ≤ A.sup id := Finset.le_sup (f := id) ha
      have hge : 2 * A.sup id + 1 ≤ max (B + 1) (2 * A.sup id + 1) := le_max_right _ _
      omega
    · intro a ha c hc d hd
      have hc_le : c ≤ A.sup id := Finset.le_sup (f := id) hc
      have hd_le : d ≤ A.sup id := Finset.le_sup (f := id) hd
      have hge : 2 * A.sup id + 1 ≤ max (B + 1) (2 * A.sup id + 1) := le_max_right _ _
      omega

/-- The set of integers that extend a finite Sidon set `A` to a larger Sidon set is
infinite. (Immediate from `sidon_exists_extension`: there are extension points above
every bound.) -/
theorem sidon_extension_points_infinite (A : Finset ℕ) (hA : IsSidon A) :
    {m : ℕ | IsSidon (insert m A)}.Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨m, hmB, _, hmS⟩ := sidon_exists_extension A hA B
  exact absurd (hB hmS) (by omega)

end Erdos340
