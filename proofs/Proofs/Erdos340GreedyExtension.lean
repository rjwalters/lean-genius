/-
Copyright (c) 2026 LeanGenius Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanGenius AI Research
-/
import Proofs.Erdos340GreedySidon

/-
# Erdős Problem #340 (oq-01): The greedy construction never gets stuck

The main file `Erdos340GreedySidon.lean` now **constructs** the greedy Sidon sequence
explicitly (it is a recursive `def`, not an axiom), proving it strictly increasing with
every initial segment Sidon.  The well-definedness obligation behind that construction —
that a finite Sidon set can *always* be extended by a new, strictly larger element while
staying Sidon — is the theorem `sidon_exists_extension`, also proved in the main file.

This companion records one further corollary of that extension theorem: the set of valid
extension points above any bound is **infinite**, so the greedy recursion never terminates.
It is a fully machine-checked result (0 sorries, 0 axioms).

It does *not* touch the open growth conjecture `|A ∩ [1,N]| ≫ N^{1/2−ε}` (Erdős #340),
which remains open.
-/

open Finset

namespace Erdos340

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