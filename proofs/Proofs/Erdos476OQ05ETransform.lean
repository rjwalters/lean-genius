/-
Erdős Problem #476, Open Question 5: Vosper's Theorem — e-transform infrastructure

Companion to `Erdos476OQ05Problem.lean`. The main file proves Vosper's theorem
except for one axiom, `vosper_case1_exists_large`, covering the `|A| ≥ 4` or
`|B| ≥ 4` branch of the inductive step. The textbook route to discharge that
axiom (Nathanson, *Additive Number Theory: Inverse Problems*, §2.4) is an
induction via the **Dyson e-transform** rather than the "all-redundant" framing.

This file builds the verified engine for that induction: the e-transform
`Finset.addDysonETransform e (A, B) = (A ∪ (e +ᵥ B), B ∩ (-e +ᵥ A))`
- enlarges the first component (`A ⊆ (τ).1`),
- shrinks the second component (`(τ).2 ⊆ B`),
- preserves `|A| + |B|` (`Finset.addDysonETransform.card`), and
- does not grow the sumset (`Finset.addDysonETransform.subset`).

The key lemma `etransform_preserves_cd_equality` combines these with
Cauchy–Davenport to show the transform keeps a CD-equality pair a CD-equality
pair (below the `< p` threshold). This is precisely the invariant an e-transform
induction on `|B|` needs at each step.

No `sorry`, no `axiom`: this is verified infrastructure. The remaining gap toward
discharging `vosper_case1_exists_large` is the AP pull-back step (recovering AP
structure of `(A, B)` from AP structure of the transformed pair), tracked in
`research/problems/erdos-476-oq-05/knowledge.md`.

References:
  - Vosper, A.G. (1956)
  - Nathanson (1996): Additive Number Theory: Inverse Problems §2.4
  - Mathlib: `ZMod.cauchy_davenport`, `Finset.addDysonETransform`
-/

import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Combinatorics.Additive.ETransform
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Card

open Finset Function
open scoped Pointwise

namespace Erdos476OQ05

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- The Dyson e-transform only enlarges the first component:
    `A ⊆ A ∪ (e +ᵥ B) = (addDysonETransform e (A, B)).1`. -/
lemma etransform_fst_superset {A B : Finset (ZMod p)} (e : ZMod p) :
    A ⊆ (addDysonETransform e (A, B)).1 := by
  show A ⊆ A ∪ (e +ᵥ B)
  exact Finset.subset_union_left

omit hp in
/-- The Dyson e-transform only shrinks the second component:
    `(addDysonETransform e (A, B)).2 = B ∩ (-e +ᵥ A) ⊆ B`. -/
lemma etransform_snd_subset {A B : Finset (ZMod p)} (e : ZMod p) :
    (addDysonETransform e (A, B)).2 ⊆ B := by
  show B ∩ (-e +ᵥ A) ⊆ B
  exact Finset.inter_subset_left

/-- **e-transform preserves Cauchy–Davenport equality.**

    If `(A, B)` is a Cauchy–Davenport equality pair below the threshold
    (`|A + B| = |A| + |B| - 1` and `|A| + |B| - 1 < p`), and the transformed pair
    `(A', B') = addDysonETransform e (A, B)` is componentwise nonempty, then
    `(A', B')` is again a Cauchy–Davenport equality pair.

    This is the inductive invariant of the e-transform proof of Vosper's theorem:
    each transform step keeps the equality hypothesis intact while (for a suitable
    `e`) strictly shrinking `|B|`, driving an induction on `|B|` down to the base
    case `vosper_base`. Note `|A'| + |B'| = |A| + |B|`, so the threshold
    `< p` is preserved automatically. -/
lemma etransform_preserves_cd_equality
    {A B : Finset (ZMod p)} (e : ZMod p)
    (h : (A + B).card = A.card + B.card - 1)
    (hlt : A.card + B.card - 1 < p)
    (hA' : (addDysonETransform e (A, B)).1.Nonempty)
    (hB' : (addDysonETransform e (A, B)).2.Nonempty) :
    ((addDysonETransform e (A, B)).1 + (addDysonETransform e (A, B)).2).card
      = (addDysonETransform e (A, B)).1.card
        + (addDysonETransform e (A, B)).2.card - 1 := by
  -- `|A'| + |B'| = |A| + |B|`  (card preservation)
  have hcard : (addDysonETransform e (A, B)).1.card
      + (addDysonETransform e (A, B)).2.card = A.card + B.card :=
    Finset.addDysonETransform.card e (A, B)
  -- `A' + B' ⊆ A + B`  (sumset does not grow)
  have hsub : (addDysonETransform e (A, B)).1 + (addDysonETransform e (A, B)).2
      ⊆ A + B :=
    Finset.addDysonETransform.subset e (A, B)
  -- Cauchy–Davenport lower bound for the transformed pair (already in `min` form)
  have hCD := ZMod.cauchy_davenport hp.1 hA' hB'
  -- upper bound from the sumset inclusion
  have hup : ((addDysonETransform e (A, B)).1
      + (addDysonETransform e (A, B)).2).card ≤ A.card + B.card - 1 :=
    (Finset.card_le_card hsub).trans_eq h
  -- threshold preserved: `|A'| + |B'| - 1 = |A| + |B| - 1 < p`
  have hthr : (addDysonETransform e (A, B)).1.card
      + (addDysonETransform e (A, B)).2.card - 1 < p := by omega
  rw [min_eq_right (le_of_lt hthr)] at hCD
  omega

end Erdos476OQ05
