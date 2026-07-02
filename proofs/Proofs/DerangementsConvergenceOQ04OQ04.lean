/-
  A bijective proof of the additive derangement recurrence
  Open Question: derangements-convergence-oq-04-oq-04

  Let `D(n) = numDerangements n` be the number of derangements (fixed-point-free
  permutations) of an `n`-element set.  The classical additive recurrence is

    D(n) = (n − 1) · (D(n−1) + D(n−2))            (for n ≥ 2).

  Mathlib records this only in the subtraction-free, `+2`-indexed form
  `numDerangements_add_two`, and proves it by a strong induction that runs the
  set-level bijection `derangements.derangementsRecursionEquiv` through the `Fin`
  cardinality lemma `card_derangements_fin_add_two`.

  ## What this entry adds

  1. `numDerangements_recurrence` — the recurrence in its **classical subtracted
     form** `D(n) = (n−1)·(D(n−1)+D(n−2))` for every `n ≥ 2`, working over `ℕ`
     with genuine truncated subtraction.  (Mathlib only states the `+2` form.)

  2. `card_derangements_recurrence` — the same recurrence lifted to the
     **cardinality of the derangement set of an arbitrary fintype** `α` with
     `2 ≤ card α`, not just `Fin n`.

  3. `card_derangements_option` / `numDerangements_succ_recurrence` /
     `numDerangements_succ_eq` — a **direct bijective derivation** of the
     recurrence.  Mathlib's bijection

        derangements (Option α) ≃ Σ a : α,
              derangements ({a}ᶜ : Set α)  ⊕  derangements α

     says: a derangement of the `(n+1)`-point set `Option α` is a choice of the
     image `a : α` of the adjoined point (`n` choices), together with either
       * a derangement of the remaining `n−1` points `{a}ᶜ` — the case where `a`
         is swept into a longer cycle, or
       * a derangement of all `n` points `α` — the case where `a` and the new
         point form a transposition.
     Counting both sides of this bijection turns straight into

        D(n+1) = n · (D(n−1) + D(n)).

     We derive this cardinality identity directly from the equivalence (via
     `card_sigma` / `card_sum` and `Fintype.card_compl_set`), obtaining the
     recurrence without the `Fin`-indexed strong induction.

  Everything is machine-checked over `ℕ` with no additional axioms; the small
  numerical checks use `decide` (no `native_decide`).
-/

import Mathlib

open Fintype

namespace DerangementsConvergenceOQ0404

/-! ## The additive recurrence in natural summand order -/

/-- Mathlib's `numDerangements_add_two`, restated with the two consecutive
    derangement values in the natural (descending) order `D(n+1) + D(n)`. -/
theorem numDerangements_add_two' (n : ℕ) :
    numDerangements (n + 2) = (n + 1) * (numDerangements (n + 1) + numDerangements n) := by
  rw [numDerangements_add_two, Nat.add_comm (numDerangements n) (numDerangements (n + 1))]

/-! ## The classical subtracted form -/

/-- **Classical additive derangement recurrence.**  For every `n ≥ 2`,
      `D(n) = (n − 1) · (D(n−1) + D(n−2))`,
    written directly with truncated subtraction on `ℕ`. -/
theorem numDerangements_recurrence (n : ℕ) (hn : 2 ≤ n) :
    numDerangements n
      = (n - 1) * (numDerangements (n - 1) + numDerangements (n - 2)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, numDerangements_add_two']

/-- The recurrence lifted to the **derangement set of an arbitrary fintype** `α`
    with `2 ≤ card α`:
      `card (derangements α) = (card α − 1) · (D(card α − 1) + D(card α − 2))`. -/
theorem card_derangements_recurrence (α : Type*) [Fintype α] [DecidableEq α]
    (hα : 2 ≤ card α) :
    card (derangements α)
      = (card α - 1) * (numDerangements (card α - 1) + numDerangements (card α - 2)) := by
  rw [card_derangements_eq_numDerangements, numDerangements_recurrence _ hα]

/-! ## Bijective derivation via the `Option` recursion equivalence -/

/-- **Counting the recursion bijection.**  Passing the Mathlib equivalence

      `derangements (Option α) ≃ Σ a : α, derangements ({a}ᶜ) ⊕ derangements α`

    through `card_sigma` and `card_sum`, and using `card ({a}ᶜ) = card α − 1`,
    each of the `card α` fibres contributes `D(card α − 1) + D(card α)`, so

      `card (derangements (Option α)) = card α · (D(card α − 1) + D(card α))`. -/
theorem card_derangements_option (α : Type*) [Fintype α] [DecidableEq α] :
    card (derangements (Option α))
      = card α * (numDerangements (card α - 1) + numDerangements (card α)) := by
  rw [card_congr (derangements.derangementsRecursionEquiv (α := α)), card_sigma]
  have key : ∀ a : α,
      card (derangements (({a}ᶜ : Set α) : Type _) ⊕ derangements α)
        = numDerangements (card α - 1) + numDerangements (card α) := by
    intro a
    rw [card_sum, card_derangements_eq_numDerangements, card_derangements_eq_numDerangements]
    congr 2
    rw [Fintype.card_compl_set, Set.card_singleton]
  rw [Finset.sum_congr rfl (fun a _ => key a), Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- **Bijective form of the recurrence, fintype version.**  Rewriting the count
    of `derangements (Option α)` via `card (derangements (Option α)) = D(card α + 1)`
    and `card (Option α) = card α + 1` turns `card_derangements_option` into

      `D(card α + 1) = card α · (D(card α − 1) + D(card α))`. -/
theorem numDerangements_succ_recurrence (α : Type*) [Fintype α] [DecidableEq α] :
    numDerangements (card α + 1)
      = card α * (numDerangements (card α - 1) + numDerangements (card α)) := by
  have h := card_derangements_option α
  rwa [card_derangements_eq_numDerangements, card_option] at h

/-- **Bijective recurrence, numerical form.**  Instantiating the fintype version
    at `α = Fin n` gives, for every `n`,
      `D(n+1) = n · (D(n−1) + D(n))`,
    obtained directly from the recursion bijection rather than by induction.
    (At `n = 0` both sides are `0`; for `n ≥ 1` this is the shifted recurrence.) -/
theorem numDerangements_succ_eq (n : ℕ) :
    numDerangements (n + 1) = n * (numDerangements (n - 1) + numDerangements n) := by
  have h := numDerangements_succ_recurrence (Fin n)
  rwa [card_fin] at h

/-! ## Numerical sanity checks (0-axiom `decide`) -/

example : numDerangements 2 = 1 := by decide
example : numDerangements 3 = 2 := by decide
example : numDerangements 4 = 9 := by decide
example : numDerangements 5 = 44 := by decide
example : numDerangements 6 = 265 := by decide

/-- Subtracted recurrence checked at `n = 6`:
    `D(6) = 5 · (D(5) + D(4)) = 5 · (44 + 9) = 265`. -/
example :
    numDerangements 6 = (6 - 1) * (numDerangements (6 - 1) + numDerangements (6 - 2)) := by
  decide

/-- Bijective recurrence checked at `n = 5`:
    `D(6) = 5 · (D(4) + D(5)) = 5 · (9 + 44) = 265`. -/
example : numDerangements (5 + 1) = 5 * (numDerangements (5 - 1) + numDerangements 5) := by
  decide

end DerangementsConvergenceOQ0404
