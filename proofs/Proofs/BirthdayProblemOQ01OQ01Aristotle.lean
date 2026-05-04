/-
  Aristotle targets for BirthdayProblemOQ01OQ01
  Routine supporting lemmas for automated proof search.
  See BirthdayProblemOQ01OQ01.lean for the main formalization.

  The three sorries in BirthdayProblemOQ01OQ01.lean are finite combinatorics
  lemmas that support the expected value calculation E[X] = C(n,2)/d:

  1. card_ordered_pairs: #{(i,j) : i < j in Fin n} = C(n,2)
     Proof idea: use Finset.card_filter over Finset.univ, relate to n*(n-1)/2.

  2. card_funs_shared_birthday: #{f : Fin n → Fin d | f i = f j} = d^(n-1) for i ≠ j
     Proof idea: biject with Fin d × (Fin (n-1) → Fin d) using the shared value
     and free assignment of remaining positions.

  3. sum_collisionCount: Σ_f collisionCount f = C(n,2) * d^(n-1)
     Proof idea: swap summation order (finite Fubini), apply card_ordered_pairs
     and card_funs_shared_birthday.

  Excluded:
  - open conjectures (none in this file)
  - def sorries (none: collisionCount and collisionIndicator are fully defined)
  - axiom declarations (none)
-/
import Mathlib
import Proofs.BirthdayProblemOQ01OQ01

namespace BirthdayProblemOQ01OQ01Aristotle

open BirthdayDistribution BigOperators Finset

/-- #{(i,j) : i < j in Fin n} = n.choose 2.
    These are the ordered pairs indexing collision indicators. -/
theorem card_ordered_pairs (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card = n.choose 2 := by
  sorry

/-- #{f : Fin n → Fin d | f i = f j} = d^(n-1) for i ≠ j.
    Core counting lemma: fixing f(i) = f(j) leaves d^(n-1) free assignments. -/
theorem card_funs_shared_birthday (n d : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter (fun f : Fin n → Fin d => f i = f j)).card = d ^ (n - 1) := by
  sorry

/-- Σ_f collisionCount f = C(n,2) * d^(n-1).
    Double counting: swap sum order and apply card_funs_shared_birthday. -/
theorem sum_collisionCount (n d : ℕ) :
    ∑ f : Fin n → Fin d, collisionCount f = n.choose 2 * d ^ (n - 1) := by
  sorry

end BirthdayProblemOQ01OQ01Aristotle
