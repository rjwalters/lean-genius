/-
  Aristotle targets for BirthdayProblemOQ01OQ01
  All three lemmas proved in BirthdayProblemOQ01OQ01.lean; this companion
  re-exports them for cross-reference.

  Originally submitted to Aristotle; proofs were completed manually in the
  main file (card_ordered_pairs, card_funs_shared_birthday, sum_collisionCount).
-/
import Mathlib
import Proofs.BirthdayProblemOQ01OQ01

namespace BirthdayProblemOQ01OQ01Aristotle

open BirthdayDistribution BigOperators Finset

/-- #{(i,j) : i < j in Fin n} = n.choose 2.
    Proved in BirthdayDistribution.card_ordered_pairs. -/
theorem card_ordered_pairs (n : ℕ) :
    (Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2)).card = n.choose 2 :=
  BirthdayDistribution.card_ordered_pairs n

/-- #{f : Fin n → Fin d | f i = f j} = d^(n-1) for i ≠ j.
    Proved in BirthdayDistribution.card_funs_shared_birthday. -/
theorem card_funs_shared_birthday (n d : ℕ) (i j : Fin n) (hij : i ≠ j) :
    (Finset.univ.filter (fun f : Fin n → Fin d => f i = f j)).card = d ^ (n - 1) :=
  BirthdayDistribution.card_funs_shared_birthday n d i j hij

/-- Σ_f collisionCount f = C(n,2) * d^(n-1).
    Proved in BirthdayDistribution.sum_collisionCount. -/
theorem sum_collisionCount (n d : ℕ) :
    ∑ f : Fin n → Fin d, collisionCount f = n.choose 2 * d ^ (n - 1) :=
  BirthdayDistribution.sum_collisionCount n d

end BirthdayProblemOQ01OQ01Aristotle
